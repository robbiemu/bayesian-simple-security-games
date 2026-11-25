module

public import Kintali.ExactRecovery.OutputWork

/-! # Exact repair after a successful relaxed trial

The composition charges dense row construction, the integer repair, and
normalization into coverage and conditional attack tables. The caller
supplies the already-computed precision and access to the prepared fields.
-/

@[expose] public section

namespace Kintali.ExactRecovery.RepairWork

open StochasticGames.CompilerRun LinearProgramming ArithmeticRun

variable {k m : ℕ}

def pointTable (read : Variable (Fin k) (Fin m) → Run ℚ) : Run (Vector ℚ (exactVars k m)) :=
  tabulate (exactVars k m) fun j => do
    let coordinate ← step (exactVars k m).size ((varIndex k m).symm j)
    read coordinate

theorem pointTable_value (read : Variable (Fin k) (Fin m) → Run ℚ) (x : Fin m → ℚ)
    (q : Fin k → Fin m → ℚ) (t e : ℚ) (exactRead : ∀ v, (read v).value = vector x q t e v) :
    (pointTable read).value = recoveryPoint x q t e := by
  simp [pointTable, recoveryPoint, exactRead]

theorem pointTable_work (read : Variable (Fin k) (Fin m) → Run ℚ) {cost w : ℕ}
    (index : (exactVars k m).size ≤ w) (reads : ∀ v, (read v).Bound cost w) :
    (pointTable read).Bound (3*(exactVars k m+1) + exactVars k m*(1+cost)) w :=
  tabulate_bound _ index fun j =>
    bound_bind (f := read) ((bound_step _ _).weaken le_rfl index) (reads ((varIndex k m).symm j))

def materialized (rows : PivotRun.Input (exactRows k m) (exactVars k m))
    (point : Vector ℚ (exactVars k m)) (h : ℕ)
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m)) : Run (Strategy k m) := do
  let solution ← RationalInput.run rows point h
  OutputWork.strategy solution prior reference

theorem materialized_value (g : Game (Fin k) (Fin m)) (p : Pattern (Fin k) (Fin m))
    (x : Fin m → ℚ) (q : Fin k → Fin m → ℚ) (t e : ℚ)
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m))
    (hp : ∀ i, (prior i).value = g.prior i)
    (hr : ∀ i, (reference i).value = p.reference i) :
    (materialized (recoveryInput g p) (recoveryPoint x q t e) (coefficientHeight g)
      prior reference).value = repair g p x q t e := by
  unfold materialized
  rw [Run.bind_value, OutputWork.strategy_value _ g p _ _ hp hr]
  rfl

theorem materialized_work (rows : PivotRun.Input (exactRows k m) (exactVars k m))
    (point : Vector ℚ (exactVars k m)) {h : ℕ}
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m))
    (pos : 0 < h) (coeff : ∀ i j, |rows.system.coeff i j| ≤ (h : ℤ))
    {w priorCost refCost : ℕ}
    (kw : k.size ≤ w) (mw : m.size ≤ w) (index : (exactVars k m).size ≤ w)
    (wp : 2 * RationalInput.widthLimit (RationalInput.inputLength rows point h) ≤ w)
    (hp : ∀ i, (prior i).Bound priorCost w) (hr : ∀ i, (reference i).Bound refCost w)
    (pf : ∀ i, ContactSize.Fits w (prior i).value) :
    (materialized rows point h prior reference).Bound
      (RationalInput.slotLimit (RationalInput.inputLength rows point h) +
        OutputWork.strategySlots k m w priorCost refCost) (TrialWork.scalarWidth w) := by
  let r := RationalInput.run rows point h
  have work := RationalInput.run_work rows point pos coeff
  have chars := OutputSize.rational_fields rows point h
  have hden : r.value.den.natAbs.size ≤ w := chars.1.trans ((Nat.mul_le_mul_left 2 work.2).trans wp)
  have hw : RationalInput.widthLimit (RationalInput.inputLength rows point h) ≤ w := by omega
  have hnum (j : Fin (exactVars k m)) : r.value.num[j.val].natAbs.size ≤ w :=
    (chars.2 j).trans (work.2.trans hw)
  have nonzero := RationalInput.run_den_ne_zero rows point h
  have convert := OutputWork.strategy_work r.value prior reference kw mw index hnum hden nonzero hp hr pf
  have grow : w ≤ TrialWork.scalarWidth w := by unfold TrialWork.scalarWidth; omega
  exact bound_bind (f := fun solution => OutputWork.strategy solution prior reference)
    (work.weaken le_rfl (hw.trans grow)) convert

def solve (d h : ℕ) (datum : RowWork.Datum k m → Run ℚ)
    (rules : Fin (exactRows k m) → Run (Option (Comparison (Fin k) (Fin m))))
    (pointRead : Variable (Fin k) (Fin m) → Run ℚ)
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m)) : Run (Strategy k m) := do
  let rows ← RowWork.compile d datum rules
  let point ← pointTable pointRead
  materialized rows point h prior reference

theorem solve_value (g : Game (Fin k) (Fin m)) (p : Pattern (Fin k) (Fin m))
    (x : Fin m → ℚ) (q : Fin k → Fin m → ℚ) (t e : ℚ)
    (datum : RowWork.Datum k m → Run ℚ) (datumSpec : ∀ a, (datum a).value = RowWork.datum g a)
    (rules : Fin (exactRows k m) → Run (Option (Comparison (Fin k) (Fin m))))
    (ruleSpec : ∀ i, (rules i).value = RowWork.rule p i)
    (pointRead : Variable (Fin k) (Fin m) → Run ℚ)
    (pointSpec : ∀ v, (pointRead v).value = vector x q t e v)
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m))
    (hp : ∀ i, (prior i).value = g.prior i)
    (hr : ∀ i, (reference i).value = p.reference i) :
    (solve (denominator g) (coefficientHeight g) datum rules pointRead prior reference).value =
      repair g p x q t e := by
  simp only [solve, Run.bind_value, RowWork.compile_value g p _ datumSpec _ ruleSpec,
    pointTable_value _ x q t e pointSpec, materialized_value g p x q t e _ _ hp hr]

def solveSlots (k m L w datumCost ruleCost pointCost priorCost refCost : ℕ) :=
  RowWork.denseSlots (exactRows k m) (exactVars k m) datumCost ruleCost +
    (3*(exactVars k m+1) + exactVars k m*(1+pointCost)) +
    RationalInput.slotLimit L + OutputWork.strategySlots k m w priorCost refCost

theorem slotLimit_mono : Monotone RationalInput.slotLimit := by
  intro a b h
  unfold RationalInput.slotLimit RecoveryRun.transitionLimit RecoveryRun.scale PointEncoding.wordLimit
  gcongr

theorem solve_work {d h : ℕ} (datum : RowWork.Datum k m → Run ℚ)
    (rules : Fin (exactRows k m) → Run (Option (Comparison (Fin k) (Fin m))))
    (pointRead : Variable (Fin k) (Fin m) → Run ℚ)
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m))
    {L w datumCost ruleCost pointCost priorCost refCost : ℕ}
    (pos : 0 < h) (denom : d.size ≤ w) (kw : k.size ≤ w) (mw : m.size ≤ w)
    (rowIndexWidth : (exactRows k m).size ≤ w) (varIndexWidth : (exactVars k m).size ≤ w)
    (datumWork : ∀ a, (datum a).Bound datumCost w)
    (datumFits : ∀ a, (datum a).value.num.natAbs.size ≤ w ∧ (datum a).value.den.size ≤ w)
    (ruleWork : ∀ i, (rules i).Bound ruleCost w)
    (pointWork : ∀ v, (pointRead v).Bound pointCost w)
    (priorWork : ∀ i, (prior i).Bound priorCost w)
    (refWork : ∀ i, (reference i).Bound refCost w)
    (priorFits : ∀ i, ContactSize.Fits w (prior i).value)
    (coeff : ∀ i j, |(RowWork.compile d datum rules).value.system.coeff i j| ≤ (h : ℤ))
    (length : RationalInput.inputLength (RowWork.compile d datum rules).value
      (pointTable pointRead).value h ≤ L)
    (bits : 2 * RationalInput.widthLimit L ≤ w) :
    (solve d h datum rules pointRead prior reference).Bound
      (solveSlots k m L w datumCost ruleCost pointCost priorCost refCost) (TrialWork.scalarWidth w) := by
  have cw := RowWork.compile_work d datum rules denom rowIndexWidth varIndexWidth
    datumWork datumFits ruleWork
  have pw := pointTable_work pointRead varIndexWidth pointWork
  have wp := (Nat.mul_le_mul_left 2 (RationalInput.widthLimit_mono length)).trans bits
  have rw := materialized_work (RowWork.compile d datum rules).value (pointTable pointRead).value
    prior reference pos coeff kw mw varIndexWidth wp priorWork refWork priorFits
  have calcSlots := rw.1.trans (Nat.add_le_add_right (slotLimit_mono length) _)
  have cwBound : 2*w+1 ≤ TrialWork.scalarWidth w := by unfold TrialWork.scalarWidth; omega
  have pwBound : w ≤ TrialWork.scalarWidth w := by unfold TrialWork.scalarWidth; omega
  constructor
  · simp only [solve, Run.bind_slots]
    unfold solveSlots
    have := cw.1
    have := pw.1
    omega
  · exact max_le (cw.2.trans cwBound) (max_le (pw.2.trans pwBound) rw.2)


end Kintali.ExactRecovery.RepairWork
