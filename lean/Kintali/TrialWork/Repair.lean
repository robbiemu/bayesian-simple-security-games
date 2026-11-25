module

public import Kintali.TrialWork.Relaxed
public import Kintali.ExactRecovery.RepairWork

/-! # The successful trial uses the already-prepared point and pattern -/

@[expose] public section

namespace Kintali.TrialWork

open StochasticGames.CompilerRun
open ExactRecovery LinearProgramming ContactSize

variable {k m : ℕ}

def Fields.recoveryDatum (f : Fields k m) : RowWork.Datum k m → Run ℚ
  | .zero => step 0 0
  | .one => step 0 1
  | .budget => step f.budget.size (f.budget : ℚ)
  | .prior i => f.prior i
  | .gain j => f.gain j
  | .intercept i j => f.intercept i j
  | .slope i j => f.slope i j

@[simp] theorem Fields.recoveryDatum_value (f : Fields k m) (a : RowWork.Datum k m) :
    (f.recoveryDatum a).value = RowWork.datum f.game a := by cases a <;> rfl

theorem Fields.recoveryDatum_bound (f : Fields k m) {c w : ℕ} (ok : FieldBound f c w)
    (a : RowWork.Datum k m) : (f.recoveryDatum a).Bound (c+1) w := by
  cases a with
  | zero => exact ⟨by simp [Fields.recoveryDatum], Nat.zero_le _⟩
  | one => exact ⟨by simp [Fields.recoveryDatum], Nat.zero_le _⟩
  | budget =>
    have hb : f.budget.size ≤ w := by simpa using ok.budget.1
    exact ⟨by simp [Fields.recoveryDatum], hb⟩
  | prior i => exact (ok.prior i).1.weaken (Nat.le_succ _) le_rfl
  | gain j => exact (ok.gain j).1.weaken (Nat.le_succ _) le_rfl
  | intercept i j => exact (ok.intercept i j).1.weaken (Nat.le_succ _) le_rfl
  | slope i j => exact (ok.slope i j).1.weaken (Nat.le_succ _) le_rfl

theorem Fields.recoveryDatum_fits (f : Fields k m) {c w : ℕ} (ok : FieldBound f c w)
    (a : RowWork.Datum k m) : Fits w (f.recoveryDatum a).value := by
  cases a with
  | zero => simpa [Fields.recoveryDatum, Fits] using ok.positive
  | one => simpa [Fields.recoveryDatum, Fits] using ok.positive
  | budget => exact ok.budget
  | prior i => exact (ok.prior i).2
  | gain j => exact (ok.gain j).2
  | intercept i j => exact (ok.intercept i j).2
  | slope i j => exact (ok.slope i j).2

def Point.recoveryRead (v : Point k m) : Variable (Fin k) (Fin m) → Run ℚ
  | .inl (i,j) => v.readQ i j
  | .inr (.inl j) => v.readX j
  | .inr (.inr false) => step 0 v.threshold
  | .inr (.inr true) => step 0 v.tolerance

@[simp] theorem Point.recoveryRead_value (v : Point k m) (r : Variable (Fin k) (Fin m)) :
    (v.recoveryRead r).value = vector v.x v.q v.threshold v.tolerance r := by
  rcases r with ⟨i,j⟩ | j | b
  · rfl
  · rfl
  · cases b <;> rfl

theorem Point.recoveryRead_bound (v : Point k m) {w : ℕ} (kw : k.size ≤ w) (mw : m.size ≤ w)
    (r : Variable (Fin k) (Fin m)) : (v.recoveryRead r).Bound 2 w := by
  rcases r with ⟨i,j⟩ | j | b
  · exact v.readQ_bound i j kw mw
  · exact (v.readX_bound j mw).weaken (by decide) le_rfl
  · cases b <;> exact ⟨by change 1 ≤ 2; decide, Nat.zero_le _⟩

def repairRun (f : Fields k m) (v : Point k m) (r : RuleFields k m) (d h : ℕ) : Run (Strategy k m) :=
  RepairWork.solve d h f.recoveryDatum (readRuleWork r) v.recoveryRead f.prior r.reference

theorem repairRun_value (f : Fields k m) (v : Point k m) {r : RuleFields k m}
    {p : Pattern (Fin k) (Fin m)} (read : RuleReads r p) :
    (repairRun f v r (denominator f.game) (coefficientHeight f.game)).value =
      ExactRecovery.repair f.game p v.x v.q v.threshold v.tolerance :=
  RepairWork.solve_value f.game p v.x v.q v.threshold v.tolerance f.recoveryDatum
    f.recoveryDatum_value (readRuleWork r) (readRuleWork_value read)
    v.recoveryRead v.recoveryRead_value f.prior r.reference (fun _ => rfl) read.ref

theorem repairRun_work (f : Fields k m) (v : Point k m) {r : RuleFields k m}
    {p : Pattern (Fin k) (Fin m)} (read : RuleReads r p)
    {L w c rc : ℕ} (fields : FieldBound f c w) (rules : RuleBound r rc w)
    (rowIndex : indexWidth k m ≤ w) (varIndex : (exactVars k m).size ≤ w)
    (den : (denominator f.game).size ≤ w) (bits : 2 * RationalInput.widthLimit L ≤ w)
    (length : RationalInput.inputLength (recoveryInput f.game p)
      (recoveryPoint v.x v.q v.threshold v.tolerance) (coefficientHeight f.game) ≤ L) :
    (repairRun f v r (denominator f.game) (coefficientHeight f.game)).Bound
      (RepairWork.solveSlots k m L w (c+1) (12+(2*rc+2)) 2 c rc) (scalarWidth w) := by
  have eq := RowWork.compile_value f.game p f.recoveryDatum f.recoveryDatum_value
    (readRuleWork r) (readRuleWork_value read)
  have point := RepairWork.pointTable_value v.recoveryRead v.x v.q v.threshold v.tolerance v.recoveryRead_value
  have coeff (i j : _) : |(RowWork.compile (denominator f.game) f.recoveryDatum
      (readRuleWork r)).value.system.coeff i j| ≤ (coefficientHeight f.game : ℤ) := by
    rw [eq, recoveryInput_system]
    exact exactSystem_coeff_bound f.game p i j
  have rowWidth := (StochasticGames.BinarySize.size_le_self (exactRows k m)).trans
    (show exactRows k m ≤ w by unfold indexWidth at rowIndex; omega)
  refine RepairWork.solve_work f.recoveryDatum (readRuleWork r) v.recoveryRead f.prior r.reference
    (coefficientHeight_pos f.game) den fields.kSize fields.mSize rowWidth varIndex
    (f.recoveryDatum_bound fields) (f.recoveryDatum_fits fields)
    (readRuleWork_bound rules rowIndex) (v.recoveryRead_bound fields.kSize fields.mSize)
    (fun i => (fields.prior i).1) rules.ref (fun i => (fields.prior i).2) coeff ?_ bits
  rw [eq, point]
  exact length

end Kintali.TrialWork
