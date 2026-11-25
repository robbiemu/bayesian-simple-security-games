module

public import Kintali.ExactRecovery.RowWork
public import Kintali.LinearProgramming.RationalOutput
public import Kintali.TrialWork.Arithmetic

/-! # Converting a repaired integer point into compact strategies -/

@[expose] public section

namespace Kintali.ExactRecovery.OutputWork

open StochasticGames.CompilerRun LinearProgramming
open ArithmeticRun TrialWork ContactSize
open InputOutput.CodecWork

variable {k m n : ℕ}

def fraction (z den : ℤ) : Run ℚ := do
  let nonnegative ← step (den.natAbs.size+1) (0 ≤ den : Bool)
  let d ← step (den.natAbs.size+1) den.natAbs
  let a ← step (z.natAbs.size+1) (if nonnegative then z else -z)
  reduce a d

@[simp] theorem fraction_value (z d : ℤ) : (fraction z d).value = Rat.divInt z d := by
  rcases Int.eq_nat_or_neg d with ⟨i,rfl | rfl⟩
  · simp [fraction, reduce_value, Rat.mkRat_eq_div]
  · by_cases hz : i = 0
    · simp [hz, fraction, reduce_value]
    · simp [fraction, hz, reduce_value, Rat.mkRat_eq_div]

def fractionSlots (w : ℕ) := 3 + (5*w + 7)

theorem fraction_work (z d : ℤ) {w : ℕ} (hz : z.natAbs.size ≤ w) (hd : d.natAbs.size ≤ w) :
    (fraction z d).Bound (fractionSlots w) (w+3) := by
  have fit : (if 0 ≤ d then z else -z).natAbs.size ≤ w := by split <;> simpa using hz
  have h := reduce_work (if 0 ≤ d then z else -z) d.natAbs fit hd
  constructor
  · simp only [fraction, Run.bind_slots, step_value, step_slots, decide_eq_true_eq]
    unfold fractionSlots
    have := h.1
    omega
  · simp only [fraction, Run.bind_width, step_value, step_width, decide_eq_true_eq]
    exact max_le (by omega) (max_le (by omega) (max_le (by omega)
      (h.2.trans (Nat.le_succ _))))

def coordinate (a : CramerRun.Answer n) (j : Fin n) : Run ℚ := do
  let z ← step n.size a.num[j.val]
  fraction z a.den

@[simp] theorem coordinate_value (a : CramerRun.Answer n) (j : Fin n) :
    (coordinate a j).value = a.value j := by simp [coordinate, CramerRun.Answer.value]

def coverage (a : CramerRun.Answer (exactVars k m)) (j : Fin m) : Run ℚ :=
  let r := varIndex k m (.inr (.inl j))
  coordinate a r

def attack (a : CramerRun.Answer (exactVars k m)) (prior : ℚ) (i : Fin k) (j : Fin m) : Run ℚ := do
  let mass ← coordinate a (varIndex k m (.inl (i,j)))
  divide mass prior

def attackRow (a : CramerRun.Answer (exactVars k m))
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m)) (i : Fin k) :
    Run (Vector ℚ m) := do
  let p ← prior i
  let zero ← step (p.num.natAbs.size+1) (p = 0 : Bool)
  if zero then
    let r ← reference i
    tabulate m fun j => step m.size (if j = r then 1 else 0)
  else
    tabulate m (attack a p i)

def table (a : CramerRun.Answer (exactVars k m))
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m)) :
    Run (Vector ℚ m × Vector (Vector ℚ m) k) := do
  let cov ← tabulate m (coverage a)
  let attacks ← tabulate k (attackRow a prior reference)
  step 0 (cov,attacks)

def strategy (a : CramerRun.Answer (exactVars k m))
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m)) : Run (Strategy k m) := do
  let (x,q) ← table a prior reference
  step 0 ⟨fun j => x[j.val],fun i j => q[i.val][j.val]⟩

theorem strategy_value (a : CramerRun.Answer (exactVars k m))
    (g : Game (Fin k) (Fin m)) (p : Pattern (Fin k) (Fin m))
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m))
    (hp : ∀ i, (prior i).value = g.prior i)
    (hr : ∀ i, (reference i).value = p.reference i) :
    let v := fun j => a.value (varIndex k m j)
    (strategy a prior reference).value = ⟨coverageOf v, g.conditional (flowOf v) p.reference⟩ := by
  have eq (i : Fin k) : (attackRow a prior reference i).value =
      Vector.ofFn (g.conditional (flowOf fun j => a.value (varIndex k m j)) p.reference i) := by
    by_cases h : g.prior i = 0
    · simp [attackRow, hp, hr, h]
      congr 1
      funext j
      simp [Game.conditional, h]
    · simp [attackRow, hp, h, attack]
      congr 1
      funext j
      simp [Game.conditional, flowOf, h]
  simp only [strategy, table, Run.bind_value, tabulate_value, eq, Vector.getElem_ofFn, step_value,
    coverage, coordinate_value]
  rfl

def attackSlots (w : ℕ) := 1+fractionSlots w+4+scalarSlots w

theorem coordinate_work (a : CramerRun.Answer n) (j : Fin n) {w : ℕ}
    (index : n.size ≤ w) (num : a.num[j.val].natAbs.size ≤ w) (den : a.den.natAbs.size ≤ w) :
    (coordinate a j).Bound (1+fractionSlots w) (w+3) :=
  bound_bind (f := fun z => fraction z a.den)
    ((bound_step _ _).weaken le_rfl (index.trans (by omega))) (fraction_work _ _ num den)

theorem coordinate_fits (a : CramerRun.Answer n) (j : Fin n) {w : ℕ}
    (num : a.num[j.val].natAbs.size ≤ w) (den : a.den.natAbs.size ≤ w) (nonzero : a.den ≠ 0) :
    Fits w (coordinate a j).value := by
  rw [coordinate_value, CramerRun.Answer.value]
  obtain ⟨hn,hd⟩ := divInt_parts_le a.num[j.val] a.den nonzero
  exact ⟨(Nat.size_le_size hn).trans num,(Nat.size_le_size hd).trans den⟩

theorem attack_work (a : CramerRun.Answer (exactVars k m)) (prior : ℚ)
    (i : Fin k) (j : Fin m) {w : ℕ}
    (index : (exactVars k m).size ≤ w)
    (num : ∀ r : Fin (exactVars k m), a.num[r.val].natAbs.size ≤ w)
    (den : a.den.natAbs.size ≤ w) (nonzero : a.den ≠ 0) (fit : Fits w prior) :
    (attack a prior i j).Bound (attackSlots w) (scalarWidth w) := by
  let r := varIndex k m (.inl (i,j))
  have coordinateBound := coordinate_work a r index (num r) den
  have span : w+3 ≤ scalarWidth w := by unfold scalarWidth; omega
  have norm := divide_work (coordinate_fits a r (num r) den nonzero) fit
  constructor
  · change (coordinate a r).work.slots + (divide (coordinate a r).value prior).work.slots ≤ _
    have := coordinateBound.1
    have := norm.1
    unfold attackSlots
    omega
  · exact max_le (coordinateBound.2.trans span) norm.2

def attackRowSlots (m w priorCost refCost : ℕ) :=
  priorCost + refCost + 1 + (3*(m+1) + m*attackSlots w)

theorem attackRow_work (a : CramerRun.Answer (exactVars k m))
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m)) (i : Fin k)
    {w pCost rCost : ℕ} (mw : m.size ≤ w) (index : (exactVars k m).size ≤ w)
    (num : ∀ r : Fin (exactVars k m), a.num[r.val].natAbs.size ≤ w)
    (den : a.den.natAbs.size ≤ w) (nonzero : a.den ≠ 0)
    (hp : (prior i).Bound pCost w) (hr : (reference i).Bound rCost w)
    (fit : Fits w (prior i).value) :
    (attackRow a prior reference i).Bound (attackRowSlots m w pCost rCost) (scalarWidth w) := by
  let p := (prior i).value
  have grow : w+1 ≤ scalarWidth w := by unfold scalarWidth; omega
  have mw'' := mw.trans ((Nat.le_succ w).trans grow)
  have idx := Nat.le_succ w |>.trans grow
  by_cases hz : p = 0
  · let f (j : Fin m) := step m.size (if j = (reference i).value then (1 : ℚ) else 0)
    have out := tabulate_bound f mw'' (fun _ => (bound_step _ _).weaken le_rfl mw'')
    have cost := out.1
    have hmul := Nat.mul_le_mul_left m (show 1 ≤ attackSlots w by unfold attackSlots; omega)
    constructor
    · simp only [attackRow, Run.bind_slots, step_slots, step_value, show (prior i).value = 0 from hz,
        decide_true, ite_true]
      change (prior i).work.slots + (1 + ((reference i).work.slots + (tabulate m f).work.slots)) ≤ _
      have := hp.1
      have := hr.1
      unfold attackRowSlots
      omega
    · simp only [attackRow, Run.bind_width, step_width, step_value, show (prior i).value = 0 from hz,
        decide_true, ite_true, max_le_iff]
      exact ⟨hp.2.trans idx, by simp; omega, hr.2.trans idx, out.2⟩
  · have out := tabulate_bound (attack a p i) mw''
      (fun j => attack_work a p i j index num den nonzero fit)
    constructor
    · simp only [attackRow, Run.bind_slots, step_slots, step_value, show (prior i).value ≠ 0 from hz,
        decide_false, Bool.false_eq_true, ite_false]
      change (prior i).work.slots + (1 + (tabulate m (attack a p i)).work.slots) ≤ _
      have := hp.1
      have := out.1
      unfold attackRowSlots
      omega
    · simp only [attackRow, Run.bind_width, step_width, step_value, show (prior i).value ≠ 0 from hz,
        decide_false, Bool.false_eq_true, ite_false, max_le_iff]
      exact ⟨hp.2.trans idx, (Nat.add_le_add_right fit.1 1).trans grow, out.2⟩

def strategySlots (k m w priorCost refCost : ℕ) :=
  3*(m+1) + m*(1+fractionSlots w) + (3*(k+1) + k*attackRowSlots m w priorCost refCost) + 2

theorem strategy_work (a : CramerRun.Answer (exactVars k m))
    (prior : Fin k → Run ℚ) (reference : Fin k → Run (Fin m))
    {w pCost rCost : ℕ} (kw : k.size ≤ w) (mw : m.size ≤ w) (index : (exactVars k m).size ≤ w)
    (num : ∀ r : Fin (exactVars k m), a.num[r.val].natAbs.size ≤ w)
    (den : a.den.natAbs.size ≤ w) (nonzero : a.den ≠ 0)
    (hp : ∀ i, (prior i).Bound pCost w) (hr : ∀ i, (reference i).Bound rCost w)
    (fit : ∀ i, Fits w (prior i).value) :
    (strategy a prior reference).Bound (strategySlots k m w pCost rCost) (scalarWidth w) := by
  have span : w+3 ≤ scalarWidth w := by unfold scalarWidth; omega
  have grow : w ≤ scalarWidth w := by unfold scalarWidth; omega
  have cov := tabulate_bound (coverage a) (mw.trans grow) fun j =>
    (coordinate_work a (varIndex k m (.inr (.inl j))) index (num _) den).weaken le_rfl span
  have q := tabulate_bound (attackRow a prior reference) (kw.trans grow) fun i =>
    attackRow_work a prior reference i mw index num den nonzero (hp i) (hr i) (fit i)
  constructor
  · simp only [strategy, table, Run.bind_slots, step_slots]
    have := cov.1
    have := q.1
    unfold strategySlots
    omega
  · exact max_le (max_le cov.2 (max_le q.2 (Nat.zero_le _))) (Nat.zero_le _)


end Kintali.ExactRecovery.OutputWork
