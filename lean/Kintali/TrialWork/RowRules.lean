module

public import Kintali.TrialWork.Pattern
public import Kintali.ExactRecovery.RowWork

/-! Decode a dense row address through the finite sums and products of
the integer recovery system. Array lookups for marks, references and
statuses carry independent costs. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery

variable {k m : ℕ}

def splitProd {n t : ℕ} (p : Fin (n*t)) : Run (Fin n × Fin t) :=
  let u := max p.val.size t.size
  let a := step u (p.val/t)
  let b := step u (p.val%t)
  ⟨(⟨a.value,p.divNat.isLt⟩,⟨b.value,p.modNat.isLt⟩),a.work.seq b.work⟩

@[simp] theorem splitProd_value {n t : ℕ} (p : Fin (n*t)) :
    (splitProd p).value = finProdFinEquiv.symm p := rfl

theorem splitProd_work {n t w : ℕ} (p : Fin (n*t)) (hi : (n*t).size ≤ w) (ht : t.size ≤ w) :
    (splitProd p).Bound 2 w :=
  ⟨le_rfl,max_le (max_le ((Nat.size_le_size p.isLt.le).trans hi) ht)
    (max_le ((Nat.size_le_size p.isLt.le).trans hi) ht)⟩

def splitSum {n t : ℕ} (p : Fin (n+t)) : Run (Fin n ⊕ Fin t) :=
  let test := step (max p.val.size n.size) (decide (p.val<n))
  if h : test.value = true then ⟨.inl ⟨p.val,of_decide_eq_true h⟩,test.work⟩ else
    let rest := natSub p.val n
    ⟨.inr ⟨rest.value,by
      change p.val-n < t
      have hn : ¬p.val<n := fun h' => h (decide_eq_true h')
      have := p.isLt
      omega⟩,test.work.seq rest.work⟩

@[simp] theorem splitSum_value {n t : ℕ} (p : Fin (n+t)) : (splitSum p).value = finSumFinEquiv.symm p := by
  obtain ⟨q,rfl⟩ := finSumFinEquiv.surjective p
  rw [Equiv.symm_apply_apply]
  rcases q with i|j
  · simp [splitSum, Fin.castAdd, i.isLt]
  · simp [splitSum, Fin.natAdd, natSub]

theorem splitSum_work {n t w : ℕ} (p : Fin (n+t)) (h : (n+t).size ≤ w) : (splitSum p).Bound 2 w := by
  have hp := (Nat.size_le_size p.isLt.le).trans h
  have hn := (Nat.size_le_size (Nat.le_add_right n t)).trans h
  dsimp only [splitSum]
  split <;> simp only [Run.Bound,Work.seq,step_slots,step_width,natSub] <;> omega

abbrev Address (k m : ℕ) :=
  (Fin 6 × Fin m) ⊕ ((Fin 4 × (Fin k × Fin m)) ⊕ ((Bool × Fin k) ⊕ Fin 6))

private def addressIndex (k m : ℕ) : Address k m ≃ Fin (exactRows k m) :=
  (Equiv.sumCongr finProdFinEquiv <|
    (Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv) <|
      (Equiv.sumCongr ((Equiv.prodCongr finTwoEquiv.symm (Equiv.refl _)).trans finProdFinEquiv)
        (Equiv.refl _)).trans finSumFinEquiv).trans finSumFinEquiv).trans finSumFinEquiv

/-- Each final tag belongs to an array of at most six constructors. -/
def rowAddress (i : Fin (exactRows k m)) : Run (Address k m) := do
  let top ← splitSum (n := 6*m) i
  match top with
  | .inl p => do let a ← splitProd p; pure (.inl a)
  | .inr rest => do
    let second ← splitSum (n := 4*(k*m)) rest
    match second with
    | .inl p => do
      let s ← splitProd p
      let t ← splitProd s.2
      pure (.inr (.inl (s.1,t)))
    | .inr rest => do
      let third ← splitSum (n := 2*k) rest
      match third with
      | .inl p => do
        let b ← splitProd p
        let tag ← step 1 (finTwoEquiv b.1)
        pure (.inr (.inr (.inl (tag,b.2))))
      | .inr tag => pure (.inr (.inr (.inr tag)))

def rowId (i : Fin (exactRows k m)) : Run (Row (Fin k) (Fin m) ⊕ Unit) := do
  let tag ← rowAddress i
  step 3 ((rowShape k m).symm tag)

@[simp] theorem rowId_value (i : Fin (exactRows k m)) : (rowId i).value = (rowIndex k m).symm i := by
  change (rowShape k m).symm (rowAddress i).value = (rowShape k m).symm ((addressIndex k m).symm i)
  congr 1
  obtain ⟨a,rfl⟩ := (addressIndex k m).surjective i
  rw [Equiv.symm_apply_apply]
  rcases a with ⟨t,j⟩ | ⟨t,i,j⟩ | ⟨t,i⟩ | t
  · change (rowAddress (finSumFinEquiv (.inl (finProdFinEquiv (t,j))))).value = _
    unfold rowAddress
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    exact congrArg Sum.inl (Equiv.symm_apply_apply finProdFinEquiv (t,j))
  · change (rowAddress (finSumFinEquiv (.inr (finSumFinEquiv (.inl
      (finProdFinEquiv (t,finProdFinEquiv (i,j)))))))).value = _
    unfold rowAddress
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    dsimp only
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    dsimp only
    rw [Run.bind_value,splitProd_value,Equiv.symm_apply_apply,Run.bind_value,splitProd_value,
      Equiv.symm_apply_apply]
    rfl
  · change (rowAddress (finSumFinEquiv (.inr (finSumFinEquiv (.inr (finSumFinEquiv (.inl
      (finProdFinEquiv (finTwoEquiv.symm t,i))))))))).value = _
    unfold rowAddress
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    dsimp only
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    dsimp only
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    dsimp only
    rw [Run.bind_value,splitProd_value,Equiv.symm_apply_apply,Run.bind_value,step_value,
      Equiv.apply_symm_apply]
    rfl
  · change (rowAddress (finSumFinEquiv (.inr (finSumFinEquiv (.inr (finSumFinEquiv (.inr t))))))).value = _
    unfold rowAddress
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    dsimp only
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    dsimp only
    rw [Run.bind_value,splitSum_value,Equiv.symm_apply_apply]
    rfl

def indexWidth (k m : ℕ) := exactRows k m+k+m+4

theorem rowId_work (i : Fin (exactRows k m)) : (rowId i).Bound 12 (indexWidth k m) := by
  let w := indexWidth k m
  have size {a : ℕ} (b : a ≤ w) : a.size ≤ w := (size_le_self a).trans b
  have nums : w = 6*m+(4*(k*m)+(2*k+6))+k+m+4 := rfl
  have top := splitSum_work (n := 6*m) i (size (by omega))
  unfold rowId
  apply Run.Bound.weaken (k := 11+1) (w := w) ?_ le_rfl le_rfl
  apply bound_bind (l := 1) ?_ ((bound_step 3 _).weaken le_rfl (by omega))
  unfold rowAddress
  apply bound_bind (l := 9) top
  cases h₁ : (splitSum (n := 6*m) i).value with
  | inl p =>
    apply Run.Bound.weaken (k := 2+0) (w := w) ?_ (by decide) le_rfl
    exact bound_bind (splitProd_work p (size (by omega)) (size (by omega))) (bound_pure _ _)
  | inr rest =>
    apply bound_bind (l := 7) (splitSum_work (n := 4*(k*m)) rest (size (by omega)))
    cases h₂ : (splitSum (n := 4*(k*m)) rest).value with
    | inl p =>
      apply Run.Bound.weaken (k := 2+(2+0)) (w := w) ?_ (by decide) le_rfl
      apply bound_bind (splitProd_work p (size (by omega)) (size (by omega)))
      apply bound_bind (splitProd_work _ (size (by omega)) (size (by omega)))
      exact bound_pure _ _
    | inr rest =>
      apply bound_bind (l := 5) (splitSum_work (n := 2*k) rest (size (by omega)))
      cases h₃ : (splitSum (n := 2*k) rest).value with
      | inl p =>
        apply Run.Bound.weaken (k := 2+(1+0)) (w := w) ?_ (by decide) le_rfl
        apply bound_bind (splitProd_work p (size (by omega)) (size (by omega)))
        apply bound_bind ((bound_step 1 _).weaken le_rfl (by omega))
        exact bound_pure _ _
      | inr tag => exact (bound_pure _ _).weaken (by decide) le_rfl

/-- A pointer to each of the three saved pattern tables. -/
structure RuleFields (k m : ℕ) where
  reference : Fin k → Run (Fin m)
  marked : Fin k → Fin m → Run Bool
  status : Fin m → Run Status

structure RuleReads (r : RuleFields k m) (p : Pattern (Fin k) (Fin m)) : Prop where
  ref : ∀ i, (r.reference i).value = p.reference i
  marked : ∀ i j, (r.marked i j).value = p.marked i j
  status : ∀ j, (r.status j).value = p.status j

structure RuleBound (r : RuleFields k m) (c w : ℕ) : Prop where
  ref : ∀ i, (r.reference i).Bound c w
  marked : ∀ i j, (r.marked i j).Bound c w
  status : ∀ j, (r.status j).Bound c w

def RuleFields.row (r : RuleFields k m) : Row (Fin k) (Fin m) → Run (Comparison (Fin k) (Fin m))
  | .unmarked i j => do let b ← r.marked i j; step 0 (if b then compare .zero .zero else compare (.flow i j) .zero)
  | .referenceCost i j => do let t ← r.reference i; step 0 (compare (.cost i t) (.cost i j) false true)
  | .markedCost i j => do
    let b ← r.marked i j
    let t ← r.reference i
    step 0 (if b then compare (.cost i j) (.cost i t) false true else compare .zero .zero)
  | .fixLower j => do let s ← r.status j
                      step 0 (if s = .lower then compare (.coverage j) .zero else compare .zero .zero)
  | .fixUpper j => do let s ← r.status j
                      step 0 (if s = .upper then compare .one (.coverage j) else compare .zero .zero)
  | .pressureLe j => do let s ← r.status j
                        step 0 (if s = .upper then compare .zero .zero else compare (.pressure j) .threshold false true)
  | .pressureGe j => do let s ← r.status j
                        step 0 (if s = .lower then compare .zero .zero else compare .threshold (.pressure j) false true)
  | .coverageLower j => step 0 (compare .zero (.coverage j))
  | .coverageUpper j => step 0 (compare (.coverage j) .one)
  | .budgetLe => step 0 (compare .coverageSum .budget)
  | .budgetGe => step 0 (compare .budget .coverageSum)
  | .flowLower i j => step 0 (compare .zero (.flow i j))
  | .rowLe i => step 0 (compare (.flowSum i) (.prior i))
  | .rowGe i => step 0 (compare (.prior i) (.flowSum i))
  | .thresholdLower => step 0 (compare .zero .threshold)
  | .residualLower => step 0 (compare .zero .zero false true)
  | .residualUpper => step 0 (compare .zero .one true false)

theorem RuleFields.row_value {r : RuleFields k m} {p : Pattern (Fin k) (Fin m)} (rd : RuleReads r p)
    (i : Row (Fin k) (Fin m)) : (r.row i).value = comparison p i := by
  cases i <;> simp [RuleFields.row,comparison,rd.ref,rd.marked,rd.status]

theorem RuleFields.row_work {r : RuleFields k m} {c w : ℕ} (ok : RuleBound r c w)
    (i : Row (Fin k) (Fin m)) : (r.row i).Bound (2*c+1) w := by
  cases i <;> simp only [RuleFields.row,Run.Bound,Run.bind_slots,Run.bind_width,step_width,
    step_slots,max_le_iff]
  all_goals first
    | exact ⟨by omega,Nat.zero_le _⟩
    | (rename_i i j; have hm := ok.marked i j; have hr := ok.ref i; dsimp only [Run.Bound] at hm hr; omega)
    | (rename_i j; have hs := ok.status j; dsimp only [Run.Bound] at hs; omega)

def readRuleWork (r : RuleFields k m) (i : Fin (exactRows k m)) :
    Run (Option (Comparison (Fin k) (Fin m))) := do
  let tag ← rowId i
  match tag with
  | .inl j => do let c ← r.row j; step 0 (some c)
  | .inr _ => step 0 none

theorem readRuleWork_value {r : RuleFields k m} {p : Pattern (Fin k) (Fin m)}
    (rd : RuleReads r p) (i : Fin (exactRows k m)) :
    (readRuleWork r i).value = RowWork.rule p i := by
  simp only [readRuleWork,Run.bind_value,rowId_value,RowWork.rule]
  cases (rowIndex k m).symm i <;> simp [RuleFields.row_value rd]

theorem readRuleWork_bound {r : RuleFields k m} {c w : ℕ} (ok : RuleBound r c w)
    (idx : indexWidth k m ≤ w) (i : Fin (exactRows k m)) :
    (readRuleWork r i).Bound (12+(2*c+2)) w := by
  apply bound_bind ((rowId_work i).weaken le_rfl idx)
  split
  · apply bound_bind (l := 1) (r.row_work ok _)
    exact (bound_step 0 _).weaken le_rfl (Nat.zero_le _)
  · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)

end Kintali.TrialWork
