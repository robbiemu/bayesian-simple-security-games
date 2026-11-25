module

public import Kintali.TrialWork.StoredPattern
public import Kintali.TrialWork.Terms

/-! Exact relaxed feasibility test on the saved pattern and projected
point. A row costs two affine evaluations, one rational comparison and
the cost of decoding its row number. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery

variable {k m : ℕ} {α : Type}

def allM (test : α → Run Bool) : List α → Run Bool
  | [] => step 0 true
  | x::xs => do
    let i ← step 0 x
    let b ← test i
    if b then allM test xs else pure false

@[simp] theorem allM_value (test : α → Run Bool) (l : List α) :
    (allM test l).value = l.all (fun i => (test i).value) := by
  induction l with
  | nil => rfl
  | cons a as ih => cases h : (test a).value <;> simp [allM,h,ih]

theorem allM_work (test : α → Run Bool) (l : List α) {c w : ℕ}
    (ok : ∀ i, (test i).Bound c w) : (allM test l).Bound (1+l.length*(c+1)) w := by
  induction l with
  | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
  | cons a as ih =>
    have tail : (if (test a).value then allM test as else (pure false : Run Bool)).Bound
        (1+as.length*(c+1)) w := by
      cases h : (test a).value
      · exact (bound_pure _ _).weaken (Nat.zero_le _) le_rfl
      · exact ih
    have work := bound_bind ((bound_step 0 a).weaken le_rfl (Nat.zero_le w))
      (f := fun i => do let b ← test i; if b then allM test as else pure false) (bound_bind (ok a) tail)
    apply work.weaken _ le_rfl
    rw [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def checkRow (d : Fields k m) (v : Point k m) (r : RuleFields k m)
    (i : Fin (exactRows k m)) : Run Bool := do
  let rule ← readRuleWork r i
  match rule with
  | none => step 0 true
  | some p => do
    let lhs ← d.term v p.left
    let rhs ← d.term v p.right
    le lhs rhs

def relaxed (d : Fields k m) (v : Point k m) (r : RuleFields k m) : Run Bool :=
  finRange (exactRows k m) >>= allM (checkRow d v r)

theorem relaxed_value (d : Fields k m) (v : Point k m) {r : RuleFields k m}
    {p : Pattern (Fin k) (Fin m)} (rd : RuleReads r p)
    (view : MarketTrial.ContactView k m (MarketTrial.grid d.game))
    (x : v.x = view.coverage) (q : v.q = view.joint) (t : v.threshold = view.pressure)
    (e : v.tolerance = contactTolerance d.game) :
    (relaxed d v r).value = MarketTrial.relaxedCheck d.game p view := by
  simp only [relaxed,Run.bind_value,finRange_value,allM_value,MarketTrial.relaxedCheck]
  apply congrArg (List.all (List.finRange (exactRows k m)))
  funext i
  simp only [checkRow,Run.bind_value,readRuleWork_value rd,RowWork.rule]
  cases h : (rowIndex k m).symm i with
  | inl j => simp [x,q,t,e]
  | inr u => cases u; rfl

def relaxWidth (k m n w : ℕ) := indexWidth k m+checkWidth n w
def rowSlots (n c cr w : ℕ) := 12+(2*cr+2)+(2*termSlots n c w+3)
def relaxSlots (k m n c cr w : ℕ) :=
  2*exactRows k m+1+(1+exactRows k m*(rowSlots n c cr w+1))

theorem checkRow_work (d : Fields k m) {v : Point k m} {r : RuleFields k m} {n c cr w : ℕ}
    (ok : FieldBound d c w) (point : PointBound v w) (rules : RuleBound r cr w)
    (hk : k ≤ n) (hm : m ≤ n) (i : Fin (exactRows k m)) :
    (checkRow d v r i).Bound (rowSlots n c cr w) (relaxWidth k m n w) := by
  let U := relaxWidth k m n w
  have h : checkWidth n w ≤ U := Nat.le_add_left ..
  have hw : w ≤ U := (show w ≤ checkWidth n w by unfold checkWidth scalarWidth termBits; omega).trans h
  have ri : RuleBound r cr U :=
    ⟨fun i => (rules.ref i).weaken le_rfl hw,fun i j => (rules.marked i j).weaken le_rfl hw,
      fun j => (rules.status j).weaken le_rfl hw⟩
  unfold checkRow rowSlots
  apply bound_bind (readRuleWork_bound ri (Nat.le_add_right ..) i)
  cases hr : (readRuleWork r i).value with
  | none => exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
  | some cs =>
    have lhs := d.term_work ok point hk hm cs.left
    have rhs := d.term_work ok point hk hm cs.right
    apply Run.Bound.weaken (k := termSlots n c w+(termSlots n c w+3)) (w := U) ?_ (by omega) le_rfl
    apply bound_bind (lhs.1.weaken le_rfl h)
    apply bound_bind (rhs.1.weaken le_rfl h)
    exact (le_work lhs.2 rhs.2).weaken le_rfl h

theorem relaxed_work (d : Fields k m) {v : Point k m} {r : RuleFields k m} {n c cr w : ℕ}
    (ok : FieldBound d c w) (point : PointBound v w) (rules : RuleBound r cr w)
    (hk : k ≤ n) (hm : m ≤ n) :
    (relaxed d v r).Bound (relaxSlots k m n c cr w) (relaxWidth k m n w) := by
  have idx : (exactRows k m).size ≤ relaxWidth k m n w :=
    (size_le_self _).trans (by unfold relaxWidth indexWidth; omega)
  apply bound_bind ((finRange_bound _).weaken le_rfl idx)
  rw [finRange_value]
  simpa only [List.length_finRange] using allM_work _ (List.finRange (exactRows k m))
    (checkRow_work d ok point rules hk hm)

end Kintali.TrialWork
