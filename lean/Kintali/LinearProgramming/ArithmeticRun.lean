module

public import StochasticGames.CompilerRun
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Charged array tabulation and signed word summation

The results use the project's binary word-cost model. A new vector reserves
space for its cells. The tabulator charges indices and writes in addition
to each supplied cell computation. Summation charges the actual widths of
both operands of every signed addition, including the partial sums.
-/

@[expose] public section

namespace Kintali.LinearProgramming.ArithmeticRun

open scoped BigOperators
open StochasticGames.CompilerRun

variable {α : Type} {n : ℕ}

/-- The calls producing the cells are materialized once, before reading
their results and combining their work annotations. -/
def tabulate (n : ℕ) (f : Fin n → Run α) : Run (Vector α n) :=
  let cells := Vector.ofFn f
  ⟨Vector.ofFn (fun i : Fin n => cells[i.val].value),
    ⟨3*(n+1) + ∑ i : Fin n, cells[i.val].work.slots,
      max n.size (Finset.univ.sup (fun i : Fin n => cells[i.val].work.width))⟩⟩

@[simp] theorem tabulate_value (f : Fin n → Run α) :
    (tabulate n f).value = Vector.ofFn (fun i => (f i).value) := by simp [tabulate]

theorem tabulate_bound (f : Fin n → Run α) {cost w : ℕ}
    (indices : n.size ≤ w) (each : ∀ i, (f i).Bound cost w) :
    (tabulate n f).Bound (3*(n+1) + n*cost) w := by
  constructor
  · simp only [tabulate, Vector.getElem_ofFn]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑ _ : Fin n, cost := Finset.sum_le_sum fun i _ => (each i).1
      _ = _ := by simp
  · simp only [tabulate, Vector.getElem_ofFn]
    exact max_le indices (Finset.sup_le (fun i _ => (each i).2))

def sum (f : α → Run ℤ) : List α → Run ℤ
  | [] => step 0 0
  | j :: js => do
    let _ ← step 0 ()
    let term ← f j
    let rest ← sum f js
    intAdd term rest

@[simp] theorem sum_value (f : α → Run ℤ) (xs : List α) :
    (sum f xs).value = (xs.map (fun j => (f j).value)).sum := by
  induction xs with
  | nil => rfl
  | cons j js ih => simp [sum, intAdd, ih]

theorem sum_magnitude (f : α → Run ℤ) {B : ℕ} (bounded : ∀ i, (f i).value.natAbs ≤ B)
    (xs : List α) : (sum f xs).value.natAbs ≤ xs.length * B := by
  induction xs with
  | nil => simp [sum]
  | cons j js ih =>
    change ((f j).value + (sum f js).value).natAbs ≤ _
    have bound := Nat.add_le_add (bounded j) ih
    exact (Int.natAbs_add_le ..).trans (by simpa [Nat.succ_mul, Nat.add_comm] using bound)

theorem sum_bound (f : α → Run ℤ) {B cost w : ℕ} (bounded : ∀ i, (f i).value.natAbs ≤ B)
    (each : ∀ i, (f i).Bound cost w) (wide : ((n+1)*B).size + 1 ≤ w)
    (xs : List α) (length : xs.length ≤ n) :
    (sum f xs).Bound (1 + xs.length * (cost+2)) w := by
  induction xs with
  | nil => exact (bound_step 0 0).weaken (by simp) (Nat.zero_le _)
  | cons j js ih =>
    have shorter : js.length ≤ n := by simpa using (Nat.le_succ js.length).trans length
    have prior := ih shorter
    have maxSize : max (f j).value.natAbs.size (sum f js).value.natAbs.size ≤ ((n+1)*B).size :=
      max_le (Nat.size_le_size ((bounded j).trans (Nat.le_mul_of_pos_left _ (by omega))))
        (Nat.size_le_size ((sum_magnitude f bounded js).trans
          (Nat.mul_le_mul_right _ (Nat.le_succ_of_le shorter))))
    have add := (bound_step _ _ : (intAdd (f j).value (sum f js).value).Bound 1 _).weaken
      le_rfl ((Nat.add_le_add_right maxSize 1).trans wide)
    have head := bound_bind (f := fun a => do
      let b ← sum f js
      intAdd a b) (each j)
        (bound_bind (f := fun b => intAdd (f j).value b) prior add)
    exact (bound_bind (f := fun _ : Unit => do
      let a ← f j
      let b ← sum f js
      intAdd a b) ((bound_step 0 ()).weaken le_rfl (Nat.zero_le _)) head).weaken
        (by simp [Nat.succ_mul]; omega) le_rfl

/-- Scan until the first successful optional answer. Each visited cell
charges the list and status checks, including the last failed one. -/
def first {β : Type} (f : α → Run (Option β)) : List α → Run (Option β)
  | [] => step 0 none
  | x :: xs => do
    let _ ← step 0 ()
    let v ← f x
    match ← step 0 v with
    | some b => pure (some b)
    | none => first f xs

@[simp] theorem first_value {β : Type} (f : α → Run (Option β)) (xs : List α) :
    (first f xs).value = xs.findSome? (fun i => (f i).value) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    cases h : (f i).value <;> simp [first, h, ih]

theorem first_bound {β : Type} (f : α → Run (Option β)) {cost w : ℕ}
    (each : ∀ i, (f i).Bound cost w) (xs : List α) :
    (first f xs).Bound (1 + xs.length*(cost+2)) w := by
  induction xs with
  | nil => exact (bound_step 0 none).weaken (by simp) (Nat.zero_le _)
  | cons i xs ih =>
    let branch : Option β → Run (Option β) := fun v =>
      match v with | some b => pure (some b) | none => first f xs
    have hb : (branch (f i).value).Bound (1+xs.length*(cost+2)) w := by
      cases h : (f i).value with
      | none => exact ih
      | some b => exact (bound_pure _ w).weaken (Nat.zero_le _) le_rfl
    have check := bound_bind (f := branch) ((bound_step 0 (f i).value).weaken le_rfl (Nat.zero_le w)) hb
    have body := bound_bind (f := fun v => step 0 v >>= branch) (each i) check
    exact (bound_bind (f := fun _ : Unit => f i >>= (fun v => step 0 v >>= branch))
      ((bound_step 0 ()).weaken le_rfl (Nat.zero_le w)) body).weaken
      (by simp [Nat.succ_mul]; omega) le_rfl

end Kintali.LinearProgramming.ArithmeticRun
