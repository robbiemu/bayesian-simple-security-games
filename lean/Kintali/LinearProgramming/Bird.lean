module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import all Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Integer determinant with stored intermediate matrices

Richard Bird's division-free recurrence, as verified in Mathlib, is evaluated
one table at a time. Each lookup in a stage reads a previously materialized
integer. The stage bound also bounds the intermediate partial sums in its two
dot products.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open scoped BigOperators

namespace Bird

abbrev Table (n : ℕ) := Vector (Vector ℤ n) n

def tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Table n :=
  Vector.ofFn fun i => Vector.ofFn (A i)

def entries {n : ℕ} (T : Table n) : Matrix (Fin n) (Fin n) ℤ :=
  .of fun i j => T[i.val][j.val]

@[simp] theorem entries_tabulate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    entries (tabulate A) = A := by
  ext i j
  simp [entries, tabulate]

def stages {n : ℕ} (A : Table n) : ℕ → Table n
  | 0 => A
  | t + 1 =>
    let F := stages A t
    tabulate (BirdDet.Spec.stepEntry (entries A) (entries F))

theorem stages_spec {n : ℕ} (A : Table n) (t : ℕ) :
    entries (stages A t) = (BirdDet.Spec.stepEntry (entries A))^[t] (entries A) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stages, entries_tabulate, ih, Function.iterate_succ_apply']

theorem sum_bound {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℤ) {H : ℤ} (hn : 0 ≤ H)
    (bound : ∀ i, |f i| ≤ H) : |∑ i ∈ s, f i| ≤ (n : ℤ) * H := by
  calc
    _ ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ s, H := Finset.sum_le_sum fun i _ => bound i
    _ = (s.card : ℤ) * H := by simp
    _ ≤ _ := by
      have count : s.card ≤ n := by simpa using Finset.card_le_univ s
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast count) hn

theorem step_bound {n h b : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ)
    (input : ∀ i j, |A i j| ≤ (h : ℤ)) (prior : ∀ i j, |F i j| ≤ (b : ℤ)) (i j : Fin n) :
    |BirdDet.Spec.stepEntry A F i j| ≤ ((2 * n * h * b : ℕ) : ℤ) := by
  rw [BirdDet.Spec.stepEntry_eq, Matrix.of_apply]
  have diagonal := sum_bound (Finset.Ioi i) _ (by positivity) (fun k => prior k k)
  have term (k : Fin n) : |F i k * A k j| ≤ (b : ℤ) * h := by
    rw [abs_mul]
    exact mul_le_mul (prior i k) (input k j) (abs_nonneg _) (by positivity)
  have row := sum_bound (Finset.Ioi i) _ (by positivity) term
  calc
    _ ≤ |(-∑ k ∈ Finset.Ioi i, F k k) * A i j| +
      |∑ k ∈ Finset.Ioi i, F i k * A k j| := abs_add_le ..
    _ ≤ ((n : ℤ) * b) * h + n * ((b : ℤ) * h) := by
      rw [abs_mul, abs_neg]
      exact add_le_add (mul_le_mul diagonal (input i j) (abs_nonneg _) (by positivity)) row
    _ = _ := by push_cast; ring

theorem stages_bound {n h : ℕ} (A : Table n) (input : ∀ i j, |entries A i j| ≤ (h : ℤ))
    (t : ℕ) (i j : Fin n) :
    |entries (stages A t) i j| ≤ (((2 * n * h) ^ t * h : ℕ) : ℤ) := by
  induction t generalizing i j with
  | zero => simpa [stages] using input i j
  | succ t ih =>
    rw [stages, entries_tabulate]
    apply (step_bound _ _ input ih i j).trans
    apply le_of_eq
    push_cast
    rw [pow_succ]
    ring

end Bird

/-- Integer determinant computed from stored Bird tables. -/
def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0, _ => 1
  | t + 1, A => (-1 : ℤ) ^ t * Bird.entries (Bird.stages (Bird.tabulate A) t) 0 0

@[simp] theorem determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    determinant A = A.det := by
  rw [BirdDet.birdDetSpec_eq_det]
  cases n with
  | zero => simp [determinant]
  | succ t =>
    rw [determinant, Bird.stages_spec, Bird.entries_tabulate, BirdDet.Spec.birdDetSpec_succ]

end Kintali.LinearProgramming
