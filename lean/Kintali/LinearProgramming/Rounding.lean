module

public import Kintali.LinearProgramming.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Recovering exact feasibility from a supplied approximate point

A pivot selects some nearly tight equations. Its integer matrix lifts their
slacks to a correction of the variables, with one integer denominator.
For a represented row, the residual after that correction times the pivot
denominator is an integer. The gap bound forces that integer to vanish.
Rows separated from zero stay feasible under the same correction.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open scoped BigOperators

variable {m n k : ℕ}

namespace System

def slack (P : System (Fin m) (Fin n)) (x : Fin n → ℚ) (i : Fin m) : ℚ :=
  (P.rhs i : ℚ) - P.matrix.mulVec x i

theorem feasible_iff_slack (P : System (Fin m) (Fin n)) (x : Fin n → ℚ) :
    P.Feasible x ↔ ∀ i, 0 ≤ P.slack x i := by
  simp [Feasible, slack]

end System

/-- For a square minor this is the adjugate inserted at the pivot columns.
The rank-zero pivot uses the empty matrix and denominator one. -/
structure Pivot (m n k : ℕ) where
  rows : Fin k → Fin m
  lift : Matrix (Fin n) (Fin k) ℤ
  den : ℤ

namespace Pivot

variable (q : Pivot m n k) (P : System (Fin m) (Fin n))

def weights : Matrix (Fin m) (Fin k) ℤ := P.coeff * q.lift

def Represents (i : Fin m) : Prop :=
  ∀ j, q.den * P.coeff i j = (q.weights P * P.coeff.submatrix q.rows id) i j

def repair (x : Fin n → ℚ) : Fin n → ℚ :=
  x + (q.den : ℚ)⁻¹ •
    ((q.lift.map (Int.castRingHom ℚ)).mulVec (fun t => P.slack x (q.rows t)))

private theorem movement (x : Fin n → ℚ) (i : Fin m) :
    P.slack x i - P.slack (q.repair P x) i =
    ((q.weights P).map (Int.castRingHom ℚ)).mulVec (fun t => P.slack x (q.rows t)) i /
      (q.den : ℚ) := by
  rw [System.slack, System.slack, repair, Matrix.mulVec_add, Pi.add_apply,
    Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_mulVec]
  change _ = ((P.coeff * q.lift).map (Int.castRingHom ℚ)).mulVec _ i / _
  rw [Matrix.map_mul]
  rw [show P.matrix = P.coeff.map (Int.castRingHom ℚ) from rfl]
  ring

private theorem weighted_row_value {i : Fin m} (represented : q.Represents P i) (x : Fin n → ℚ) :
    (q.den : ℚ) * P.matrix.mulVec x i =
      ((q.weights P).map (Int.castRingHom ℚ)).mulVec
        (fun t => P.matrix.mulVec x (q.rows t)) i := by
  let C := (q.weights P).map (Int.castRingHom ℚ)
  let T := (P.coeff.submatrix q.rows id).map (Int.castRingHom ℚ)
  have rows : (q.den : ℚ) • P.matrix i = (C * T) i := by
    funext j
    change (Int.castRingHom ℚ) q.den * (Int.castRingHom ℚ) (P.coeff i j) =
      ((q.weights P).map (Int.castRingHom ℚ) *
        (P.coeff.submatrix q.rows id).map (Int.castRingHom ℚ)) i j
    rw [← map_mul, ← RingHom.map_matrix_mul]
    exact congrArg _ (represented j)
  calc
    _ = ((q.den : ℚ) • P.matrix i) ⬝ᵥ x := (smul_dotProduct ..).symm
    _ = (C * T).mulVec x i := congrArg (· ⬝ᵥ x) rows
    _ = _ := congrFun (Matrix.mulVec_mulVec x C T).symm i

/-- The variables outside the pivot can have arbitrary rational denominators.
For a represented row they cancel from the residual. -/
theorem integral_residual {i : Fin m} (represented : q.Represents P i) (nonzero : q.den ≠ 0)
    (x : Fin n → ℚ) :
    ∃ z : ℤ, (q.den : ℚ) * P.slack (q.repair P x) i = (z : ℚ) := by
  let C := (q.weights P).map (Int.castRingHom ℚ)
  let b := P.rhs ∘ q.rows
  let u := fun t => P.matrix.mulVec x (q.rows t)
  have den : (q.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr nonzero
  have changeRow := (eq_div_iff den).mp (q.movement P x i)
  have residuals : (fun t => P.slack x (q.rows t)) = (fun t => (b t : ℚ)) - u := rfl
  rw [residuals, Matrix.mulVec_sub, Pi.sub_apply] at changeRow
  have rowValue := q.weighted_row_value P represented x
  refine ⟨q.den * P.rhs i - (q.weights P).mulVec b i, ?_⟩
  have intValue := (Int.castRingHom ℚ).map_mulVec (q.weights P) b i
  rw [Int.cast_sub, Int.cast_mul]
  change (((q.weights P).mulVec b i : ℤ) : ℚ) = C.mulVec (fun t => (b t : ℚ)) i at intValue
  rw [intValue]
  unfold System.slack at changeRow ⊢
  dsimp only [u, b, Function.comp_apply] at changeRow
  change _ = (q.den : ℚ) * (P.rhs i : ℚ) - C.mulVec (fun t => (P.rhs (q.rows t) : ℚ)) i
  change (q.den : ℚ) * _ = C.mulVec _ i at rowValue
  change (_ - _) * _ = C.mulVec _ i - C.mulVec _ i at changeRow
  linarith only [changeRow, rowValue]

private theorem abs_dot_le {s : ℕ} (a v : Fin s → ℚ) {H E : ℚ} (hn : 0 ≤ H)
    (ha : ∀ j, |a j| ≤ H) (hv : ∀ j, |v j| ≤ E) :
    |a ⬝ᵥ v| ≤ (s : ℚ) * H * E := by
  calc
    _ ≤ ∑ j, |a j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin s, H * E := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul (ha j) (hv j) (abs_nonneg _) hn
    _ = _ := by simp [mul_assoc]

theorem movement_bound (x : Fin n → ℚ) (i : Fin m) {h g : ℕ} {a : ℚ}
    (nonzero : q.den ≠ 0) (coeff : ∀ r j, |P.coeff r j| ≤ (h : ℤ))
    (liftBound : ∀ j t, |q.lift j t| ≤ (g : ℤ)) (near : ∀ t, |P.slack x (q.rows t)| ≤ a) :
    |P.slack x i - P.slack (q.repair P x) i| ≤ ((k * n * h * g : ℕ) : ℚ) * a := by
  let C := (q.weights P).map (Int.castRingHom ℚ)
  have weight (t : Fin k) : |C i t| ≤ (n : ℚ) * h * g := by
    change |(P.coeff * q.lift).map (Int.castRingHom ℚ) i t| ≤ _
    rw [Matrix.map_mul]
    exact abs_dot_le _ _ (by positivity)
      (fun j => by change |((P.coeff i j : ℤ) : ℚ)| ≤ _; exact_mod_cast coeff i j)
      (fun j => by change |((q.lift j t : ℤ) : ℚ)| ≤ _; exact_mod_cast liftBound j t)
  have total := abs_dot_le (C i) _ (by positivity) weight near
  have one : (1 : ℚ) ≤ |(q.den : ℚ)| := by exact_mod_cast Int.one_le_abs nonzero
  rw [q.movement, abs_div]
  refine (div_le_self (abs_nonneg _) one).trans ?_
  change |C i ⬝ᵥ (fun j => P.slack x (q.rows j))| ≤ ((k * n * h * g : ℕ) : ℚ) * a
  push_cast
  simpa only [mul_assoc] using total

/-- At the chosen slack gap, the projected point satisfies every inequality. -/
theorem repair_feasible (x : Fin n → ℚ) {h g : ℕ} {a : ℚ}
    (nonzero : q.den ≠ 0) (coeff : ∀ r j, |P.coeff r j| ≤ (h : ℤ))
    (liftBound : ∀ j t, |q.lift j t| ≤ (g : ℤ)) (denBound : |q.den| ≤ (g : ℤ))
    (near : ∀ t, |P.slack x (q.rows t)| ≤ a)
    (cover : ∀ i, |P.slack x i| ≤ a → q.Represents P i)
    (separated : ∀ i, |P.slack x i| ≤ a ∨ ((k * n * h * g : ℕ) : ℚ) * a ≤ P.slack x i)
    (tiny : (g : ℚ) * (a + ((k * n * h * g : ℕ) : ℚ) * a) < 1) :
    P.Feasible (q.repair P x) := by
  rw [System.feasible_iff_slack]
  intro i
  let s := P.slack x i
  let t := P.slack (q.repair P x) i
  let L : ℚ := (k * n * h * g : ℕ)
  have changeRow : |s - t| ≤ L * a := q.movement_bound P x i nonzero coeff liftBound near
  rcases separated i with close | far
  · obtain ⟨z, hz⟩ := q.integral_residual P (cover i close) nonzero x
    have ht : |t| ≤ a + L * a := by
      have triangle := abs_add_le s (t - s)
      rw [show s + (t - s) = t by ring, abs_sub_comm t s] at triangle
      exact triangle.trans (add_le_add close changeRow)
    have hd : |(q.den : ℚ)| ≤ (g : ℚ) := by exact_mod_cast denBound
    have hzlt : |(z : ℚ)| < 1 := by
      rw [← hz, abs_mul]
      exact (mul_le_mul hd ht (abs_nonneg _) (by positivity)).trans_lt tiny
    have z0 : z = 0 := by
      by_contra nz
      have ge : (1 : ℚ) ≤ |(z : ℚ)| := by exact_mod_cast Int.one_le_abs nz
      linarith
    rw [z0, Int.cast_zero] at hz
    exact le_of_eq ((mul_eq_zero.mp hz).resolve_left (Int.cast_ne_zero.mpr nonzero)).symm
  · exact sub_nonpos.mp (by linarith only [le_abs_self (s - t), changeRow, far] : 0 - t ≤ 0)

end Pivot

end Kintali.LinearProgramming
