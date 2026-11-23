module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! ## Separation from zero at a rational basis

Clearing the right-hand side by a common denominator makes a Cramer
numerator integral. This gives a uniform positive gap for a coordinate
of any nonsingular tight basis.
-/

public section

namespace StochasticGames
namespace DeterminantGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem cramer_mulVec (A : Matrix ι ι ℚ) (x : ι → ℚ) :
    A.cramer (A.mulVec x) = A.det • x := by
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem cast_cramer (A : Matrix ι ι ℤ) (b : ι → ℤ) (i : ι) :
    (A.cramer b i : ℚ) =
      ((Int.castRingHom ℚ).mapMatrix A).cramer (fun j => (b j : ℚ)) i := by
  simp only [Matrix.cramer_apply]
  change Int.castRingHom ℚ (A.updateCol i b).det = _
  rw [(Int.castRingHom ℚ).map_det]
  congr 1
  exact Matrix.map_updateCol (Int.castRingHom ℚ)

/-- A cleared integer right-hand side makes the scaled coordinate integral. -/
theorem cramer_scaled_coordinate (A : Matrix ι ι ℤ) (b : ι → ℤ) (D : ℚ)
    (x : ι → ℚ)
    (tight : ((Int.castRingHom ℚ).mapMatrix A).mulVec (fun i => D * x i) =
      (fun i => (b i : ℚ))) (i : ι) :
    (A.det : ℚ) * (D * x i) = (A.cramer b i : ℚ) := by
  have identity := cramer_mulVec ((Int.castRingHom ℚ).mapMatrix A) (fun j => D * x j)
  rw [tight] at identity
  have coordinate := congrFun identity i
  rw [← cast_cramer A b i] at coordinate
  change (A.cramer b i : ℚ) =
    ((Int.castRingHom ℚ).mapMatrix A).det * (D * x i) at coordinate
  rw [← (Int.castRingHom ℚ).map_det] at coordinate
  exact coordinate.symm

/-- Any positive coordinate is at least the reciprocal of the determinant bound
times the common denominator. -/
theorem positive_coordinate_gap (A : Matrix ι ι ℤ) (b : ι → ℤ) (D B : ℚ)
    (x : ι → ℚ)
    (tight : ((Int.castRingHom ℚ).mapMatrix A).mulVec (fun i => D * x i) =
      (fun i => (b i : ℚ)))
    (detNonzero : A.det ≠ 0) (Dpos : 0 < D) (Bpos : 0 < B)
    (detBound : |(A.det : ℚ)| ≤ B) (i : ι) (xpos : 0 < x i) :
    1 / (D * B) ≤ x i := by
  have determinantNonzero : (A.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr detNonzero
  have identity := cramer_scaled_coordinate A b D x tight i
  have numeratorNonzero : A.cramer b i ≠ 0 := by
    intro zeroNumerator
    rw [zeroNumerator, Int.cast_zero, mul_eq_zero] at identity
    exact identity.elim determinantNonzero (mul_ne_zero Dpos.ne' xpos.ne')
  have numeratorAbs : 1 ≤ |(A.cramer b i : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs numeratorNonzero
  have absIdentity := congrArg (fun q : ℚ => |q|) identity
  rw [abs_mul, abs_mul, abs_of_pos Dpos, abs_of_pos xpos] at absIdentity
  apply (div_le_iff₀ (mul_pos Dpos Bpos)).2
  calc
    1 ≤ |(A.det : ℚ)| * (D * x i) := absIdentity.symm ▸ numeratorAbs
    _ ≤ B * (D * x i) := mul_le_mul_of_nonneg_right detBound (mul_nonneg Dpos.le xpos.le)
    _ = x i * (D * B) := by ring

theorem det_abs_le_of_entries (A : Matrix ι ι ℤ) (h : ℤ)
    (entries : ∀ i j, |A i j| ≤ h) :
    |A.det| ≤ ((Fintype.card ι).factorial : ℤ) * h ^ Fintype.card ι := by
  simpa [nsmul_eq_mul] using
    (Matrix.det_le (A := A) (abv := AbsoluteValue.abs) (x := h) entries)

end DeterminantGap
end StochasticGames
