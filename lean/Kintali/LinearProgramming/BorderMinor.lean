module

public import Kintali.LinearProgramming.Bounds

/-! # Bordered minors and pivot selection

Extending a nonsingular pivot with one more row and one more column tests the
corresponding residual coefficient. A Cramer identity computes the bordered
determinant, including when the starting minor has dimension zero.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open scoped BigOperators

namespace Border

variable {k : ℕ}

def matrix (w : ℤ) (v u : Fin k → ℤ) (M : Matrix (Fin k) (Fin k) ℤ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
  .of (Fin.cons (Fin.cons w v) (fun i => Fin.cons (u i) (M i)))

private theorem updateCol_mulVec (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)
    (z : Fin (k + 1) → ℤ) :
    (B.updateCol 0 (B.mulVec z)).det = B.det * z 0 := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

private theorem single_column (w : ℤ) (v u : Fin k → ℤ) (M : Matrix (Fin k) (Fin k) ℤ)
    (r : ℤ) :
    ((matrix w v u M).updateCol 0 (Fin.cons r 0)).det = r * M.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [matrix, Matrix.submatrix]
  exact Or.inl rfl

/-- The Schur complement numerator of the integer pivot. -/
theorem det_matrix (w : ℤ) (v u : Fin k → ℤ) (M : Matrix (Fin k) (Fin k) ℤ)
    (nonzero : M.det ≠ 0) :
    (matrix w v u M).det = w * M.det - v ⬝ᵥ (M.adjugate.mulVec u) := by
  let B := matrix w v u M
  let z : Fin (k + 1) → ℤ := Fin.cons M.det (-(M.adjugate.mulVec u))
  let r := w * M.det - v ⬝ᵥ (M.adjugate.mulVec u)
  have image : B.mulVec z = Fin.cons r 0 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∑ l, (Fin.cons w v : Fin (k + 1) → ℤ) l * z l) = r
      rw [Fin.sum_univ_succ]
      simp [z, r, dotProduct, sub_eq_add_neg]
    · have annihilate (j : Fin k) : M.mulVec (M.adjugate.mulVec u) j = M.det * u j := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
        rfl
      change (∑ l, (Fin.cons (u j) (M j) : Fin (k + 1) → ℤ) l * z l) = 0
      rw [Fin.sum_univ_succ]
      simp only [z, Fin.cons_zero, Fin.cons_succ, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      change u j * M.det + -M.mulVec (M.adjugate.mulVec u) j = _
      rw [annihilate, mul_comm]
      ring
  have identity := updateCol_mulVec B z
  rw [image, single_column] at identity
  exact mul_right_cancel₀ nonzero identity.symm

end Border

end Kintali.LinearProgramming
