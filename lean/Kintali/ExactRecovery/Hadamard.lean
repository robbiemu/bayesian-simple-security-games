module

public import Kintali.ExactRecovery.Determinant
public import StochasticGames.RealStrictWitness
import Mathlib.Tactic.Positivity

/-! # The intermediate Hadamard estimate in Lemma 2

The integer bound (n C)^n also follows elementarily from the determinant
expansion. Here the Euclidean row lengths give the paper's sharper intermediate
estimate (√n C)^n for exactly the same pattern matrix.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.ExactRecovery

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem determinant_hadamard (g : Game I J) (p : Pattern I J) (rows : Variable I J → Row I J) :
    |(((matrix g p).submatrix rows id).det : ℝ)| ≤
      (Real.sqrt (Fintype.card (Variable I J)) * ((2 * atomBound g : ℤ) : ℝ)) ^
        Fintype.card (Variable I J) := by
  let A := (matrix g p).submatrix rows id
  let B := (Int.castRingHom ℝ).mapMatrix A
  let n := Fintype.card (Variable I J)
  let C := ((2 * atomBound g : ℤ) : ℝ)
  have cp : 0 ≤ C := by
    dsimp only [C]
    exact_mod_cast (show (0 : ℤ) ≤ 2 * atomBound g by
      exact mul_nonneg (by decide) (atomBound_pos g).le)
  have entry (i j : Variable I J) : |B i j| ≤ C := by
    change |(matrix g p (rows i) j : ℝ)| ≤ ((2 * atomBound g : ℤ) : ℝ)
    exact_mod_cast matrix_bound g p (rows i) j
  have lengths (i : Variable I J) : (∑ j, (B i j)^2) ≤ (Real.sqrt n * C)^2 := by
    have square (j : Variable I J) : (B i j)^2 ≤ C^2 := by
      rw [← sq_abs (B i j)]
      exact pow_le_pow_left₀ (abs_nonneg _) (entry i j) 2
    calc
      _ ≤ ∑ _j : Variable I J, C^2 := Finset.sum_le_sum fun j _ => square j
      _ = (n : ℝ) * C^2 := by simp [nsmul_eq_mul,n]
      _ = (Real.sqrt (n : ℝ) * C)^2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have bound := StochasticGames.RealStrictWitness.real_det_abs_le_of_row_squares B _
    (mul_nonneg (Real.sqrt_nonneg _) cp) lengths
  change |((Int.castRingHom ℝ).mapMatrix A).det| ≤ _ at bound
  rw [← (Int.castRingHom ℝ).map_det] at bound
  exact bound

end Kintali.ExactRecovery
