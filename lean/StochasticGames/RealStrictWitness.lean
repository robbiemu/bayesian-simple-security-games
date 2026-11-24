module

public import StochasticGames.LinearFeasibilityGap
public import Mathlib.Basic.Real.Basic
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Tactic.Ring

/-! # Rational witnesses for bounded real polyhedra

A real feasible point with a positive margin gives a tight point with at least
that margin. Cramer's rule expresses every coordinate of the tight point as a
rational number. Hadamard's inequality gives the uniform denominator bound
from the Euclidean lengths of the rows.
-/

@[expose] public section

namespace StochasticGames.RealStrictWitness

open BoundedLinearProgram LinearFeasibilityGap

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

def realMatrix (A : Matrix κ ι ℤ) : Matrix κ ι ℝ :=
  A.map (fun z => (z : ℝ))

noncomputable def realRhs (b : κ → ℤ) (D : ℚ) : κ → ℝ :=
  fun i => (b i : ℝ) / (D : ℝ)

omit [Fintype κ] [DecidableEq ι] in
theorem feasible_cast_iff (A : Matrix κ ι ℤ) (b : κ → ℤ) (D : ℚ) (y : ι → ℚ) :
    Feasible (realMatrix A) (realRhs b D) (fun i => (y i : ℝ)) ↔
      Feasible (rationalMatrix A) (rationalRhs b D) y := by
  change (∀ i, ∑ j, (A i j : ℝ) * (y j : ℝ) ≤ (b i : ℝ) / (D : ℝ)) ↔
      ∀ i, ∑ j, (A i j : ℚ) * y j ≤ (b i : ℚ) / D
  norm_cast

/-- A real feasible point gives a rational feasible point with no larger
objective, and each positive coordinate obeys the common basis bound. -/
theorem exists_point_with_gap_of_det_bound
    (A : Matrix κ ι ℤ) (b : κ → ℤ) (D B : ℚ) (Dpos : 0 < D) (Bpos : 0 < B)
    (detBound : ∀ rows : ι → κ, |((A.submatrix rows id).det : ℚ)| ≤ B)
    (bounded : Bounded (realMatrix A) (realRhs b D))
    (objective : (ι → ℝ) →ₗ[ℝ] ℝ) {x : ι → ℝ}
    (feasible : Feasible (realMatrix A) (realRhs b D) x) :
    ∃ y : ι → ℚ, Feasible (rationalMatrix A) (rationalRhs b D) y ∧
      objective (fun i => (y i : ℝ)) ≤ objective x ∧
      ∀ i, 0 < y i → 1 / (D * B) ≤ y i := by
  obtain ⟨z, feasibleZ, objectiveLe, kernelZero⟩ :=
    exists_tight_point _ _ bounded objective feasible
  obtain ⟨rows, active, nonsingular⟩ :=
    TightRows.exists_active_nonsingular_submatrix _ _ kernelZero
  let M := A.submatrix rows id
  let c := fun i => b (rows i)
  have detM : M.det ≠ 0 := by
    intro zero
    apply nonsingular
    change ((Int.castRingHom ℝ).mapMatrix M).det = 0
    rw [← (Int.castRingHom ℝ).map_det, zero, map_zero]
  have realD : 0 < (D : ℝ) := by exact_mod_cast Dpos
  have tight : ((Int.castRingHom ℝ).mapMatrix M).mulVec (fun j => (D : ℝ) * z j) =
      fun i => (c i : ℝ) := by
    funext i
    change (realMatrix A).mulVec ((D : ℝ) • z) (rows i) = _
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      (mem_tightRows _ _ _ _).1 (active i)]
    exact mul_div_cancel₀ _ realD.ne'
  let y (i : ι) : ℚ := (M.cramer c i : ℚ) / ((M.det : ℚ) * D)
  have castY : (fun i => (y i : ℝ)) = z := by
    funext i
    simp only [y, Rat.cast_div, Rat.cast_mul, Rat.cast_intCast]
    apply (div_eq_iff (mul_ne_zero (Int.cast_ne_zero.mpr detM) realD.ne')).2
    rw [← DeterminantGap.cramer_scaled_coordinate M c (D : ℝ) z tight i]
    ring
  refine ⟨y, (feasible_cast_iff A b D y).1 (castY.symm ▸ feasibleZ),
    castY.symm ▸ objectiveLe, ?_⟩
  intro i positive
  have posZ : 0 < z i := by
    rw [← castY]
    change 0 < (y i : ℝ)
    exact_mod_cast positive
  have boundReal : |(M.det : ℝ)| ≤ (B : ℝ) := by exact_mod_cast detBound rows
  have gap := DeterminantGap.positive_coordinate_gap M c (D : ℝ) (B : ℝ) z tight detM realD
    (by exact_mod_cast Bpos) boundReal i posZ
  rw [← castY] at gap
  change 1 / ((D : ℝ) * (B : ℝ)) ≤ (y i : ℝ) at gap
  exact_mod_cast gap

/-- Moving to a rational vertex preserves a positive margin and makes it
at least the reciprocal denominator bound. -/
theorem exists_uniform_margin_of_det_bound
    (A : Matrix κ ι ℤ) (b : κ → ℤ) (D B : ℚ) (Dpos : 0 < D) (Bpos : 0 < B)
    (detBound : ∀ rows : ι → κ, |((A.submatrix rows id).det : ℚ)| ≤ B)
    (bounded : Bounded (realMatrix A) (realRhs b D))
    (margin : ι) {x : ι → ℝ} (feasible : Feasible (realMatrix A) (realRhs b D) x)
    (positive : 0 < x margin) :
    ∃ y : ι → ℚ, Feasible (rationalMatrix A) (rationalRhs b D) y ∧
      1 / (D * B) ≤ y margin := by
  obtain ⟨y, feasibleY, greater, gap⟩ := exists_point_with_gap_of_det_bound
    A b D B Dpos Bpos detBound bounded (-LinearMap.proj margin) feasible
  have marginLe : x margin ≤ (y margin : ℝ) := neg_le_neg_iff.mp greater
  have positiveY : 0 < y margin := by exact_mod_cast positive.trans_le marginLe
  exact ⟨y, feasibleY, gap margin positiveY⟩

/-- An entry bound gives a margin using the elementary factorial determinant estimate. -/
theorem exists_uniform_margin
    (A : Matrix κ ι ℤ) (b : κ → ℤ) (D : ℚ) (h : ℤ)
    (Dpos : 0 < D) (hpos : 0 < h) (entryBound : ∀ i j, |A i j| ≤ h)
    (bounded : Bounded (realMatrix A) (realRhs b D))
    (margin : ι) {x : ι → ℝ} (feasible : Feasible (realMatrix A) (realRhs b D) x)
    (positive : 0 < x margin) :
    ∃ y : ι → ℚ, Feasible (rationalMatrix A) (rationalRhs b D) y ∧
      1 / (D * determinantBound ι h) ≤ y margin := by
  apply exists_uniform_margin_of_det_bound A b D _ Dpos (determinantBound_pos hpos) _
    bounded margin feasible positive
  intro rows
  have bound := DeterminantGap.det_abs_le_of_entries (A.submatrix rows id) h
    (fun i j => entryBound (rows i) j)
  unfold determinantBound
  exact_mod_cast bound

private theorem abs_det_fin_le_of_row_squares {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : ℝ) (nonnegative : 0 ≤ h) (rows : ∀ i, ∑ j, (M i j) ^ 2 ≤ h ^ 2) :
    |M.det| ≤ h ^ n := by
  let v (i : Fin n) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (M i)
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨by simp⟩
  have coordinates : e.toBasis.toMatrix v = M.transpose := by
    ext i j
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rfl
  have volume := e.toBasis.orientation.abs_volumeForm_apply_le v
  rw [e.toBasis.orientation.volumeForm_robust e rfl, Module.Basis.det_apply, coordinates,
    Matrix.det_transpose] at volume
  have rowNorm (i : Fin n) : ‖v i‖ ≤ h := by
    apply (sq_le_sq₀ (norm_nonneg _) nonnegative).1
    rw [EuclideanSpace.real_norm_sq_eq]
    exact rows i
  calc
    |M.det| ≤ ∏ i, ‖v i‖ := volume
    _ ≤ ∏ _ : Fin n, h := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => rowNorm i)
    _ = h ^ n := by simp

/-- Hadamard's determinant bound for an integer matrix, using squared row
lengths so that the hypothesis is entirely in integer arithmetic. -/
theorem det_abs_le_of_row_squares (M : Matrix ι ι ℤ) (h : ℤ) (nonnegative : 0 ≤ h)
    (rowSquares : ∀ i, ∑ j, (M i j) ^ 2 ≤ h ^ 2) :
    |M.det| ≤ h ^ Fintype.card ι := by
  let e := Fintype.equivFin ι
  let R := (Int.castRingHom ℝ).mapMatrix M
  have bound := abs_det_fin_le_of_row_squares (Matrix.reindex e e R) (h : ℝ)
    (by exact_mod_cast nonnegative) (fun i => by
      change (∑ j, (M (e.symm i) (e.symm j) : ℝ) ^ 2) ≤ (h : ℝ) ^ 2
      rw [Equiv.sum_comp e.symm (fun j => (M (e.symm i) j : ℝ) ^ 2)]
      exact_mod_cast rowSquares (e.symm i))
  rw [Matrix.det_reindex_self] at bound
  change |((Int.castRingHom ℝ).mapMatrix M).det| ≤ _ at bound
  rw [← (Int.castRingHom ℝ).map_det] at bound
  change |(M.det : ℝ)| ≤ (h : ℝ) ^ Fintype.card ι at bound
  exact_mod_cast bound

/-- A real strict witness survives tightening by the reciprocal of the
right-hand-side denominator times the Hadamard bound. -/
theorem exists_uniform_margin_of_row_squares
    (A : Matrix κ ι ℤ) (b : κ → ℤ) (D : ℚ) (h : ℤ)
    (Dpos : 0 < D) (hpos : 0 < h) (rowSquares : ∀ i, ∑ j, (A i j) ^ 2 ≤ h ^ 2)
    (bounded : Bounded (realMatrix A) (realRhs b D))
    (margin : ι) {x : ι → ℝ} (feasible : Feasible (realMatrix A) (realRhs b D) x)
    (positive : 0 < x margin) :
    ∃ y : ι → ℚ, Feasible (rationalMatrix A) (rationalRhs b D) y ∧
      1 / (D * (h : ℚ) ^ Fintype.card ι) ≤ y margin := by
  apply exists_uniform_margin_of_det_bound A b D _ Dpos (pow_pos (by exact_mod_cast hpos) _) _
    bounded margin feasible positive
  intro rows
  exact_mod_cast det_abs_le_of_row_squares (A.submatrix rows id) h hpos.le
    (fun i => rowSquares (rows i))

/-- A rational feasible slack below the Hadamard gap can be repaired to zero. -/
theorem exists_zero_slack_of_row_squares
    (A : Matrix κ ι ℤ) (b : κ → ℤ) (D : ℚ) (h : ℤ)
    (Dpos : 0 < D) (hpos : 0 < h) (rowSquares : ∀ i, ∑ j, (A i j) ^ 2 ≤ h ^ 2)
    (bounded : Bounded (rationalMatrix A) (rationalRhs b D))
    (slack : ι) (nonnegative : ∀ y, Feasible (rationalMatrix A) (rationalRhs b D) y → 0 ≤ y slack)
    {x : ι → ℚ} (feasible : Feasible (rationalMatrix A) (rationalRhs b D) x)
    (small : x slack < 1 / (D * (h : ℚ) ^ Fintype.card ι)) :
    ∃ y, Feasible (rationalMatrix A) (rationalRhs b D) y ∧ y slack = 0 := by
  have detBound (rows : ι → κ) : |((A.submatrix rows id).det : ℚ)| ≤ (h : ℚ) ^ Fintype.card ι := by
    exact_mod_cast det_abs_le_of_row_squares (A.submatrix rows id) h hpos.le
      (fun i => rowSquares (rows i))
  obtain ⟨y, feasibleY, smaller, gap⟩ := LinearFeasibilityGap.exists_point_with_gap_of_det_bound
    A b D _ Dpos (pow_pos (by exact_mod_cast hpos) _) detBound bounded (LinearMap.proj slack) feasible
  refine ⟨y, feasibleY, le_antisymm ?_ (nonnegative y feasibleY)⟩
  by_contra! positive
  exact (not_lt_of_ge (gap slack positive)) (lt_of_le_of_lt smaller small)

end StochasticGames.RealStrictWitness
