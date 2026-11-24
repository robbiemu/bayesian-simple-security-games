module

public import StochasticGames.LinearFeasibilityGap
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
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

omit [Fintype κ] [DecidableEq ι] in
/-- Every coordinate attains its minimum on a nonempty bounded real polyhedron. -/
theorem exists_coordinate_minimum (A : Matrix κ ι ℝ) (b : κ → ℝ)
    (bounded : Bounded A b) (i : ι) {x : ι → ℝ} (feasible : Feasible A b x) :
    ∃ m, Feasible A b m ∧ ∀ y, Feasible A b y → m i ≤ y i := by
  obtain ⟨C, bound⟩ := bounded
  have compact : IsCompact {v | Feasible A b v} := by
    apply (isCompact_Icc (a := fun _ : ι => -C) (b := fun _ : ι => C)).of_isClosed_subset
    · change IsClosed {v | ∀ j, A.mulVec v j ≤ b j}
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro j
      change IsClosed {v : ι → ℝ | ∑ k, A j k * v k ≤ b j}
      apply isClosed_le _ continuous_const
      fun_prop
    · intro v hv
      exact ⟨fun j => (abs_le.mp (bound v hv j)).1, fun j => (abs_le.mp (bound v hv j)).2⟩
  obtain ⟨m, hm, optimal⟩ := compact.exists_isMinOn ⟨x, feasible⟩ (continuous_apply i).continuousOn
  exact ⟨m, hm, fun _ hy => optimal hy⟩

private theorem rational_coordinates_of_basis (M : Matrix ι ι ℤ) (c : ι → ℤ)
    (D : ℚ) (Dpos : 0 < D) (detM : M.det ≠ 0) (z : ι → ℝ)
    (tight : ((Int.castRingHom ℝ).mapMatrix M).mulVec (fun j => (D : ℝ) * z j) =
      fun i => (c i : ℝ)) :
    ∃ y : ι → ℚ, (fun i => (y i : ℝ)) = z := by
  refine ⟨fun i => (M.cramer c i : ℚ) / ((M.det : ℚ) * D), ?_⟩
  funext i
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_intCast]
  apply (div_eq_iff (mul_ne_zero (Int.cast_ne_zero.mpr detM) (by exact_mod_cast Dpos.ne'))).2
  rw [← DeterminantGap.cramer_scaled_coordinate M c (D : ℝ) z tight i]
  ring

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
  obtain ⟨y, castY⟩ := rational_coordinates_of_basis M c D Dpos detM z tight
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

/-- Hadamard's inequality with an arbitrary finite coordinate type and real
row-length bound. -/
theorem real_det_abs_le_of_row_squares (M : Matrix ι ι ℝ) (A : ℝ) (hn : 0 ≤ A)
    (rows : ∀ i, ∑ j, (M i j)^2 ≤ A^2) : |M.det| ≤ A ^ Fintype.card ι := by
  let e := Fintype.equivFin ι
  have bound := abs_det_fin_le_of_row_squares (Matrix.reindex e e M) A hn (fun i => by
    change (∑ j, (M (e.symm i) (e.symm j))^2) ≤ A^2
    rw [Equiv.sum_comp e.symm (fun j => (M (e.symm i) j)^2)]
    exact rows _)
  simpa only [Matrix.det_reindex_self] using bound

/-- Hadamard's determinant bound for an integer matrix, using squared row
lengths so that the hypothesis is entirely in integer arithmetic. -/
theorem det_abs_le_of_row_squares (M : Matrix ι ι ℤ) (h : ℤ) (nonnegative : 0 ≤ h)
    (rowSquares : ∀ i, ∑ j, (M i j) ^ 2 ≤ h ^ 2) :
    |M.det| ≤ h ^ Fintype.card ι := by
  have bound := real_det_abs_le_of_row_squares ((Int.castRingHom ℝ).mapMatrix M) (h : ℝ)
    (by exact_mod_cast nonnegative) (fun i => by
      change (∑ j, (M i j : ℝ)^2) ≤ (h : ℝ)^2
      exact_mod_cast rowSquares i)
  change |((Int.castRingHom ℝ).mapMatrix M).det| ≤ _ at bound
  rw [← (Int.castRingHom ℝ).map_det] at bound
  change |(M.det : ℝ)| ≤ (h : ℝ) ^ Fintype.card ι at bound
  exact_mod_cast bound

/-- A coordinate optimum occurs at a rational point. When positive, its value
satisfies the gap in H4, Lemma 3, including on lower-dimensional polyhedra. -/
theorem exists_rational_extremal_coordinate (M : Matrix κ ι ℤ) (rhs : κ → ℝ)
    (B : ℕ) (hB : 0 < B) (A : ℝ)
    (rowNorm : ∀ i, Real.sqrt (∑ j, (M i j : ℝ)^2) ≤ A)
    (clears : ∀ i, ∃ z : ℤ, (B : ℝ) * rhs i = z)
    (bounded : Bounded (realMatrix M) rhs) (i : ι) (x : ι → ℝ)
    (feasible : Feasible (realMatrix M) rhs x)
    (extremal : (∀ y, Feasible (realMatrix M) rhs y → x i ≤ y i) ∨
      (∀ y, Feasible (realMatrix M) rhs y → y i ≤ x i)) :
    ∃ q : ι → ℚ, Feasible (realMatrix M) rhs (fun k => (q k : ℝ)) ∧ (q i : ℝ) = x i ∧
      (0 < x i → 1 / ((B : ℝ) * A ^ Fintype.card ι) ≤ x i) := by
  have onFace (obj : (ι → ℝ) →ₗ[ℝ] ℝ)
      (flat : ∀ y, Feasible (realMatrix M) rhs y → obj y ≤ obj x → y i = x i) :
      ∃ q : ι → ℚ, Feasible (realMatrix M) rhs (fun k => (q k : ℝ)) ∧ (q i : ℝ) = x i ∧
        (0 < x i → 1 / ((B : ℝ) * A ^ Fintype.card ι) ≤ x i) := by
    obtain ⟨y, feasibleY, noLarger, kernelZero⟩ := exists_tight_point _ _ bounded obj feasible
    have same := flat y feasibleY noLarger
    obtain ⟨p, active, nonsingular⟩ :=
      TightRows.exists_active_nonsingular_submatrix _ _ kernelZero
    let C := M.submatrix p id
    choose z hz using clears
    have det : (C.det : ℝ) ≠ 0 := by
      intro zero
      apply nonsingular
      change ((Int.castRingHom ℝ).mapMatrix C).det = 0
      rwa [← (Int.castRingHom ℝ).map_det]
    have normNonneg : 0 ≤ A := (Real.sqrt_nonneg _).trans (rowNorm (p i))
    have bound := real_det_abs_le_of_row_squares ((Int.castRingHom ℝ).mapMatrix C) A normNonneg
      (fun k => by
        change (∑ j, (M (p k) j : ℝ)^2) ≤ A^2
        have hn : 0 ≤ ∑ j, (M (p k) j : ℝ)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        rw [← Real.sq_sqrt hn]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (rowNorm _) 2)
    rw [← (Int.castRingHom ℝ).map_det] at bound
    change |(C.det : ℝ)| ≤ A^Fintype.card ι at bound
    have tight : ((Int.castRingHom ℝ).mapMatrix C).mulVec (fun j => (B : ℝ)*y j) =
        (fun k => (z (p k) : ℝ)) := by
      funext k
      change (realMatrix M).mulVec ((B : ℝ) • y) (p k) = _
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, (mem_tightRows _ _ _ _).mp (active k)]
      exact hz _
    obtain ⟨q, hq⟩ := rational_coordinates_of_basis C (z ∘ p) (B : ℚ)
      (by exact_mod_cast hB) (Int.cast_ne_zero.mp det) y (by simpa using tight)
    refine ⟨q, hq.symm ▸ feasibleY, (congrFun hq i).trans same, fun positive => ?_⟩
    rw [← same]
    exact DeterminantGap.positive_coordinate_gap C (z ∘ p) (B : ℝ) _ y tight
      (Int.cast_ne_zero.mp det) (by exact_mod_cast hB) ((abs_pos.mpr det).trans_le bound)
      bound i (same.symm ▸ positive)
  rcases extremal with lower | upper
  · exact onFace (LinearMap.proj i) (fun y hy h => le_antisymm h (lower y hy))
  · exact onFace (-LinearMap.proj i)
      (fun y hy h => le_antisymm (upper y hy) (neg_le_neg_iff.mp h))

/-- H4, Lemma 3. A positive minimum or maximum is at least the reciprocal of the
clearing denominator times the d-th power of the bound on the Euclidean row lengths. -/
theorem positive_extremal_coordinate_gap (M : Matrix κ ι ℤ) (rhs : κ → ℝ)
    (B : ℕ) (hB : 0 < B) (A : ℝ)
    (rowNorm : ∀ i, Real.sqrt (∑ j, (M i j : ℝ)^2) ≤ A)
    (clears : ∀ i, ∃ z : ℤ, (B : ℝ) * rhs i = z)
    (bounded : Bounded (realMatrix M) rhs) (i : ι) (x : ι → ℝ)
    (feasible : Feasible (realMatrix M) rhs x)
    (extremal : (∀ y, Feasible (realMatrix M) rhs y → x i ≤ y i) ∨
      (∀ y, Feasible (realMatrix M) rhs y → y i ≤ x i))
    (positive : 0 < x i) : 1 / ((B : ℝ) * A ^ Fintype.card ι) ≤ x i := by
  obtain ⟨_, _, _, separation⟩ :=
    exists_rational_extremal_coordinate M rhs B hB A rowNorm clears bounded i x feasible extremal
  exact separation positive

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
