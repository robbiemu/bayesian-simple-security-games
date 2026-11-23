module

public import StochasticGames.BoundedLinearProgram
public import StochasticGames.DeterminantGap
public import StochasticGames.TightRows

/-! ## Bounded linear programs have a rational coordinate gap

Find a point with spanning tight rows, use those rows as a basis, and apply
the determinant gap. Minimizing the slack tests exact feasibility. Maximizing
a common margin performs the same step for a system with strict rows.
-/

public section

namespace StochasticGames
namespace LinearFeasibilityGap

open BoundedLinearProgram

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

def rationalMatrix (A : Matrix κ ι ℤ) : Matrix κ ι ℚ :=
  A.map (fun value => (value : ℚ))

def rationalRhs (b : κ → ℤ) (D : ℚ) : κ → ℚ :=
  fun i => (b i : ℚ) / D

def determinantBound (ι : Type*) [Fintype ι] (h : ℤ) : ℚ :=
  ((Fintype.card ι).factorial : ℚ) * (h : ℚ) ^ Fintype.card ι

omit [DecidableEq ι] in
private theorem determinantBound_pos {h : ℤ} (hpos : 0 < h) :
    0 < determinantBound ι h := by
  have factorialPos : (0 : ℚ) < (Fintype.card ι).factorial := by
    exact_mod_cast Nat.factorial_pos (Fintype.card ι)
  have boundPos : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hpos
  exact mul_pos factorialPos (pow_pos boundPos _)

/-- A bounded feasible system admits a point no worse for the given objective
whose positive coordinates satisfy the same determinant bound. -/
theorem exists_point_with_gap (A : Matrix κ ι ℤ) (b : κ → ℤ) (D : ℚ) (h : ℤ)
    (Dpos : 0 < D) (hpos : 0 < h) (entryBound : ∀ i j, |A i j| ≤ h)
    (bounded : Bounded (rationalMatrix A) (rationalRhs b D))
    (objective : (ι → ℚ) →ₗ[ℚ] ℚ) {x : ι → ℚ}
    (feasible : Feasible (rationalMatrix A) (rationalRhs b D) x) :
    ∃ y, Feasible (rationalMatrix A) (rationalRhs b D) y ∧ objective y ≤ objective x ∧
      ∀ i, 0 < y i → 1 / (D * determinantBound ι h) ≤ y i := by
  obtain ⟨y, feasibleY, objectiveLe, kernelZero⟩ :=
    exists_tight_point _ _ bounded objective feasible
  obtain ⟨rows, active, detNonzero⟩ :=
    TightRows.exists_active_nonsingular_submatrix _ _ kernelZero
  let M := A.submatrix rows id
  have detM : M.det ≠ 0 := by
    intro zero
    apply detNonzero
    change ((Int.castRingHom ℚ).mapMatrix M).det = 0
    rw [← (Int.castRingHom ℚ).map_det, zero, map_zero]
  have tight : ((Int.castRingHom ℚ).mapMatrix M).mulVec (fun j => D * y j) =
      (fun i => (b (rows i) : ℚ)) := by
    funext i
    change (rationalMatrix A).mulVec (D • y) (rows i) = _
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      (mem_tightRows _ _ _ _).1 (active i)]
    exact mul_div_cancel₀ _ Dpos.ne'
  have boundM : |(M.det : ℚ)| ≤ determinantBound ι h := by
    have bound := DeterminantGap.det_abs_le_of_entries M h (fun i j => entryBound (rows i) j)
    unfold determinantBound
    exact_mod_cast bound
  exact ⟨y, feasibleY, objectiveLe, fun i => DeterminantGap.positive_coordinate_gap
    M _ D _ y tight detM Dpos (determinantBound_pos hpos) boundM i⟩

/-- A feasible slack strictly smaller than the uniform gap can be replaced by
an exact zero slack. -/
theorem exists_zero_slack (A : Matrix κ ι ℤ) (b : κ → ℤ) (D : ℚ) (h : ℤ)
    (Dpos : 0 < D) (hpos : 0 < h) (entryBound : ∀ i j, |A i j| ≤ h)
    (bounded : Bounded (rationalMatrix A) (rationalRhs b D))
    (slack : ι) (nonnegative :
      ∀ y, Feasible (rationalMatrix A) (rationalRhs b D) y → 0 ≤ y slack)
    {x : ι → ℚ} (feasible : Feasible (rationalMatrix A) (rationalRhs b D) x)
    (small : x slack < 1 / (D * determinantBound ι h)) :
    ∃ y, Feasible (rationalMatrix A) (rationalRhs b D) y ∧ y slack = 0 := by
  obtain ⟨y, feasibleY, smaller, gap⟩ :=
    exists_point_with_gap A b D h Dpos hpos entryBound bounded (LinearMap.proj slack) feasible
  refine ⟨y, feasibleY, le_antisymm ?_ (nonnegative y feasibleY)⟩
  by_contra! positive
  exact (not_lt_of_ge (gap slack positive)) (lt_of_le_of_lt smaller small)

/-- Any strictly positive feasible margin can be replaced by one at least the
uniform gap, while satisfying the same weak rows. -/
theorem exists_uniform_margin (A : Matrix κ ι ℤ) (b : κ → ℤ) (D : ℚ) (h : ℤ)
    (Dpos : 0 < D) (hpos : 0 < h) (entryBound : ∀ i j, |A i j| ≤ h)
    (bounded : Bounded (rationalMatrix A) (rationalRhs b D))
    (margin : ι) {x : ι → ℚ} (feasible : Feasible (rationalMatrix A) (rationalRhs b D) x)
    (positive : 0 < x margin) :
    ∃ y, Feasible (rationalMatrix A) (rationalRhs b D) y ∧
      1 / (D * determinantBound ι h) ≤ y margin := by
  obtain ⟨y, feasibleY, greater, gap⟩ :=
    exists_point_with_gap A b D h Dpos hpos entryBound bounded (-LinearMap.proj margin) feasible
  have vectorLe : x margin ≤ y margin := neg_le_neg_iff.mp greater
  exact ⟨y, feasibleY, gap margin (positive.trans_le vectorLe)⟩

end LinearFeasibilityGap
end StochasticGames
