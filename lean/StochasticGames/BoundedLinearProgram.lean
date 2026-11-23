module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! ## A tight point in a bounded linear system

Among feasible points no worse than a supplied point, choose one with as many
tight rows as possible. Any nonzero direction annihilated by those rows can
be signed to keep the objective from increasing. Move along it until another
row becomes tight, contradicting the choice of point.
-/

public section

namespace StochasticGames
namespace BoundedLinearProgram

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

def Feasible (A : Matrix κ ι ℚ) (b : κ → ℚ) (x : ι → ℚ) : Prop :=
  ∀ i, A.mulVec x i ≤ b i

def tightRows (A : Matrix κ ι ℚ) (b : κ → ℚ) (x : ι → ℚ) : Finset κ :=
  Finset.univ.filter (fun i => A.mulVec x i = b i)

def Bounded (A : Matrix κ ι ℚ) (b : κ → ℚ) : Prop :=
  ∃ B : ℚ, ∀ x, Feasible A b x → ∀ j, |x j| ≤ B

@[simp] theorem mem_tightRows (A : Matrix κ ι ℚ) (b : κ → ℚ) (x : ι → ℚ) (i : κ) :
    i ∈ tightRows A b x ↔ A.mulVec x i = b i := by
  simp [tightRows]

omit [Fintype κ] in
private theorem row_along (A : Matrix κ ι ℚ) (x d : ι → ℚ) (t : ℚ) (i : κ) :
    A.mulVec (x + t • d) i = A.mulVec x i + t * A.mulVec d i := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  rfl

private theorem exists_positive_row (A : Matrix κ ι ℚ) (b : κ → ℚ)
    (bounded : Bounded A b) {x d : ι → ℚ} (feasible : Feasible A b x) (nonzero : d ≠ 0) :
    ∃ i, 0 < A.mulVec d i := by
  by_contra! noPositive
  obtain ⟨B, bound⟩ := bounded
  have existsCoordinate : ∃ j, d j ≠ 0 := by
    by_contra! allZero
    apply nonzero
    funext j
    exact allZero j
  obtain ⟨j, directionNonzero⟩ := existsCoordinate
  have directionPos : 0 < |d j| := abs_pos.mpr directionNonzero
  have Bnonneg := (abs_nonneg (x j)).trans (bound x feasible j)
  let t := (2 * B + 1) / |d j|
  have tPos : 0 < t := by
    dsimp [t]
    apply div_pos _ directionPos
    linarith
  have feasibleRay : Feasible A b (x + t • d) := by
    intro i
    rw [row_along]
    exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos tPos.le
      (noPositive i))).trans (feasible i)
  have movement : |(x + t • d) j - x j| = 2 * B + 1 := by
    change |x j + t * d j - x j| = _
    rw [show x j + t * d j - x j = t * d j by ring, abs_mul, abs_of_pos tPos]
    exact div_mul_cancel₀ _ directionPos.ne'
  have limited := abs_sub_le ((x + t • d) j) 0 (x j)
  simp only [sub_zero, zero_sub, abs_neg] at limited
  rw [movement] at limited
  linarith [bound (x + t • d) feasibleRay j, bound x feasible j]

private theorem step_to_new_row (A : Matrix κ ι ℚ) (b : κ → ℚ)
    (bounded : Bounded A b) {x d : ι → ℚ} (feasible : Feasible A b x) (nonzero : d ≠ 0)
    (vanishing : ∀ i ∈ tightRows A b x, A.mulVec d i = 0) :
    ∃ t : ℚ, 0 < t ∧ Feasible A b (x + t • d) ∧
      tightRows A b x ⊂ tightRows A b (x + t • d) := by
  classical
  let rising := Finset.univ.filter (fun i => 0 < A.mulVec d i)
  let time := fun i => (b i - A.mulVec x i) / A.mulVec d i
  have rising_nonempty : rising.Nonempty := by
    obtain ⟨i, pos⟩ := exists_positive_row A b bounded feasible nonzero
    exact ⟨i, by simp [rising, pos]⟩
  obtain ⟨j, jMem, earliest⟩ := rising.exists_min_image time rising_nonempty
  have slope : 0 < A.mulVec d j := by simpa [rising] using jMem
  have notTight : j ∉ tightRows A b x := by
    intro already
    exact slope.ne' (vanishing j already)
  have strictSlack : A.mulVec x j < b j :=
    lt_of_le_of_ne (feasible j) (by simpa using notTight)
  have positiveTime : 0 < time j := div_pos (sub_pos.mpr strictSlack) slope
  refine ⟨time j, positiveTime, ?_, ?_⟩
  · intro i
    rw [row_along]
    by_cases rises : 0 < A.mulVec d i
    · have ile := earliest i (by simp [rising, rises])
      have timeLe : time j * A.mulVec d i ≤ b i - A.mulVec x i :=
        (le_div_iff₀ rises).1 ile
      linarith
    · linarith [feasible i, mul_nonpos_of_nonneg_of_nonpos positiveTime.le
        (le_of_not_gt rises)]
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro i active
      rw [mem_tightRows] at active ⊢
      rw [row_along, vanishing i (by simpa using active), mul_zero, add_zero, active]
    · intro equal
      apply notTight
      rw [equal, mem_tightRows, row_along]
      dsimp [time]
      rw [div_mul_cancel₀ _ slope.ne']
      ring

/-- There is a feasible point, with no larger objective, whose tight rows
annihilate only the zero direction. -/
theorem exists_tight_point (A : Matrix κ ι ℚ) (b : κ → ℚ)
    (bounded : Bounded A b) (objective : (ι → ℚ) →ₗ[ℚ] ℚ) {x : ι → ℚ}
    (feasible : Feasible A b x) :
    ∃ y, Feasible A b y ∧ objective y ≤ objective x ∧
      ∀ d : ι → ℚ, (∀ i ∈ tightRows A b y, A.mulVec d i = 0) → d = 0 := by
  classical
  let attainable :=
    (Finset.range (Fintype.card κ + 1)).filter fun k =>
      ∃ y, Feasible A b y ∧ objective y ≤ objective x ∧ (tightRows A b y).card = k
  have mem_attainable {y : ι → ℚ} (ok : Feasible A b y)
      (cost : objective y ≤ objective x) : (tightRows A b y).card ∈ attainable := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _)),
      y, ok, cost, rfl⟩
  have attainable_nonempty : attainable.Nonempty :=
    ⟨_, mem_attainable feasible le_rfl⟩
  obtain ⟨y, opt, cost, cardinality⟩ :=
    (Finset.mem_filter.mp (Finset.max'_mem attainable attainable_nonempty)).2
  refine ⟨y, opt, cost, ?_⟩
  have impossibleDirection (d : ι → ℚ) (vanishing : ∀ i ∈ tightRows A b y, A.mulVec d i = 0)
      (nonzero : d ≠ 0) (slopeNonpos : objective d ≤ 0) : False := by
    obtain ⟨t, positive, next, enlarged⟩ :=
      step_to_new_row A b bounded opt nonzero vanishing
    have newCost : objective (y + t • d) ≤ objective x := by
      rw [map_add, map_smul, smul_eq_mul]
      linarith [mul_nonpos_of_nonneg_of_nonpos positive.le slopeNonpos]
    have atMost := Finset.le_max' _ _ (mem_attainable next newCost)
    rw [← cardinality] at atMost
    exact (not_lt_of_ge atMost) (Finset.card_lt_card enlarged)
  intro d vanishing
  by_contra nonzero
  by_cases nonpos : objective d ≤ 0
  · exact impossibleDirection d vanishing nonzero nonpos
  · apply impossibleDirection (-d)
    · intro i active
      rw [Matrix.mulVec_neg, Pi.neg_apply, vanishing i active, neg_zero]
    · exact neg_ne_zero.mpr nonzero
    · rw [map_neg]
      exact neg_nonpos.mpr (le_of_not_ge nonpos)

end BoundedLinearProgram
end StochasticGames
