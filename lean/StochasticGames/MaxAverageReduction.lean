module

public import StochasticGames.BranchLinearization
public import StochasticGames.LinearFeasibilityGap
public import StochasticGames.Precision
import all StochasticGames.AverageFeasibility
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import all StochasticGames.Precision
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Exact elimination of bounded averages

Clear the right-hand sides of all possible branch matrices with the same
scale. Bound their determinants using the small integer row coefficients.
Compile the averages to the precision given by this gap.
-/

public section

namespace StochasticGames.MaxAverageReduction

open AverageFeasibility BranchLinearization LinearFeasibilityGap Precision

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- List the input offsets once, before making any selection of max terms. -/
def offsets (system : System ι) : List ℚ :=
  (system.differences.flatMap fun row => [row.lhs.offset, row.rhs.offset]) ++
    (system.maxima.flatMap fun row => row.lhs.offset :: row.terms.map Term.offset) ++
    (system.averages.flatMap fun row => [row.lhs.offset, row.first.offset, row.second.offset])

omit [Fintype ι] in
theorem clears_branch_rhs (system : System ι) (branch : system.Branch) (i : Rows system) :
    Clears (denominator (offsets system)) (rhs system branch i) := by
  have differenceCleared (r : DifferenceRow ι) (hr : r ∈ system.differences) :
      Clears (denominator (offsets system)) (r.rhs.offset - r.lhs.offset) := by
    apply Clears.sub <;> apply denominator_clears <;>
      simp only [offsets, List.mem_append, List.mem_flatMap] <;>
      exact Or.inl (Or.inl ⟨r, hr, by simp⟩)
  have maximumCleared (r : {r // r ∈ system.maxima}) :
      Clears (denominator (offsets system)) ((branch r).val.offset - r.val.lhs.offset) := by
    apply Clears.sub <;> apply denominator_clears <;>
      simp only [offsets, List.mem_append, List.mem_flatMap]
    · exact Or.inl (Or.inr ⟨r.val, r.property,
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(branch r).val, (branch r).property, rfl⟩)⟩)
    · exact Or.inl (Or.inr ⟨r.val, r.property, List.mem_cons_self⟩)
  have averageCleared (r : AverageRow ι) (hr : r ∈ system.averages)
      {c : ℚ} (hc : c ∈ [r.lhs.offset, r.first.offset, r.second.offset]) :
      Clears (denominator (offsets system)) c := by
    apply denominator_clears
    simp only [offsets, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨r, hr, hc⟩
  rcases i with i | i | i | upper
  · exact differenceCleared _ (List.get_mem _ i)
  · exact maximumCleared (atPosition system.maxima i)
  · let r := system.averages.get i
    have member : r ∈ system.averages := List.get_mem _ i
    have first := averageCleared r member (show r.first.offset ∈ _ by simp)
    have second := averageCleared r member (show r.second.offset ∈ _ by simp)
    have lhs := averageCleared r member (show r.lhs.offset ∈ _ by simp)
    change Clears (denominator (offsets system))
      (r.first.offset + r.second.offset - 2 * r.lhs.offset)
    rw [two_mul]
    exact (first.add second).sub (lhs.add lhs)
  · cases upper
    · exact Clears.zero _
    · exact Clears.one _

def gap (system : System ι) : ℚ :=
  1 / ((denominator (offsets system) : ℚ) * determinantBound (Option ι) 2)

omit [DecidableEq ι] in
private theorem one_le_gap_divisor (system : System ι) :
    1 ≤ (denominator (offsets system) : ℚ) * determinantBound (Option ι) 2 := by
  have D : (1 : ℚ) ≤ (denominator (offsets system) : ℚ) := by
    exact_mod_cast denominator_pos (offsets system)
  have factorial : (1 : ℚ) ≤ (Fintype.card (Option ι)).factorial := by
    exact_mod_cast Nat.factorial_pos (Fintype.card (Option ι))
  unfold determinantBound
  exact one_le_mul_of_one_le_of_one_le D
    (one_le_mul_of_one_le_of_one_le factorial (one_le_pow₀ (by norm_num)))

omit [DecidableEq ι] in
theorem gap_pos (system : System ι) : 0 < gap system :=
  one_div_pos.mpr (zero_lt_one.trans_le (one_le_gap_divisor system))

/-- Row coefficient bounds and one scale give the same gap for every max branch. -/
theorem uniform_gap (system : System ι)
    (bounded : ∃ B : ℚ, ∀ x, system.HardRows x → ∀ i, |x i| ≤ B) :
    system.HasGap (gap system) := by
  intro branch slack slackNonneg smallSlack possible
  obtain ⟨x, relaxed⟩ := possible
  let A := matrix system branch
  let D := denominator (offsets system)
  let b : Rows system → ℤ := fun i => Classical.choose (clears_branch_rhs system branch i)
  have Dpos : (0 : ℚ) < (D : ℚ) := by
    exact_mod_cast denominator_pos (offsets system)
  have rhsEq : rationalRhs b (D : ℚ) = rhs system branch := by
    funext i
    change (b i : ℚ) / (D : ℚ) = _
    apply (div_eq_iff Dpos.ne').2
    simpa only [b, D, mul_comm] using (Classical.choose_spec (clears_branch_rhs system branch i)).symm
  have branchRows (y : Option ι → ℚ) :
      BoundedLinearProgram.Feasible (rationalMatrix A) (rationalRhs b (D : ℚ)) y ↔
        system.Relaxed branch (fun i => y (some i)) (y none) ∧ 0 ≤ y none ∧ y none ≤ 1 := by
    rw [rhsEq]
    exact feasible_iff system branch y
  have boundedMatrix : BoundedLinearProgram.Bounded (rationalMatrix A) (rationalRhs b (D : ℚ)) := by
    obtain ⟨B, sourceBound⟩ := bounded
    refine ⟨max B 1, fun y feasible i => ?_⟩
    obtain ⟨⟨hard, _, _⟩, lower, upper⟩ := (branchRows y).1 feasible
    cases i with
    | none => exact ((abs_of_nonneg lower).symm ▸ upper).trans (le_max_right _ _)
    | some i => exact (sourceBound _ hard i).trans (le_max_left _ _)
  have slackLeOne : slack ≤ 1 := by
    apply smallSlack.le.trans
    unfold gap
    apply (div_le_iff₀ (zero_lt_one.trans_le (one_le_gap_divisor system))).2
    simpa only [one_mul] using one_le_gap_divisor system
  let y : Option ι → ℚ := fun i => i.elim slack x
  have feasibleY : BoundedLinearProgram.Feasible (rationalMatrix A) (rationalRhs b (D : ℚ)) y :=
    (branchRows y).2 ⟨relaxed, slackNonneg, slackLeOne⟩
  obtain ⟨z, feasibleZ, zeroSlack⟩ := exists_zero_slack A b (D : ℚ) 2 Dpos
    (by norm_num) (entry_bound system branch) boundedMatrix none
    (fun z feasibleZ => ((branchRows z).1 feasibleZ).2.1) feasibleY smallSlack
  exact ⟨fun i => z (some i), zeroSlack ▸ ((branchRows z).1 feasibleZ).1⟩

/-- A bounded max-average system and its one-sided comparison circuit have
exactly the same feasibility answer at the input-computable precision. -/
theorem exact_compilation (system : System ι) {width : ℚ}
    (widthNonneg : 0 ≤ width) (inputWidths : system.InputsBounded width)
    (bounded : ∃ B : ℚ, ∀ x, system.HardRows x → ∀ i, |x i| ≤ B) :
    (∃ x, system.Exact x) ↔ ∃ x, system.Compiled width (rounds width (gap system)) x :=
  system.exact_feasible_iff_compiled widthNonneg inputWidths (uniform_gap system bounded) _
    (error_lt_gap widthNonneg (gap_pos system))

end StochasticGames.MaxAverageReduction
