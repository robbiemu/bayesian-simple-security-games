module

public import StochasticGames.ShiftedComparisons
import Mathlib.Tactic.NormNum

/-! ## Eliminate averages using a uniform branch gap

The compiled rows constrain auxiliary wires only from above. A compiled
solution therefore satisfies a branch of the original system with small
common slack. The branch gap then supplies a possibly different exact
solution.
-/

public section

namespace StochasticGames
namespace AverageFeasibility

open ShiftedComparisons

variable {ι : Type*}

structure Term (ι : Type*) where
  index : Option ι
  offset : ℚ

def Term.value (a : Term ι) (x : ι → ℚ) : ℚ :=
  (a.index.elim 0 x) + a.offset

structure DifferenceRow (ι : Type*) where
  lhs : Term ι
  rhs : Term ι

structure MaxRow (ι : Type*) where
  lhs : Term ι
  terms : List (Term ι)

structure AverageRow (ι : Type*) where
  lhs : Term ι
  first : Term ι
  second : Term ι

structure System (ι : Type*) where
  differences : List (DifferenceRow ι)
  maxima : List (MaxRow ι)
  averages : List (AverageRow ι)

namespace System

variable (system : System ι)

def HardRows (x : ι → ℚ) : Prop :=
  ∀ row ∈ system.differences, row.lhs.value x ≤ row.rhs.value x

def MaxRows (x : ι → ℚ) : Prop :=
  ∀ row ∈ system.maxima, ∃ term ∈ row.terms, row.lhs.value x ≤ term.value x

def AverageRows (x : ι → ℚ) (slack : ℚ) : Prop :=
  ∀ row ∈ system.averages,
    row.lhs.value x ≤ (row.first.value x + row.second.value x) / 2 + slack

def Exact (x : ι → ℚ) : Prop :=
  system.HardRows x ∧ system.MaxRows x ∧ system.AverageRows x 0

abbrev Branch :=
  (row : {r // r ∈ system.maxima}) → {term // term ∈ row.val.terms}

def Relaxed (branch : system.Branch) (x : ι → ℚ) (slack : ℚ) : Prop :=
  system.HardRows x ∧
    (∀ row : {r // r ∈ system.maxima}, row.val.lhs.value x ≤ (branch row).val.value x) ∧
    system.AverageRows x slack

def InputsBounded (width : ℚ) : Prop :=
  ∀ x, system.HardRows x → ∀ row ∈ system.averages,
    |row.first.value x - row.second.value x| ≤ width

/-- A uniform slack below the positive gap can be removed within the selected branch. -/
def HasGap (gap : ℚ) : Prop :=
  ∀ (branch : system.Branch) (slack : ℚ), 0 ≤ slack → slack < gap →
    (∃ x, system.Relaxed branch x slack) → ∃ y, system.Relaxed branch y 0

def Compiled (width : ℚ) (rounds : ℕ) (x : ι → ℚ) : Prop :=
  system.HardRows x ∧ system.MaxRows x ∧
    ∀ row ∈ system.averages,
      ∃ trace : Fin (rounds + 1) → ℚ × ℚ,
        ValidTrace width (row.first.value x) (row.second.value x) rounds trace ∧
        row.lhs.value x ≤ (trace (Fin.last rounds)).1

theorem exact_to_compiled {width : ℚ} (bounded : system.InputsBounded width) (rounds : ℕ)
    {x : ι → ℚ} (exactRows : system.Exact x) : system.Compiled width rounds x := by
  obtain ⟨hard, maxima, averages⟩ := exactRows
  refine ⟨hard, maxima, ?_⟩
  intro row rowMem
  apply (trace_upper_bound_iff _ _ _ _ _).2
  have source := averages row rowMem
  rw [add_zero] at source
  exact source.trans (upperMean_bounds (bounded x hard row rowMem) rounds).1

theorem compiled_to_branch {width : ℚ} (bounded : system.InputsBounded width) (rounds : ℕ)
    {x : ι → ℚ} (compiled : system.Compiled width rounds x) :
    ∃ branch : system.Branch, system.Relaxed branch x (gapBound width rounds / 2) := by
  obtain ⟨hard, maxima, averages⟩ := compiled
  let branch : system.Branch := fun row =>
    ⟨Classical.choose (maxima row.val row.property),
      (Classical.choose_spec (maxima row.val row.property)).1⟩
  refine ⟨branch, hard, ?_, ?_⟩
  · intro row
    exact (Classical.choose_spec (maxima row.val row.property)).2
  · intro row rowMem
    have upper := (trace_upper_bound_iff _ _ _ _ _).1 (averages row rowMem)
    exact upper.trans (upperMean_bounds (bounded x hard row rowMem) rounds).2

theorem zero_slack_is_exact {branch : system.Branch} {x : ι → ℚ}
    (proof : system.Relaxed branch x 0) : system.Exact x := by
  obtain ⟨hard, chosen, averages⟩ := proof
  refine ⟨hard, ?_, averages⟩
  intro row rowMem
  exact ⟨(branch ⟨row, rowMem⟩).val, (branch ⟨row, rowMem⟩).property,
    chosen ⟨row, rowMem⟩⟩

/-- The one-sided compilation preserves exact decisions when its error is
smaller than the uniform gap for the selected linear systems. -/
theorem exact_feasible_iff_compiled {width gap : ℚ}
    (widthNonneg : 0 ≤ width) (bounded : system.InputsBounded width)
    (uniformGap : system.HasGap gap) (rounds : ℕ)
    (precision : gapBound width rounds / 2 < gap) :
    (∃ x, system.Exact x) ↔ ∃ x, system.Compiled width rounds x := by
  constructor
  · rintro ⟨x, exactRows⟩
    exact ⟨x, system.exact_to_compiled bounded rounds exactRows⟩
  · rintro ⟨x, compiled⟩
    obtain ⟨branch, relaxed⟩ := system.compiled_to_branch bounded rounds compiled
    have nonneg : 0 ≤ gapBound width rounds / 2 := by
      rw [gapBound_eq]
      exact div_nonneg (div_nonneg widthNonneg (pow_nonneg (by norm_num) _)) (by norm_num)
    obtain ⟨y, repaired⟩ := uniformGap branch _ nonneg precision ⟨x, relaxed⟩
    exact ⟨y, system.zero_slack_is_exact repaired⟩

end System
end AverageFeasibility
end StochasticGames
