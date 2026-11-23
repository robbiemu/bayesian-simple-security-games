module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! ## The averaging circuit

The shifted comparison rounds preserve the sum and halve an upper bound on
the gap. The one-sided gate constraints bound every proposed trace above by
the actual circuit evaluation.
-/

public section

namespace StochasticGames
namespace ShiftedComparisons

/-- The upper and lower outputs of a comparator. -/
def sortPair (x y : ℚ) : ℚ × ℚ := (max x y, min x y)

/-- Shift the upper signal down and the lower signal up, then compare them. -/
def shiftAndSort (shift : ℚ) (values : ℚ × ℚ) : ℚ × ℚ :=
  sortPair (values.1 - shift) (values.2 + shift)

/-- The bound on the gap after a given number of rounds. -/
def gapBound (width : ℚ) : ℕ → ℚ
  | 0 => width
  | round + 1 => gapBound width round / 2

/-- Both outputs of the shared comparison circuit. -/
def evaluate (width x y : ℚ) : ℕ → ℚ × ℚ
  | 0 => sortPair x y
  | round + 1 =>
      shiftAndSort (gapBound width round / 4) (evaluate width x y round)

/-- The upper output is the approximation to the average. -/
def upperMean (width : ℚ) (rounds : ℕ) (x y : ℚ) : ℚ :=
  (evaluate width x y rounds).1

private theorem sortPair_sum (x y : ℚ) :
    (sortPair x y).1 + (sortPair x y).2 = x + y := by
  rcases le_total x y with h | h
  · simp [sortPair, max_eq_right h, min_eq_left h, add_comm]
  · simp [sortPair, max_eq_left h, min_eq_right h]

private theorem sortPair_gap (x y : ℚ) :
    (sortPair x y).1 - (sortPair x y).2 = |x - y| := by
  rcases le_total x y with h | h
  · simp only [sortPair, max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · simp [sortPair, max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]

private theorem sortPair_sorted (x y : ℚ) :
    (sortPair x y).2 ≤ (sortPair x y).1 :=
  (min_le_left x y).trans (le_max_left x y)

theorem shiftAndSort_mono (shift : ℚ) : Monotone (shiftAndSort shift) := by
  intro p q h
  have upper := sub_le_sub_right h.1 shift
  have lower := add_le_add h.2 (le_refl shift)
  exact ⟨max_le_max upper lower, min_le_min upper lower⟩

private theorem shiftAndSort_sum (shift : ℚ) (values : ℚ × ℚ) :
    (shiftAndSort shift values).1 + (shiftAndSort shift values).2 =
      values.1 + values.2 := by
  unfold shiftAndSort
  rw [sortPair_sum]
  ring

private theorem shiftAndSort_gap (shift : ℚ) (values : ℚ × ℚ) :
    (shiftAndSort shift values).1 - (shiftAndSort shift values).2 =
      |values.1 - values.2 - 2 * shift| := by
  unfold shiftAndSort
  rw [sortPair_gap]
  congr 1
  ring

theorem gapBound_eq (width : ℚ) (rounds : ℕ) :
    gapBound width rounds = width / (2 : ℚ) ^ rounds := by
  induction rounds with
  | zero => simp [gapBound]
  | succ round ih =>
      rw [gapBound, ih, pow_succ, div_div]

theorem evaluate_sorted (width x y : ℚ) (rounds : ℕ) :
    (evaluate width x y rounds).2 ≤ (evaluate width x y rounds).1 := by
  cases rounds with
  | zero => exact sortPair_sorted _ _
  | succ round => exact sortPair_sorted _ _

theorem evaluate_sum (width x y : ℚ) (rounds : ℕ) :
    (evaluate width x y rounds).1 + (evaluate width x y rounds).2 = x + y := by
  induction rounds with
  | zero => exact sortPair_sum x y
  | succ round ih => rw [evaluate, shiftAndSort_sum, ih]

theorem evaluate_gap {width x y : ℚ} (initialGap : |x - y| ≤ width) (rounds : ℕ) :
    (evaluate width x y rounds).1 - (evaluate width x y rounds).2 ≤
      gapBound width rounds := by
  induction rounds with
  | zero => simpa only [evaluate, gapBound, sortPair_gap] using initialGap
  | succ round ih =>
      rw [evaluate, gapBound, shiftAndSort_gap, abs_le]
      have sorted := evaluate_sorted width x y round
      constructor <;> linarith

theorem upperMean_bounds {width x y : ℚ} (initialGap : |x - y| ≤ width) (rounds : ℕ) :
    (x + y) / 2 ≤ upperMean width rounds x y ∧
      upperMean width rounds x y ≤ (x + y) / 2 + gapBound width rounds / 2 := by
  unfold upperMean
  have sum := evaluate_sum width x y rounds
  have sorted := evaluate_sorted width x y rounds
  have gap := evaluate_gap initialGap rounds
  constructor <;> linarith

/-- The constraints on a trace are upper bounds at the comparator outputs.
For a lower wire the bound by a minimum is two difference inequalities. -/
def ValidTrace (width x y : ℚ) (rounds : ℕ) (trace : Fin (rounds + 1) → ℚ × ℚ) : Prop :=
  trace 0 ≤ sortPair x y ∧
    ∀ j : Fin rounds,
      trace j.succ ≤
        shiftAndSort (gapBound width j.val / 4) (trace j.castSucc)

theorem trace_le_evaluation {width x y : ℚ} {rounds : ℕ}
    {trace : Fin (rounds + 1) → ℚ × ℚ} (valid : ValidTrace width x y rounds trace)
    (j : Fin (rounds + 1)) :
    trace j ≤ evaluate width x y j.val := by
  induction j using Fin.induction with
  | zero => exact valid.1
  | succ j ih =>
      exact (valid.2 j).trans (shiftAndSort_mono _ ih)

theorem evaluation_is_validTrace (width x y : ℚ) (rounds : ℕ) :
    ValidTrace width x y rounds (fun j => evaluate width x y j.val) := by
  constructor
  · exact le_rfl
  · intro j
    exact le_rfl

theorem trace_upper_bound_iff (width x y lower : ℚ) (rounds : ℕ) :
    (∃ trace : Fin (rounds + 1) → ℚ × ℚ,
      ValidTrace width x y rounds trace ∧ lower ≤ (trace (Fin.last rounds)).1) ↔
      lower ≤ upperMean width rounds x y := by
  constructor
  · rintro ⟨trace, valid, lowerLe⟩
    exact lowerLe.trans (trace_le_evaluation valid (Fin.last rounds)).1
  · intro lowerLe
    exact ⟨fun j => evaluate width x y j.val, evaluation_is_validTrace width x y rounds,
      lowerLe⟩

end ShiftedComparisons
end StochasticGames
