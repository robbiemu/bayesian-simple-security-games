module

public import StochasticGames.ReachabilitySemantics
public import StochasticGames.ThresholdCompiler
public import StochasticGames.TrivialThreshold
import StochasticGames.RealCompilation
import all StochasticGames.ThresholdCompiler
import all StochasticGames.ThresholdInput
import all StochasticGames.ArenaEncoding

/-! # Simple stochastic reachability reduces to deterministic mean payoff

Test the strict failure of the source threshold in the intermediate game.
The final change of owners and weights reverses this test, including equality.
-/

@[expose] public section
namespace StochasticGames.ThresholdReduction

open ArenaEncoding MeanPayoff ThresholdCompiler TrivialThreshold

variable {n : ℕ} (input : ThresholdInput n)

/-- Output the one deterministic arena whose sign answers the source threshold. -/
def compile : Table :=
  if input.numerator ≤ 0 then loop true
  else if (input.denominator : ℤ) < input.numerator then loop false
  else match input.start with
    | .inr terminal => loop terminal
    | .inl s => ThresholdCompiler.table input s

theorem compile_valid : (compile input).Valid := by
  unfold compile
  split
  · exact loop_valid _
  split
  · exact loop_valid _
  cases input.start with
  | inr b => exact loop_valid b
  | inl s => exact (ThresholdCompiler.table_represents input s).valid

private theorem intermediate_tests_strict_failure (s : Fin n) (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) :
    (Source.value input.rows.get (.inl s) : ℝ) < (input.threshold : ℝ) ↔
      (intermediate input s).Nonnegative none := by
  calc
    _ ↔ ∃ y, Source.DualFeasible input.rows.get y ∧ 1 - (input.threshold : ℝ) < y s :=
      Source.value_lt_iff_dualFeasible _ _ _
    _ ↔ ∃ y : Fin n → ℝ, SourceRows.Exact (system input s) y :=
      (SourcePrecision.strict_witness_iff input.rows.get s input.threshold input.denominator
        input.denominator_pos input.clears_threshold).trans
        (SourcePrecision.tightened_real_iff_rational input.rows.get s input.threshold input.denominator
          input.denominator_pos input.clears_threshold).symm
    _ ↔ ∃ v : Variables input s → ℝ, AtomEncoding.RowsHold (weightedRows input s) v :=
      RealCompilation.real_exact_iff_compiled input s
    _ ↔ ∃ h, IntegerAtoms.RowsHold (integerRows input s) h :=
      RealCompilation.real_compiled_iff_integer input s positive atMostOne
    _ ↔ (intermediate input s).Certificate none :=
      integer_rows_iff_certificate input s
    _ ↔ (intermediate input s).Nonnegative none :=
      ((intermediate input s).nonnegative_iff_certificate none).symm

private theorem nonterminal_correct (s : Fin n) (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) :
    (input.threshold : ℝ) ≤ (Source.value input.rows.get (.inl s) : ℝ) ↔
      (ThresholdCompiler.table input s).Nonnegative := by
  calc
    _ ↔ ¬ ((Source.value input.rows.get (.inl s) : ℝ) < (input.threshold : ℝ)) := not_lt.symm
    _ ↔ ¬ (intermediate input s).Nonnegative none :=
      not_congr (intermediate_tests_strict_failure input s positive atMostOne)
    _ ↔ (final input s).Nonnegative none :=
      ((intermediate input s).swap_nonnegative_iff none).symm
    _ ↔ (ThresholdCompiler.table input s).Nonnegative :=
      (ThresholdCompiler.table_represents input s).nonnegative_iff.symm

/-- The emitted graph has nonnegative mean-payoff value exactly when the
source reachability value meets the given rational threshold. -/
theorem compile_correct :
    (input.threshold : ℝ) ≤ (Source.value input.rows.get input.start : ℝ) ↔
      (compile input).Nonnegative := by
  unfold compile
  split
  · rename_i nonpositive
    rw [loop_nonnegative_iff]
    have threshold_le : (input.threshold : ℝ) ≤ 0 := by
      exact_mod_cast (input.threshold_nonpos_iff.mpr nonpositive)
    exact iff_of_true (threshold_le.trans (Source.value input.rows.get input.start).property.1) rfl
  · rename_i positive
    split
    · rename_i tooHigh
      rw [loop_nonnegative_iff, Bool.false_eq_true, iff_false]
      have threshold_gt : (1 : ℝ) < (input.threshold : ℝ) := by
        exact_mod_cast (input.one_lt_threshold_iff.mpr tooHigh)
      exact not_le_of_gt ((Source.value input.rows.get input.start).property.2.trans_lt threshold_gt)
    · rename_i notTooHigh
      have atMostOne : input.threshold ≤ 1 :=
        le_of_not_gt fun h => notTooHigh (input.one_lt_threshold_iff.mp h)
      have aboveZero : 0 < input.threshold :=
        lt_of_not_ge fun h => positive (input.threshold_nonpos_iff.mp h)
      cases input.start with
      | inl s => exact nonterminal_correct input s (lt_of_not_ge positive) atMostOne
      | inr terminal =>
        rw [loop_nonnegative_iff]
        cases terminal
        · simp only [Source.value_lose, Bool.false_eq_true, iff_false]
          exact not_le_of_gt (by exact_mod_cast aboveZero : (0 : ℝ) < (input.threshold : ℝ))
        · simp only [Source.value_win, iff_true]
          have le : (input.threshold : ℝ) ≤ (1 : ℝ) := by exact_mod_cast atMostOne
          exact le

end StochasticGames.ThresholdReduction
