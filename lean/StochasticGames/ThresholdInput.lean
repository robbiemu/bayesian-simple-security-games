module

public import StochasticGames.SourceGame
public import StochasticGames.Precision
import all StochasticGames.Precision
import Mathlib.Tactic.Linarith

/-! # Explicit threshold instances

A vertex table and two binary integers represent the input. The denominator
can be used as written, even when the printed fraction is not reduced.
-/

@[expose] public section

namespace StochasticGames

structure ThresholdInput (n : ℕ) where
  rows : Vector (Source.Row (Fin n)) n
  start : Source.Position (Fin n)
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator

namespace ThresholdInput

variable {n : ℕ} (input : ThresholdInput n)

def threshold : ℚ := (input.numerator : ℚ) / (input.denominator : ℚ)

theorem clears_threshold : Precision.Clears input.denominator input.threshold := by
  refine ⟨input.numerator, ?_⟩
  have nonzero : (input.denominator : ℚ) ≠ 0 := by exact_mod_cast input.denominator_pos.ne'
  rw [threshold, mul_comm, div_mul_cancel₀ _ nonzero]

theorem threshold_nonpos_iff : input.threshold ≤ 0 ↔ input.numerator ≤ 0 := by
  have positive : (0 : ℚ) < input.denominator := by exact_mod_cast input.denominator_pos
  rw [threshold, div_le_iff₀ positive, zero_mul, Int.cast_nonpos]

theorem one_lt_threshold_iff : 1 < input.threshold ↔ (input.denominator : ℤ) < input.numerator := by
  have positive : (0 : ℚ) < input.denominator := by exact_mod_cast input.denominator_pos
  rw [threshold, lt_div_iff₀ positive, one_mul, ← Int.cast_natCast, Int.cast_lt]

theorem threshold_ge_reciprocal (positive : 0 < input.numerator) :
    1 / (input.denominator : ℚ) ≤ input.threshold := by
  unfold threshold
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (by omega : (1 : ℤ) ≤ input.numerator)

end ThresholdInput
end StochasticGames
