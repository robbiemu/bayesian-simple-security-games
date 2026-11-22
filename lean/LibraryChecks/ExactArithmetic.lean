module

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor

/-! Exact rational coefficients, their binary magnitudes, and evaluation over the reals. -/

example : let q := (-21 / 12 : ℚ)
          q.num = -7 ∧ q.den = 4 ∧ q.num.natAbs.size = 3 ∧ q.den.size = 3 := by
  decide +kernel

example : ⌈(7 / 3 : ℚ)⌉ = 3 := by norm_num

example (q : ℚ) (k : ℕ) : q.den.size ≤ k ↔ q.den < 2 ^ k :=
  Nat.size_le

example (a d s : ℚ) : ((a - d * s : ℚ) : ℝ) = (a : ℝ) - (d : ℝ) * (s : ℝ) := by
  norm_cast
