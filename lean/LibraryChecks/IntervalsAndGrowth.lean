module

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Interval.Set.Infinite

/-! Finite exclusions from an open interval, integer logarithms, and analytic estimates. -/

open Asymptotics Filter

example {a b : ℝ} (hab : a < b) (ends : Finset ℝ) :
    ∃ x ∈ Set.Ioo a b, x ∉ ends :=
  (Set.Ioo_infinite hab).exists_notMem_finset ends

example {k m : ℕ} (f : Fin k → Fin m) (hf : Function.Injective f) : k ≤ m := by
  simpa using Fintype.card_le_of_injective f hf

example (n : ℕ) : ⌊Real.logb 2 n⌋₊ = n.log2 := by
  simpa [Nat.log2_eq_log_two] using Real.natFloor_logb_natCast 2 n

example {r : ℝ} (hr : 0 < r) : Real.log =o[atTop] (fun x : ℝ ↦ x ^ r) :=
  isLittleO_log_rpow_atTop hr

example {x : ℝ} (hx : |x| < 1) :
    |x + Real.log (1 - x)| ≤ |x| ^ 2 / (1 - |x|) := by
  simpa using Real.abs_log_sub_add_sum_range_le hx 1
