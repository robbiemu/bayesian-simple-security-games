module

import Mathlib.Analysis.Convex.Combination
import Mathlib.Basic.Real.Basic
import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-! Probability weights, their convex combinations, and zero sums of nonnegative terms. -/

open Convexity

variable {n : ℕ}

example (p : StdSimplex ℝ (Fin n)) (b : ℝ) : ∑ i, b * p.weights i = b := by
  rw [← Finset.mul_sum, p.total_of_fintype, mul_one]

example (p : StdSimplex ℝ (Fin n)) (x : Fin n → ℝ) :
    (∑ i, p.weights i • x i) ∈ convexHull ℝ (Set.range x) :=
  (convex_convexHull ℝ _).sum_mem (fun i _ ↦ p.weights_nonneg i) p.total_of_fintype
    (fun i _ ↦ subset_convexHull ℝ _ (Set.mem_range_self i))

example (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i = 0) (j : Fin n) :
    f j = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hf i)).mp hsum j (Finset.mem_univ j)

example (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (r : ℝ) : Convex ℝ {x | f x ≤ r} :=
  convex_halfSpace_le f.isLinear r
