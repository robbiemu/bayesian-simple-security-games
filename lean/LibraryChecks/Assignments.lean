module

import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Finite assignment scores, the row convention for permutation matrices, and Birkhoff weights. -/

variable {n : ℕ}

example (score : Equiv.Perm (Fin n) → ℚ) : ∃ π, ∀ ρ, score ρ ≤ score π := by
  simpa using Finset.univ.exists_max_image score Finset.univ_nonempty

example (π : Equiv.Perm (Fin n)) (i : Fin n) : π.cycleOf i i = π i :=
  π.cycleOf_apply_self i

example (π : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : ∑ i, x (π i) = ∑ i, x i :=
  Equiv.sum_comp π x

-- Row i has its unit entry in column π i.
example (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    π.permMatrix ℚ i j = if π i = j then 1 else 0 := by
  simp [Equiv.toPEquiv_apply]

-- An explicit two-by-two decomposition with rational coefficients.
example : (1 / 3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) +
    (2 / 3 : ℚ) • (Equiv.swap (0 : Fin 2) 1).permMatrix ℚ = !![1/3, 2/3; 2/3, 1/3] := by
  decide +kernel

example (A : Matrix (Fin n) (Fin n) ℝ) (h₀ : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ π, 0 ≤ w π) ∧ ∑ π, w π = 1 ∧
      ∑ π, w π • π.permMatrix ℝ = A :=
  exists_eq_sum_perm_of_mem_doublyStochastic (mem_doublyStochastic_iff_sum.mpr ⟨h₀, hrow, hcol⟩)
