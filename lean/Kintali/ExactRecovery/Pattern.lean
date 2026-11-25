module

public import Kintali.Equilibrium
public import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-!
# Rational marked patterns

Sections 1 and 3 of Shiva Kintali's short proof use one common residual for
the two families of cost comparisons and for the pressure comparisons.
Coverage, budget, row sums and unmarked flows are exact at every residual.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery

inductive Status where
  | lower | upper | balanced
  deriving DecidableEq, Repr

/-- The reference is always a marked target of its type. -/
structure Pattern (I J : Type*) where
  reference : I → J
  marked : I → J → Bool
  reference_marked : ∀ i, marked i (reference i) = true
  status : J → Status

variable {I J : Type*} [Fintype I] [Fintype J]
variable {g : Game I J} {p : Pattern I J}

/-- The system of Section 1, including both one-sided rows for each
balanced target. At residual zero these rows give a pressure equality. -/
structure Relaxed (g : Game I J) (p : Pattern I J) (x : J → ℚ)
    (q : I → J → ℚ) (threshold residual : ℚ) : Prop where
  coverage_bounds : ∀ j, 0 ≤ x j ∧ x j ≤ 1
  budget : ∑ j, x j = g.resources
  nonneg : ∀ i j, 0 ≤ q i j
  row_sum : ∀ i, ∑ j, q i j = g.prior i
  unmarked : ∀ i j, p.marked i j = false → q i j = 0
  threshold_nonneg : 0 ≤ threshold
  residual_bounds : 0 ≤ residual ∧ residual ≤ 1
  reference_le : ∀ i j, g.cost i (p.reference i) (x (p.reference i)) ≤
    g.cost i j (x j) + residual
  marked_le : ∀ i j, p.marked i j = true →
    g.cost i j (x j) ≤ g.cost i (p.reference i) (x (p.reference i)) + residual
  lower_coverage : ∀ j, p.status j = .lower → x j = 0
  upper_coverage : ∀ j, p.status j = .upper → x j = 1
  pressure_le : ∀ j, p.status j ≠ .upper → g.pressure q j ≤ threshold + residual
  pressure_ge : ∀ j, p.status j ≠ .lower → threshold ≤ g.pressure q j + residual

/-- The LP output gives the existing compact certificate, including when a
balanced target reaches a coverage endpoint. -/
theorem exactCertificate {x : J → ℚ} {q : I → J → ℚ} {t : ℚ}
    (h : Relaxed g p x q t 0) : g.ExactCertificate x q p.reference t := by
  refine ⟨h.budget, h.coverage_bounds, h.row_sum, h.nonneg, ?_, ?_, ?_, ?_⟩
  · simpa using h.reference_le
  · intro i j hq
    have marked : p.marked i j = true := by
      cases hm : p.marked i j with
      | true => rfl
      | false => exact (hq.ne' (h.unmarked i j hm)).elim
    simpa using h.marked_le i j marked
  · intro j hj
    have hs : p.status j ≠ .upper := fun he => hj.ne (h.upper_coverage j he)
    simpa using h.pressure_le j hs
  · intro j hj
    have hs : p.status j ≠ .lower := fun he => hj.ne' (h.lower_coverage j he)
    simpa using h.pressure_ge j hs

/-- The contact's status includes every endpoint explicitly. -/
def statusAt (x : ℚ) : Status :=
  if x = 0 then .lower else if x = 1 then .upper else .balanced

/-- Section 3 marks all targets within η of the reference, including targets
on which the eventual witness might have zero flow. -/
def contactPattern (g : Game I J) (x : J → ℚ) (reference : I → J)
    (η : ℚ) (hη : 0 ≤ η) : Pattern I J where
  reference := reference
  marked i j := decide (g.cost i j (x j) ≤ g.cost i (reference i) (x (reference i)) + η)
  reference_marked i := by simp [hη]
  status j := statusAt (x j)

end Kintali.ExactRecovery
