module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Exact recovery in compact strategies

Kintali's exact LP uses joint attack masses and a defender pressure
threshold. The public Formal Conjectures statement for arXiv:2610.08796
uses conditional attack distributions and pairwise coverage comparisons.
This module checks the conversion on tables indexed by finite types.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali

/-- Attacker costs are negatives of the payoffs. Only the defender's
gain from covering an attacked target enters her best-response condition. -/
structure Game (AttackType Target : Type*) where
  resources : ℕ
  prior : AttackType → ℚ
  intercept : AttackType → Target → ℚ
  slope : AttackType → Target → ℚ
  gain : Target → ℚ

namespace Game

variable {AttackType Target : Type*} [Fintype AttackType] [Fintype Target]
variable (g : Game AttackType Target)

def cost (i : AttackType) (j : Target) (x : ℚ) : ℚ :=
  g.intercept i j + g.slope i j * x

def pressure (joint : AttackType → Target → ℚ) (j : Target) : ℚ :=
  (∑ i, joint i j) * g.gain j

/-- The compact equilibrium predicate. Shape and length are built into
the finite index types. -/
structure IsBayesNash (x : Target → ℚ) (q : AttackType → Target → ℚ) : Prop where
  coverage_sum : (∑ j, x j) = g.resources
  coverage_bounds : ∀ j, 0 ≤ x j ∧ x j ≤ 1
  distribution : ∀ i, (∑ j, q i j) = 1 ∧ ∀ j, 0 ≤ q i j
  attacker : ∀ i j s, 0 < q i j → g.cost i j (x j) ≤ g.cost i s (x s)
  defender : ∀ j s, 0 < x j → x s < 1 →
    g.pressure (fun i t => g.prior i * q i t) s ≤
      g.pressure (fun i t => g.prior i * q i t) j

/-- The exact constraints delivered by a feasible marked pattern,
with a best-response reference also supplied for each zero-prior type. -/
structure ExactCertificate (x : Target → ℚ) (joint : AttackType → Target → ℚ)
    (reference : AttackType → Target) (threshold : ℚ) : Prop where
  coverage_sum : (∑ j, x j) = g.resources
  coverage_bounds : ∀ j, 0 ≤ x j ∧ x j ≤ 1
  mass_sum : ∀ i, (∑ j, joint i j) = g.prior i
  mass_nonneg : ∀ i j, 0 ≤ joint i j
  reference_min : ∀ i s, g.cost i (reference i) (x (reference i)) ≤ g.cost i s (x s)
  support_min : ∀ i j, 0 < joint i j →
    g.cost i j (x j) ≤ g.cost i (reference i) (x (reference i))
  pressure_upper : ∀ s, x s < 1 → g.pressure joint s ≤ threshold
  pressure_lower : ∀ j, 0 < x j → threshold ≤ g.pressure joint j

variable [DecidableEq Target]

/-- Normalize the joint rows with positive prior. A zero-prior row
chooses its reference target with probability one. -/
def conditional (joint : AttackType → Target → ℚ) (reference : AttackType → Target)
    (i : AttackType) (j : Target) : ℚ :=
  if g.prior i = 0 then (if j = reference i then 1 else 0) else joint i j / g.prior i

/-- A feasible exact certificate yields the compact Bayes–Nash
conditions, including a best response for each zero-prior type. -/
theorem certificate_isBayesNash
    {x : Target → ℚ} {joint : AttackType → Target → ℚ}
    {reference : AttackType → Target} {threshold : ℚ}
    (h : g.ExactCertificate x joint reference threshold) :
    g.IsBayesNash x (g.conditional joint reference) := by
  have hPrior (i : AttackType) : 0 ≤ g.prior i := by
    rw [← h.mass_sum i]
    exact Finset.sum_nonneg (fun j _ => h.mass_nonneg i j)
  have hRecover (i : AttackType) (j : Target) :
      g.prior i * g.conditional joint reference i j = joint i j := by
    by_cases hz : g.prior i = 0
    · have hjoint : joint i j = 0 := le_antisymm
        ((Finset.single_le_sum (f := joint i)
          (fun j _ => h.mass_nonneg i j) (Finset.mem_univ j)).trans_eq ((h.mass_sum i).trans hz))
        (h.mass_nonneg i j)
      simp [hz, hjoint]
    · simp only [conditional, ite_eq_right hz]
      field_simp
  refine ⟨h.coverage_sum, h.coverage_bounds, ?_, ?_, ?_⟩
  · intro i
    by_cases hz : g.prior i = 0
    · simp [conditional, hz]
      intro j
      split <;> norm_num
    · have hp : 0 < g.prior i := lt_of_le_of_ne (hPrior i) (Ne.symm hz)
      simp only [conditional, ite_eq_right hz]
      constructor
      · simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, h.mass_sum i, ← div_eq_mul_inv, div_self hz]
      · exact fun j => div_nonneg (h.mass_nonneg i j) hp.le
  · intro i j s hPos
    by_cases hz : g.prior i = 0
    · have hRef : j = reference i := by
        by_contra hne
        simp [conditional, hz, hne] at hPos
      simpa [hRef] using h.reference_min i s
    · have hp : 0 < g.prior i := lt_of_le_of_ne (hPrior i) (Ne.symm hz)
      have hjoint : 0 < joint i j := hRecover i j ▸ mul_pos hp hPos
      exact (h.support_min i j hjoint).trans (h.reference_min i s)
  · intro j s hj hs
    simpa only [pressure, hRecover] using (h.pressure_upper s hs).trans (h.pressure_lower j hj)

end Game
end Kintali
