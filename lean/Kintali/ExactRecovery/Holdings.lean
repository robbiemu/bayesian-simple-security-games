module

public import Kintali.ExactRecovery.Grid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Acceptance and the physical coverage

The elementary private buyer in gap k ranks above quotes z ≤ k and below
quotes z > k. Its remaining endowment is its outside holding. A vacancy or a
lower-ranked positive holding would block an unfilled private buyer. Real
bids strictly above physical coverage displace a positive private holding.
These arguments use the expanded grid and hold in every restriction.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery

structure Holdings (I J : Type*) (G : ℕ) where
  real : I → J → Quote G → ℚ
  outside : I → ℚ
  privateBuy : J → Fin G → ℚ
  vacancy : J → ℚ

namespace Holdings

variable {I J : Type*} {G : ℕ}

def privateTotal (a : Holdings I J G) (j : J) : ℚ := ∑ k, a.privateBuy j k

def physical (a : Holdings I J G) (g : Game I J) (σ : ℚ) (j : J) : ℚ :=
  if 0 < g.gain j then 1 - a.privateTotal j / σ else 0

/-- The site's strictly worse holdings for its private bid in gap k. -/
def privateBlock (a : Holdings I J G) (σ : ℚ) (j : J) (k : Fin G) : Prop :=
  a.privateBuy j k < σ / G ∧
    (0 < a.vacancy j ∨ (∃ i z, z.val ≤ k.val ∧ 0 < a.real i j z) ∨
      (∃ h, h.val < k.val ∧ 0 < a.privateBuy j h))

/-- A sufficient reason for a site to accept a real quote, independent of
buyer tie ranks at that quote. -/
def siteAccepts (a : Holdings I J G) (j : J) (z : Quote G) : Prop :=
  0 < a.vacancy j ∨ ∃ k, k.val < z.val ∧ 0 < a.privateBuy j k

def quoteCost (g : Game I J) (i : I) (j : J) (z : Quote G) : ℚ := g.cost i j (price z)

/-- The endpoint used to price the outside record. -/
def endpoint (g : Game I J) (j : J) : ℚ := if 0 < g.gain j then 1 else 0

def outsideCost (g : Game I J) (redirect : I → J) (i : I) : ℚ :=
  g.cost i (redirect i) (endpoint g (redirect i))

def Eligible (g : Game I J) (redirect : I → J) (i : I) (j : J) (z : Quote G) : Prop :=
  0 < g.gain j ∧ quoteCost g i j z ≤ outsideCost g redirect i

/-- Either the real buyer has outside balance, which ranks last even on a
cost tie, or the buyer holds a strictly dearer real quote. -/
def buyerAccepts (a : Holdings I J G) (g : Game I J) (i : I) (j : J) (z : Quote G) : Prop :=
  0 < a.outside i ∨ ∃ k w, 0 < a.real i k w ∧ quoteCost g i j z < quoteCost g i k w

/-- This blocking configuration suffices for the cost comparisons. Full
ordinal stability also excludes improvements relying on same-cost tie ranks. -/
def costBlock (a : Holdings I J G) (g : Game I J) (i : I) (j : J) (z : Quote G) : Prop :=
  a.buyerAccepts g i j z ∧ a.siteAccepts j z

variable [Fintype I] [Fintype J]

def realTotal (a : Holdings I J G) (j : J) : ℚ := ∑ i, ∑ z, a.real i j z

/-- Balances and retained private stability at contact. An expanded stable
allocation supplies these facts even when optional real bids were omitted. -/
structure Contact (a : Holdings I J G) (g : Game I J) (redirect : I → J) (σ t : ℚ) : Prop where
  grid_pos : 0 < G
  sigma_pos : 0 < σ
  pressure_nonneg : 0 ≤ t
  real_nonneg : ∀ i j z, 0 ≤ a.real i j z
  outside_nonneg : ∀ i, 0 ≤ a.outside i
  private_bounds : ∀ j k, 0 ≤ a.privateBuy j k ∧ a.privateBuy j k ≤ σ / G
  vacancy_nonneg : ∀ j, 0 ≤ a.vacancy j
  buyer_balance : ∀ i, (∑ j, ∑ z, a.real i j z) + a.outside i = g.prior i
  site_balance : ∀ j, 0 < g.gain j →
    a.realTotal j + a.privateTotal j + a.vacancy j = t / g.gain j
  eligible_purchase : ∀ i j z, 0 < a.real i j z → Eligible g redirect i j z
  outside_min : ∀ i j, outsideCost g redirect i ≤ g.cost i j (endpoint g j)
  private_stable : ∀ j, 0 < g.gain j → ∀ k, ¬a.privateBlock σ j k
  budget : (∑ j, a.physical g σ j) = g.resources

variable {a : Holdings I J G} {g : Game I J} {redirect : I → J} {σ t : ℚ}
variable (h : a.Contact g redirect σ t)
include h

theorem privateTotal_bounds (j : J) : 0 ≤ a.privateTotal j ∧ a.privateTotal j ≤ σ := by
  refine ⟨Finset.sum_nonneg (fun k _ => (h.private_bounds j k).1), ?_⟩
  exact (Finset.sum_le_sum (fun k _ => (h.private_bounds j k).2)).trans_eq
    (gap_mass h.grid_pos σ)

theorem physical_bounds (j : J) : 0 ≤ a.physical g σ j ∧ a.physical g σ j ≤ 1 := by
  by_cases site : 0 < g.gain j
  · obtain ⟨lo,hi⟩ := privateTotal_bounds h j
    have upper : a.privateTotal j / σ ≤ 1 := (div_le_one h.sigma_pos).mpr hi
    have lower := div_nonneg lo h.sigma_pos.le
    simp only [physical, ite_eq_left site]
    constructor <;> linarith
  · simp [physical, site]

theorem physical_mul {j : J} (site : 0 < g.gain j) :
    a.physical g σ j * σ = σ - a.privateTotal j := by
  simp [physical, site, sub_mul, h.sigma_pos.ne']

theorem private_fill_of_worse {j : J} (site : 0 < g.gain j) (k : Fin G)
    (worse : 0 < a.vacancy j ∨ (∃ i z, z.val ≤ k.val ∧ 0 < a.real i j z) ∨
      (∃ u, u.val < k.val ∧ 0 < a.privateBuy j u)) : a.privateBuy j k = σ / G :=
  le_antisymm (h.private_bounds j k).2 (le_of_not_gt fun unfilled => h.private_stable j site k ⟨unfilled,worse⟩)

/-- The elementary private purchases fill from the top rank down. -/
theorem higher_gap_filled {j : J} (site : 0 < g.gain j) {k u : Fin G}
    (higher : u.val < k.val) (lowerPurchase : 0 < a.privateBuy j u) :
    a.privateBuy j k = σ / G :=
  private_fill_of_worse h site k (Or.inr (Or.inr ⟨u,higher,lowerPurchase⟩))

theorem purchased_quote_ge {i : I} {j : J} {z : Quote G} (purchase : 0 < a.real i j z) :
    a.physical g σ j ≤ price z := by
  have site := (h.eligible_purchase i j z purchase).1
  have mass : σ * (1 - price z) ≤ a.privateTotal j := by
    rw [← mass_above_price h.grid_pos]
    apply Finset.sum_le_sum
    intro k _
    split_ifs with above
    · exact (private_fill_of_worse h site k (Or.inr (Or.inl ⟨i,z,above,purchase⟩))).ge
    · exact (h.private_bounds j k).1
  apply (mul_le_mul_iff_left₀ h.sigma_pos).mp
  rw [physical_mul h site]
  linarith [mul_sub σ 1 (price z), mul_comm σ (price z)]

theorem siteAccepts_of_above {j : J} (site : 0 < g.gain j) {z : Quote G}
    (above : a.physical g σ j < price z) : a.siteAccepts j z := by
  apply Or.inr
  by_contra! none
  have mass : a.privateTotal j ≤ σ * (1 - price z) := by
    rw [← mass_above_price h.grid_pos]
    apply Finset.sum_le_sum
    intro k _
    split_ifs with le
    · exact (h.private_bounds j k).2
    · exact none k (lt_of_not_ge le)
  have ht := mul_lt_mul_of_pos_right above h.sigma_pos
  rw [physical_mul h site] at ht
  linarith [mul_sub σ 1 (price z), mul_comm σ (price z)]

theorem vacancy_implies_zero {j : J} (vac : 0 < a.vacancy j) : a.physical g σ j = 0 := by
  by_cases site : 0 < g.gain j
  · have fill (k : Fin G) := private_fill_of_worse h site k (Or.inl vac)
    have total : a.privateTotal j = σ := by simpa [privateTotal, fill] using gap_mass h.grid_pos σ
    simp [physical, site, total, h.sigma_pos.ne']
  · simp [physical, site]

end Holdings
end Kintali.ExactRecovery
