module

public import Kintali.QuotaSweep.Expansion
public import Kintali.QuotaSweep.SparseRefinement
public import Kintali.QuotaSweep.IndexEquality
public import Kintali.QuotaSweep.KeyTable
public import Kintali.QuotaSweep.LayoutTables
public import Kintali.ExactRecovery.SparseGrouping
public import Kintali.BudgetContact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The executable selected restriction and its analytical expansion

The grouped trial enumerates only retained real bids and private intervals.
Its stable first budget contact expands to the same physical coverage at
every site in the full elementary grid, with zero on omitted real bids.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep

section General

variable {I J A H : Type*} {G : ℕ}
variable [Fintype I] [Fintype J] [Fintype A] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
variable [Encodable I] [Encodable J] [Encodable A] [Encodable H]
variable {g : Game I J} {L : Layout I J G A H} {P : Grouping.Partition (J × Fin G) H}
variable {bi : I → ℕ} {si : J → ℕ} {σ t : ℚ} {x : R I J A H → ℚ}
variable {redirect : I → J} {optional : I → J → Quote G → Bool}

theorem expanded_stable (geo : Geometry L P) (listed : ListsReal L g bi si redirect optional)
    (hσ : 0 ≤ σ) (hs : (book g bi si L).market.StableOn (book g bi si L).retainedRecords
      (Book.quota (Expanded.siteRate g) (mass g σ L) t) x) :
    Expanded.Stable g bi si redirect optional σ t (expandedAllocation g σ L P x) := by
  rw [← coarseMass_eq g σ geo] at hs
  have hw (h : H) : 0 ≤ groupUnit g σ L h := by
    unfold groupUnit
    split
    · exact div_nonneg hσ (Nat.cast_nonneg _)
    · exact le_rfl
  have h := (refinement g bi si geo).stable_expand hw hs
  rw [fineMass_eq g σ geo, ← Expanded.quota_eq_sweep] at h
  exact elementary_stable_extend listed h

theorem siteCoverage_eq_physical (geo : Geometry L P) (listed : ListsReal L g bi si redirect optional)
    (hG : 0 < G) (hσ : 0 < σ)
    (hs : (book g bi si L).market.StableOn (book g bi si L).retainedRecords
      (Book.quota (Expanded.siteRate g) (mass g σ L) t) x) (j : J) :
    siteCoverage g σ L x j = (Expanded.holdings (expandedAllocation g σ L P x)).physical g σ j := by
  rw [← Expanded.coverage_eq_physical (expanded_stable geo listed hσ.le hs) hσ hG j]
  by_cases ha : 0 < g.gain j
  · have hi : Function.Injective (fun k : Fin G => (outside (.inr (j,k)) : Expanded.R I J G)) := by
      intro k l h
      simpa using h
    simp only [siteCoverage, ha, ↓reduceIte, Market.coverage, Expanded.privateOutsideSet,
      Finset.sum_image hi.injOn]
    rw [siteOutside_eq geo (refinement g bi si geo) hs]
  · simp [siteCoverage, ha, Market.coverage, Expanded.privateOutsideSet]

end General

variable {k m G : ℕ} (g : Game (Fin k) (Fin m)) (redirect : Fin k → Fin m)
variable (s : QuoteSearch.Selection (k*m))

theorem selectedListsReal (bi : Fin k → ℕ) (si : Fin m → ℕ) :
    ListsReal (selectedLayout (G := G) g redirect s) g bi si redirect (selectedOptional s) := by
  rintro ⟨i,j,z⟩
  change (∃ a, realEmbedding g redirect s a = (i,j,z)) ↔
    Expanded.realBid i j z ∈ (Expanded.book g bi si redirect (selectedOptional s)).retained
  rw [realEmbedding_range, mem_realBids, mem_realAt, Expanded.retained_real]

def selectedParameters (σ : ℚ) :=
  let L := selectedLayout (G := G) g redirect s
  BudgetContact.parameters g σ (fun h => (L.representative h).1)
    (fun h => mass g σ L (.inr h))

/-- The state computed from the sparse selected trial; quote tie-breaks are
the finite type and site indices of the explicitly listed input. -/
@[noinline] def selectedRun (σ : ℚ) :=
  let L := (selectedLayout (G := G) g redirect s).stored
  let K := keyedBook g Fin.val Fin.val L
  let P := BudgetContact.parameters g σ (fun h => (L.representative h).1)
    (fun h => mass g σ L (.inr h))
  K.indexedContact Book.encodedEq Book.encodedEq Book.encodedEq P (8*(K.records.length+1))

def selectedContact (σ : ℚ) := (selectedRun (G := G) g redirect s σ).1.encodedView

theorem selectedContact_eq_firstContact (σ : ℚ) :
    let L := selectedLayout (G := G) g redirect s
    selectedContact g redirect s σ = (book g Fin.val Fin.val L).firstContact
      (selectedParameters g redirect s σ) :=
  by simp [selectedContact,selectedRun,selectedParameters,Book.indexedContact_eq,Book.Stored.encodedView_eq,Book.contactWork_value]

private theorem intervalMass_sum {A : Type*} (real : A ↪ (Fin k × Fin m × Quote G))
    (D : Fin m → QuotePartition G) {σ : ℚ} (hG : 0 < G) (j : Fin m) :
    (∑ h : IntervalGroup D, if h.1 = j then mass g σ (intervalLayout real D) (.inr h) else 0) =
      if 0 < g.gain j then σ else 0 := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single j]
  · change (∑ h : Fin (D j).groups, if j = j then
        (if 0 < g.gain j then ((D j).size h : ℚ) * (σ / G) else 0) else 0) = _
    by_cases ha : 0 < g.gain j
    · have hsum : (∑ h : Fin (D j).groups, ((D j).size h : ℚ)) = G := by
        exact_mod_cast (D j).size_sum
      simp only [ha, ↓reduceIte, ← Finset.sum_mul, hsum]
      field_simp [show (G : ℚ) ≠ 0 by exact_mod_cast hG.ne']
    · simp [ha]
  · intro i _ hne
    simp [hne]
  · simp

theorem selectedContact_correct (valid : g.Valid) (normal : ¬g.DirectCase) (σ : ℚ)
    (hσ : 0 < σ) (hG : 0 < G) (small : ∀ j, g.gain j * σ < 1) :
    let L := selectedLayout (G := G) g redirect s
    let P := intervalGroups (partition g redirect s)
    let z := selectedContact (G := G) g redirect s σ
    let X := expandedAllocation g σ L P z.allocation
    (book g Fin.val Fin.val L).market.StableOn (book g Fin.val Fin.val L).retainedRecords
        (Book.quota (Expanded.siteRate g) (mass g σ L) z.pressure) z.allocation ∧
      0 < z.pressure ∧ z.pressure < 1 + maxGain g ∧
      Expanded.Stable g Fin.val Fin.val redirect (selectedOptional s) σ z.pressure X ∧
      (∀ j, siteCoverage g σ L z.allocation j = (Expanded.holdings X).physical g σ j) ∧
      (∑ j, siteCoverage g σ L z.allocation j) = g.resources := by
  simp only [selectedContact_eq_firstContact]
  let L := selectedLayout (G := G) g redirect s
  let K := book g Fin.val Fin.val L
  let sites := fun h => (L.representative h).1
  let priv := fun h => mass g σ L (.inr h)
  let z := K.firstContact (selectedParameters g redirect s σ)
  have hmass (h) : 0 ≤ priv h := by
    change 0 ≤ if 0 < g.gain (L.representative h).1 then (L.size h : ℚ)*(σ/G) else 0
    split
    · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hσ.le (Nat.cast_nonneg _))
    · exact le_rfl
  have hsite (e) (h) (hb : K.buyer e = .inr h) : K.site e = sites h := by
    rcases e with a | u
    · change Sum.inl (L.real a).1 = Sum.inr h at hb
      cases hb
    · change Sum.inr u = Sum.inr h at hb
      exact congrArg sites (Sum.inr.inj hb)
  have hret (h) (ha : 0 < g.gain (sites h)) : ∃ e ∈ K.retained, K.buyer e = .inr h :=
    ⟨.inr h, (group_retained ..).mpr ha, rfl⟩
  obtain ⟨hs, hp, hbound, hbudget⟩ := BudgetContact.at_budget g valid normal σ hσ small K sites priv
    hmass (intervalMass_sum g (realEmbedding g redirect s) (partition g redirect s) hG) hsite hret
  have rateEq : BudgetContact.rate g = Expanded.siteRate g := by
    funext j
    simp only [BudgetContact.rate, Expanded.siteRate, one_div]
  have massEq : BudgetContact.mass g priv = mass g σ L := by funext b; cases b <;> rfl
  have stable : K.market.StableOn K.retainedRecords
      (Book.quota (Expanded.siteRate g) (mass g σ L) z.pressure) z.allocation := by
    change K.market.StableOn _ (Book.quota (BudgetContact.rate g) (BudgetContact.mass g priv) _ ) _ at hs
    rwa [rateEq, massEq] at hs
  have geo := selectedGeometry (G := G) g redirect s
  have listed := selectedListsReal (G := G) g redirect s Fin.val Fin.val
  refine ⟨stable, hp, hbound, expanded_stable geo listed hσ.le stable,
    siteCoverage_eq_physical geo listed hG hσ stable, ?_⟩
  have ht : (∑ j ∈ BudgetContact.activeSites g, siteOutside L z.allocation j) =
      σ * (g.resources : ℚ) := by
    have heq := BudgetContact.privateSum_bySite g sites (fun b => z.allocation (outside b))
    exact heq.symm.trans hbudget
  change (∑ j, if 0 < g.gain j then siteOutside L z.allocation j / σ else 0) = g.resources
  rw [← Finset.sum_filter]
  change (∑ j ∈ BudgetContact.activeSites g, siteOutside L z.allocation j / σ) = _
  simp only [div_eq_mul_inv, ← Finset.sum_mul, ht]
  field_simp [hσ.ne']

end Kintali.ExactRecovery.Sparse
