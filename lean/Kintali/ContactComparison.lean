module

public import Kintali.StableAllocation
public import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith

/-!
# Contact comparison

Kintali's Lemma 6 compares restricted and full allocations at their
budget contacts by evaluating a common market at both pressures. The
rejection-weight bound proves the required coverage order between any
two stable allocations of that common market.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali
namespace Market

variable {Vertex Record Site : Type*}
variable [DecidableEq Vertex] [Fintype Record] [Fintype Vertex]
variable {M : Market Vertex Record}

/-- At variable pressure, buyer masses stay fixed and site quotas increase
linearly with pressure. Kintali uses rate `1 / dⱼ` at site `j`. -/
def pressureQuota (isSite : Vertex → Bool) (rate mass : Vertex → ℚ)
    (pressure : ℚ) (v : Vertex) : ℚ :=
  if isSite v then rate v * pressure else mass v

/-- Each site's private buyers have combined mass σ. Coverage equals
the sum of their outside balances divided by σ. -/
def coverage (outside : Site → Finset Record) (σ : ℚ)
    (allocation : Record → ℚ) (j : Site) : ℚ :=
  (∑ e ∈ outside j, allocation e) / σ

/-- Give sites sign +1 and buyers sign −1. A zero sum on a two-ended
record says that it is an ordinary buyer–site bid. -/
def side (isSite : Vertex → Bool) (v : Vertex) : ℚ :=
  if isSite v then 1 else -1

theorem coverage_eq_of_stable_same_quota
    {retained : Finset Record} {quota : Vertex → ℚ} {x y : Record → ℚ}
    {outside : Site → Finset Record} (σ : ℚ)
    (hOutside : ∀ j e, e ∈ outside j → (M.ends e).card = 1)
    (hx : M.StableOn retained quota x) (hy : M.StableOn retained quota y) :
    coverage outside σ x = coverage outside σ y := by
  funext j
  unfold coverage
  congr 1
  exact Finset.sum_congr rfl (fun e he => slack_invariant hx hy (hOutside j e he))

/-- Increasing all site quotas can only decrease each buyer's outside
balance. Apply this to the private buyers to compare coverage. -/
theorem coverage_antitone
    {retained : Finset Record} {x y : Record → ℚ} {low high σ : ℚ}
    {isSite : Vertex → Bool} {rate mass : Vertex → ℚ}
    {outside : Site → Finset Record}
    (hBipartite : ∀ e, (M.ends e).card = 2 → (∑ v ∈ M.ends e, side isSite v) = 0)
    (hRate : ∀ v, 0 ≤ rate v) (hPressure : low ≤ high) (hσ : 0 < σ)
    (hOutside : ∀ j e, e ∈ outside j → ∃ v, isSite v = false ∧ M.ends e = {v})
    (hx : M.StableOn retained (pressureQuota isSite rate mass high) x)
    (hy : M.StableOn retained (pressureQuota isSite rate mass low) y) :
    coverage outside σ x ≤ coverage outside σ y := by
  have hSide (v : Vertex) : side isSite v = 1 ∨ side isSite v = -1 := by
    cases h : isSite v <;> simp [side, h]
  have hQuota (v : Vertex) :
      |pressureQuota isSite rate mass high v - pressureQuota isSite rate mass low v| =
        side isSite v * (pressureQuota isSite rate mass high v -
          pressureQuota isSite rate mass low v) := by
    cases h : isSite v
    · simp [pressureQuota, side, h]
    · have hm := mul_le_mul_of_nonneg_left hPressure (hRate v)
      simp [pressureQuota, side, h, abs_of_nonneg (sub_nonneg.mpr hm)]
  intro j
  apply div_le_div_of_nonneg_right _ hσ.le
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨v, hv, hvend⟩ := hOutside j e he
  have hSlack := signed_slack_change hx hy (side isSite) hSide hBipartite hQuota hvend
  simp [side, hv] at hSlack
  linarith [le_abs_self (x e - y e)]

/-- The equal-budget slice of a coordinatewise chain contains only
one coverage vector. -/
private theorem eq_of_le_of_sum_eq [Fintype Site] {x y : Site → ℚ}
    (hle : x ≤ y) (hsum : (∑ j, x j) = ∑ j, y j) : x = y := by
  classical
  have hzero : (∑ j, (y j - x j)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  funext j
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hle i))).mp
    hzero j (Finset.mem_univ j)
  exact (sub_eq_zero.mp hz).symm

variable [DecidableEq Record]

omit [DecidableEq Record] [Fintype Record] [Fintype Vertex] in
/-- Two positive holdings rejected by the same endpoint have the same worst rank. -/
private theorem rejected_positive_unique {x : Record → ℚ} {v : Vertex} {e f : Record}
    (he : v ∈ M.ends e) (hf : v ∈ M.ends f) (hxe : 0 < x e) (hxf : 0 < x f)
    (hre : ¬M.Accepts x v e) (hrf : ¬M.Accepts x v f) : e = f := by
  apply M.rank_injective v e f he hf
  exact le_antisymm (le_of_not_gt (fun h => hrf ⟨e, he, h, hxe⟩))
    (le_of_not_gt (fun h => hre ⟨f, hf, h, hxf⟩))

omit [DecidableEq Record] [Fintype Vertex] in
/-- Any collection of positive ordinary holdings in a stable allocation has
size at most its number of buyers plus sites. Charge a holding to the
buyer if the buyer refuses more, and to the site otherwise. Stability
ensures that the charged endpoint refuses more. -/
theorem positive_support_card_le
    {retained : Finset Record} {quota : Vertex → ℚ} {x : Record → ℚ}
    (hx : M.StableOn retained quota x) (holdings : Finset Record) (buyer site : Record → Vertex)
    (hPos : ∀ e ∈ holdings, 0 < x e)
    (hEnds : ∀ e ∈ holdings, M.ends e = {buyer e, site e})
    (hOrdinary : ∀ e ∈ holdings, (M.ends e).card = 2) :
    holdings.card ≤ (holdings.image buyer).card + (holdings.image site).card := by
  classical
  let buyerAccepts (e : Record) := M.Accepts x (buyer e) e
  let byBuyer := holdings.filter (fun e => ¬buyerAccepts e)
  let bySite := holdings.filter buyerAccepts
  have hBuyerInj : Set.InjOn buyer byBuyer := by
    intro e he f hf hSame
    obtain ⟨he', hre⟩ := Finset.mem_filter.mp he
    obtain ⟨hf', hrf⟩ := Finset.mem_filter.mp hf
    apply rejected_positive_unique (M := M) (v := buyer e) (x := x)
    · simp [hEnds e he']
    · simp [hSame, hEnds f hf']
    · exact hPos e he'
    · exact hPos f hf'
    · exact hre
    · simpa [buyerAccepts, hSame] using hrf
  have hSiteReject {e : Record} (he : e ∈ holdings) (hAccepts : buyerAccepts e) :
      ¬M.Accepts x (site e) e := by
    intro hSite
    apply hx.stable e (hx.support e (hOrdinary e he) (hPos e he))
    refine ⟨hOrdinary e he, ?_⟩
    intro v hv
    rw [hEnds e he, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hAccepts
    · exact hSite
  have hSiteInj : Set.InjOn site bySite := by
    intro e he f hf hSame
    obtain ⟨he', hae⟩ := Finset.mem_filter.mp he
    obtain ⟨hf', haf⟩ := Finset.mem_filter.mp hf
    apply rejected_positive_unique (M := M) (v := site e) (x := x)
    · simp [hEnds e he']
    · simp [hSame, hEnds f hf']
    · exact hPos e he'
    · exact hPos f hf'
    · exact hSiteReject he' hae
    · simpa [hSame] using hSiteReject hf' haf
  have hBuyerCount : byBuyer.card ≤ (holdings.image buyer).card := by
    rw [← Finset.card_image_of_injOn hBuyerInj]
    exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  have hSiteCount : bySite.card ≤ (holdings.image site).card := by
    rw [← Finset.card_image_of_injOn hSiteInj]
    exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  calc
    holdings.card = bySite.card + byBuyer.card :=
      (Finset.card_filter_add_card_filter_not buyerAccepts).symm
    _ ≤ _ := by omega

/-- Lemma 6. The union retains the full contact allocation's positive
ordinary holdings. If none of the new witness bids blocks, both
contact allocations are stable on the union at their respective pressures.
Comparison on that single market makes their equal-budget coverages
identical. A difference in coverage therefore identifies a witness bid
omitted by the trial and blocking its allocation. -/
theorem contact_eq_or_omitted_blocker [Fintype Site]
    {restricted full witness : Finset Record} {trial target : Record → ℚ}
    {tTrial tFull σ : ℚ} {isSite : Vertex → Bool} {rate mass : Vertex → ℚ}
    {outside : Site → Finset Record}
    (hBipartite : ∀ e, (M.ends e).card = 2 → (∑ v ∈ M.ends e, side isSite v) = 0)
    (hRate : ∀ v, 0 ≤ rate v) (hσ : 0 < σ)
    (hOutside : ∀ j e, e ∈ outside j → ∃ v, isSite v = false ∧ M.ends e = {v})
    (hTrial : M.StableOn restricted (pressureQuota isSite rate mass tTrial) trial)
    (hFull : M.StableOn full (pressureQuota isSite rate mass tFull) target)
    (hSubset : restricted ⊆ full) (hWitness : witness ⊆ full)
    (hSupport : ∀ e, (M.ends e).card = 2 → 0 < target e → e ∈ restricted ∪ witness)
    (hBudget : (∑ j, coverage outside σ trial j) = ∑ j, coverage outside σ target j) :
    coverage outside σ trial = coverage outside σ target ∨
      ∃ e ∈ witness, e ∉ restricted ∧ M.Blocks trial e := by
  classical
  by_cases hBlocker : ∃ e ∈ witness, e ∉ restricted ∧ M.Blocks trial e
  · exact Or.inr hBlocker
  apply Or.inl
  have hTrialUnion : M.StableOn (restricted ∪ witness)
      (pressureQuota isSite rate mass tTrial) trial := by
    refine ⟨hTrial.nonneg, hTrial.balance, ?_, ?_⟩
    · intro e he hp
      exact Finset.mem_union_left _ (hTrial.support e he hp)
    · intro e he
      by_cases hr : e ∈ restricted
      · exact hTrial.stable e hr
      · have hw := (Finset.mem_union.mp he).resolve_left hr
        exact fun hb => hBlocker ⟨e, hw, hr, hb⟩
  have hFullUnion : M.StableOn (restricted ∪ witness)
      (pressureQuota isSite rate mass tFull) target :=
    ⟨hFull.nonneg, hFull.balance, hSupport,
      fun e he => hFull.stable e
        ((Finset.mem_union.mp he).elim (fun hr => hSubset hr) (fun hw => hWitness hw))⟩
  rcases le_total tTrial tFull with h | h
  · exact (eq_of_le_of_sum_eq
      (coverage_antitone hBipartite hRate h hσ hOutside hFullUnion hTrialUnion) hBudget.symm).symm
  · exact eq_of_le_of_sum_eq
      (coverage_antitone hBipartite hRate h hσ hOutside hTrialUnion hFullUnion) hBudget

end Market
end Kintali
