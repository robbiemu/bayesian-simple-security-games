module

public import Kintali.QuotaSweep.GroupLayout
public import Kintali.QuotaSweep.Restriction
import Mathlib.Tactic.Linarith

/-!
# Stability of the elementary expansion

An accepted fine bid gives a coarse buyer acceptance. A worse holding at
the site either lies in a distinct coarse record and produces a coarse block,
or is lower within the same group. In the latter case the proposing private
buyer is already full. The prefix masses conserve the site quotas exactly.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Grouping.Refinement

variable {I S R F H : Type*} [DecidableEq I] [DecidableEq S] [DecidableEq R]
variable [DecidableEq F] [DecidableEq H]
variable {P : Partition F H} {C : PrivateBook I S R H} {L : PrivateBook I S R F}
variable (A : Refinement P C L)
include A

private theorem same_group_impossible {unit : H → ℚ} (hw : ∀ h, 0 ≤ unit h)
    {x : PrivateRecord I S R H → ℚ} {e : R ⊕ F} {r : PrivateRecord I S R F}
    (heq : P.record (bid e) = P.record r)
    (ha : L.market.Accepts (P.expand unit x) (.inl (L.buyer e)) (bid e))
    (hlt : L.market.rank (.inr (L.site e)) (bid e) < L.market.rank (.inr (L.site e)) r)
    (hp : 0 < P.expand unit x r) : False := by
  rcases e with a | f <;> rcases r with (b | g) | v <;>
    simp only [Partition.record, Partition.edge, Sum.map_inl, Sum.map_inr, id_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at heq
  · subst b
    exact (lt_irrefl _) hlt
  · have horder := A.internal_rank f g heq hlt
    have hpa := A.private_accepts (by simpa [A.fine_private] using ha)
    change 0 < fill (unit (P.group g)) (x (bid (.inr (P.group g)))) (P.index g) at hp
    change 0 < unit (P.group f) -
      fill (unit (P.group f)) (x (bid (.inr (P.group f)))) (P.index f) at hpa
    rw [heq, prior_full (hw _) horder hp, sub_self] at hpa
    exact (lt_irrefl _) hpa

variable [Fintype I] [Fintype S] [Fintype R] [Fintype H]
variable {rate : S → ℚ} {mass : I → ℚ} {unit : H → ℚ} {t : ℚ}
variable {x : PrivateRecord I S R H → ℚ}

theorem block_projects (hw : ∀ h, 0 ≤ unit h)
    (hx : C.market.StableOn C.retainedRecords (Book.quota rate (P.coarseMass mass unit) t) x)
    {e : R ⊕ F} (hb : L.market.Blocks (P.expand unit x) (bid e)) :
    C.market.Blocks x (bid (P.edge e)) := by
  have hbi : Sum.inl (L.buyer e) ∈ L.market.ends (bid e) := by simp
  have hsi : Sum.inr (L.site e) ∈ L.market.ends (bid e) := by simp
  have ha := hb.2 (.inl (L.buyer e)) hbi
  obtain ⟨rb, hincb, hltb, hpb⟩ := ha
  obtain ⟨rs, hincs, hlts, hps⟩ := hb.2 (.inr (L.site e)) hsi
  have hne : P.record (bid e) ≠ P.record rs :=
    fun h => A.same_group_impossible hw h (hb.2 _ hbi) hlts hps
  refine ⟨C.bid_degree _, ?_⟩
  intro v hv
  simp only [C.ends_bid, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · rw [← A.owners]
    exact ⟨P.record rb, A.maps_buyer hincb, A.buyer_rank _ _ _ hbi hincb hltb,
      A.positive_coarse hw hx hpb⟩
  · rw [← A.sites]
    exact ⟨P.record rs, A.maps_site hincs, A.site_rank _ _ _ hsi hincs hne hlts,
      A.positive_coarse hw hx hps⟩

variable [Fintype F]

private theorem fine_buyer_balance
    (hx : C.market.StableOn C.retainedRecords (Book.quota rate (P.coarseMass mass unit) t) x)
    (b : I ⊕ F) :
    (∑ r, if Sum.inl b ∈ L.market.ends r then P.expand unit x r else 0) =
      (P.fineMass mass unit) b := by
  cases b with
  | inl i =>
    have h := C.buyer_balance hx (.inl i)
    simpa [Fintype.sum_sum_type, L.ends_bid, L.ends_outside, L.ends_vacancy,
      A.coarse_real, A.coarse_private, A.fine_real, A.fine_private,
      Partition.expand, Partition.coarseMass, Partition.fineMass, eq_comm] using h
  | inr f =>
    simp [Fintype.sum_sum_type, L.ends_bid, L.ends_outside, L.ends_vacancy, A.fine_real,
      A.fine_private, Partition.expand, Partition.fineMass]

private theorem fine_site_balance
    (hx : C.market.StableOn C.retainedRecords (Book.quota rate (P.coarseMass mass unit) t) x)
    (s : S) :
    (∑ r, if Sum.inr s ∈ L.market.ends r then P.expand unit x r else 0) = rate s*t := by
  have hg (h : H) : (∑ k : Fin (P.size h), fill (unit h) (x (bid (.inr h))) k.val) =
      x (bid (.inr h)) := by
    apply group_sum (hx.nonneg _)
    have hr := A.private_row hx h
    linarith [hx.nonneg (outside (.inr h))]
  have hpriv : (∑ f : F, if s = C.site (.inr (P.group f)) then
      fill (unit (P.group f)) (x (bid (.inr (P.group f)))) (P.index f) else 0) =
      ∑ h : H, if s = C.site (.inr h) then x (bid (.inr h)) else 0 := by
    rw [P.sum_fibers]
    simp [hg]
  have hcoarse := C.vacancy_balance hx s
  simp [Fintype.sum_sum_type, L.ends_bid, L.ends_outside, L.ends_vacancy, Book.sitePurchases,
    A.sites, Partition.edge, Partition.expand, eq_comm] at hcoarse ⊢
  erw [hpriv]
  exact hcoarse

/-- The expansion conserves individual buyer balances and site quotas, uses
only retained ordinary bids and is stable in the full elementary private
book. Real purchases and vacant masses are definitionally the original ones. -/
theorem stable_expand (hw : ∀ h, 0 ≤ unit h)
    (hx : C.market.StableOn C.retainedRecords (Book.quota rate (P.coarseMass mass unit) t) x) :
    L.market.StableOn L.retainedRecords (Book.quota rate (P.fineMass mass unit) t)
      (P.expand unit x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ((r | f) | (i | g) | s)
    · exact hx.nonneg _
    · exact fill_nonneg (hw _) _ _
    · exact hx.nonneg _
    · exact sub_nonneg.mpr (fill_le (hw _) _ _)
    · exact hx.nonneg _
  · rintro (b | s)
    · exact A.fine_buyer_balance hx b
    · exact A.fine_site_balance hx s
  · rintro (e | b | s) hc hp
    · apply L.mem_retainedRecords.mpr ((A.retained e).mpr ?_)
      exact C.mem_retainedRecords.mp
        (hx.support (bid (P.edge e)) (C.bid_degree _) (A.positive_coarse hw hx hp))
    · change (L.market.ends (outside b)).card = 2 at hc
      simp [L.ends_outside] at hc
    · change (L.market.ends (vacancy s)).card = 2 at hc
      simp [L.ends_vacancy] at hc
  · intro r hr hb
    obtain ⟨e, hm, rfl⟩ := Finset.mem_map.mp hr
    exact hx.stable (bid (P.edge e)) (C.mem_retainedRecords.mpr ((A.retained e).mp hm))
      (A.block_projects hw hx hb)

end Kintali.QuotaSweep.Grouping.Refinement
