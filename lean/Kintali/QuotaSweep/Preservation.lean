module

public import Kintali.QuotaSweep.Choices
import Mathlib.Tactic.Linarith

/-!
# Preservation of stability and the exhaustion bound

Every newly positive record is the proposal of a site. This alone implies
that buyer acceptance can only shrink. For a putative new block, a worse
site holding was either positive before, contradicting old stability, or was
a proposal, contradicting the site's choice of its best accepted bid.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E)

theorem incident_buyers_eq {b c : B} {e : Record B S E}
    (hb : Sum.inl b ∈ K.market.ends e) (hc : Sum.inl c ∈ K.market.ends e) : b = c := by
  rcases e with e | b' | s
  · exact (K.buyer_mem_bid b e).mp hb |>.trans ((K.buyer_mem_bid c e).mp hc).symm
  · change Sum.inl b ∈ K.market.ends (outside b') at hb
    change Sum.inl c ∈ K.market.ends (outside b') at hc
    simp [K.ends_outside] at hb hc
    exact hb.trans hc.symm
  · change Sum.inl b ∈ K.market.ends (vacancy s) at hb
    simp [K.ends_vacancy] at hb

theorem incident_sites_eq {s t : S} {e : Record B S E}
    (hs : Sum.inr s ∈ K.market.ends e) (ht : Sum.inr t ∈ K.market.ends e) : s = t := by
  rcases e with e | b | s'
  · exact ((K.site_mem_bid s e).mp hs).trans ((K.site_mem_bid t e).mp ht).symm
  · change Sum.inr s ∈ K.market.ends (outside b) at hs
    simp [K.ends_outside] at hs
  · change Sum.inr s ∈ K.market.ends (vacancy s') at hs
    change Sum.inr t ∈ K.market.ends (vacancy s') at ht
    simp [K.ends_vacancy] at hs ht
    exact hs.trans ht.symm

theorem buyer_accepts_proposal {x : Record B S E → ℚ} {s : S} {b : B}
    (hb : Sum.inl b ∈ K.market.ends (K.proposal x s)) :
    K.market.Accepts x (.inl b) (K.proposal x s) := by
  rcases K.proposal_cases x s with hoff | hvac
  · cases h : K.proposal x s with
    | inl e =>
      have he := K.proposal_bid h
      rw [h] at hb
      rw [(K.buyer_mem_bid b e).mp hb]
      exact he.2.2
    | inr v => exact False.elim (K.slack_not_mem_offers x s v (h ▸ hoff))
  · simp [hvac, K.ends_vacancy] at hb

/-- A single update, including its endpoint, can create holdings only on
a proposal chosen at the start of the update. -/
def Purchases (x y : Record B S E → ℚ) : Prop :=
  ∀ e, 0 < y e → 0 < x e ∨ ∃ s, K.proposal x s = e

theorem buyer_support {x y : Record B S E → ℚ} (h : K.Purchases x y)
    {b : B} {e : Record B S E} (he : Sum.inl b ∈ K.market.ends e) (hp : 0 < y e) :
    0 < x e ∨ K.market.Accepts x (.inl b) e := by
  rcases h e hp with h | ⟨s, rfl⟩
  · exact Or.inl h
  · exact Or.inr (K.buyer_accepts_proposal he)

theorem buyer_accepts_antitone {x y : Record B S E → ℚ} (h : K.Purchases x y)
    {b : B} {e : Record B S E} (hy : K.market.Accepts y (.inl b) e) :
    K.market.Accepts x (.inl b) e := by
  obtain ⟨f, hf, hef, hyf⟩ := hy
  rcases K.buyer_support h hf hyf with hxf | ⟨g, hg, hfg, hxg⟩
  · exact ⟨f, hf, hef, hxf⟩
  · exact ⟨g, hg, hef.trans hfg, hxg⟩

variable [Fintype B] [Fintype S] [Fintype E]

/-- Both cycle and pressure updates preserve stability. Conservation of the
computed direction and the exhaustion test supply the first two side conditions. -/
theorem stable_of_purchases
    {x y : Record B S E → ℚ} {q q' : Vertex B S → ℚ}
    (hx : K.market.StableOn K.retainedRecords q x) (hy : ∀ e, 0 ≤ y e)
    (hbalance : ∀ v, (∑ e, if v ∈ K.market.ends e then y e else 0) = q' v)
    (h : K.Purchases x y) : K.market.StableOn K.retainedRecords q' y := by
  refine ⟨hy, hbalance, ?_, ?_⟩
  · intro r hr hp
    rcases h r hp with hpos | ⟨s, hprop⟩
    · exact hx.support r hr hpos
    · rcases r with e | b | s'
      · exact K.mem_retainedRecords.mpr (K.proposal_bid hprop).1
      · change (K.market.ends (outside b)).card = 2 at hr
        simp [K.ends_outside] at hr
      · change (K.market.ends (vacancy s')).card = 2 at hr
        simp [K.ends_vacancy] at hr
  · intro r hr hblock
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hr
    change K.market.Blocks y (bid e) at hblock
    have hbuy := K.buyer_accepts_antitone h (hblock.2 (.inl (K.buyer e)) (by simp))
    obtain ⟨f, hsite, hbetter, hyf⟩ :=
      hblock.2 (.inr (K.site e)) (by simp)
    rcases h f hyf with hxf | ⟨s, hprop⟩
    · apply hx.stable (bid e) (K.mem_retainedRecords.mpr he)
      refine ⟨K.bid_degree e, ?_⟩
      intro v hv
      simp only [K.ends_bid, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hbuy
      · exact ⟨f, hsite, hbetter, hxf⟩
    · have hss : s = K.site e := K.incident_sites_eq (hprop ▸ K.proposal_incident x s) hsite
      subst s
      have hp := K.proposal_rank (K.bid_mem_offers.mpr ⟨he, rfl, hbuy⟩)
      rw [hprop] at hp
      exact hp.not_gt hbetter

/-- Records that could still be exhausted. A positive buyer holding is
present; a currently absent ordinary bid can enter only if the buyer accepts it. -/
def remaining (x : Record B S E → ℚ) : Finset (Record B S E) :=
  Finset.univ.filter fun e => ∃ b : B, Sum.inl b ∈ K.market.ends e ∧
    (0 < x e ∨ K.accepts x (.inl b) e = true)

@[simp] theorem mem_remaining {x : Record B S E → ℚ} {r : Record B S E} :
    r ∈ K.remaining x ↔ ∃ b : B, Sum.inl b ∈ K.market.ends r ∧
      (0 < x r ∨ K.market.Accepts x (.inl b) r) := by simp [remaining]

theorem remaining_subset {x y : Record B S E → ℚ} (h : K.Purchases x y) :
    K.remaining y ⊆ K.remaining x := by
  intro e he
  obtain ⟨b, hb, hp | ha⟩ := K.mem_remaining.mp he
  · exact K.mem_remaining.mpr ⟨b, hb, K.buyer_support h hb hp⟩
  · exact K.mem_remaining.mpr ⟨b, hb, Or.inr (K.buyer_accepts_antitone h ha)⟩

/-- Exhausting one worst holding strictly decreases an integer bounded
by the number of market records, including at simultaneous exhaustions. -/
theorem remaining_card_lt {x y : Record B S E → ℚ} (h : K.Purchases x y) {b : B}
    (hp : 0 < x (K.worst x b)) (hzero : y (K.worst x b) = 0) :
    (K.remaining y).card < (K.remaining x).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (K.remaining_subset h) |>.mpr ?_
  refine ⟨K.worst x b, K.mem_remaining.mpr ⟨b, K.worst_incident x b, Or.inl hp⟩, ?_⟩
  intro he
  obtain ⟨c, hc, hc' | hc'⟩ := K.mem_remaining.mp he
  · simp [hzero] at hc'
  · have hcb := K.incident_buyers_eq hc (K.worst_incident x b)
    subst c
    exact K.rejects_worst x b (K.buyer_accepts_antitone h hc')

end Kintali.QuotaSweep.Book
