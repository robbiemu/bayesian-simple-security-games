module

public import Kintali.ExactRecovery.QuoteOrder
public import Kintali.QuoteSearch.Witness
public import Kintali.QuotaSweep.Rates

/-! # Fixed witness for the expanded book

Kintali's full-contact support compares two budget contacts. The extra witness
contains at most one eligible, nonpermanent, next-above-coverage bid per pair.
Once these bids do not block the trial, its own holdings form a relaxed
pattern witness.
-/

open scoped BigOperators
open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Expanded

variable {I J : Type*} {G : ℕ}

def siteRate (g : Game I J) (j : J) : ℚ := if 0 < g.gain j then 1 / g.gain j else 0

def buyerMass (g : Game I J) (σ : ℚ) : Buyer I J G → ℚ
  | .inl i => g.prior i
  | .inr (j,_) => if 0 < g.gain j then σ / G else 0

theorem quota_eq_sweep (g : Game I J) (σ t : ℚ) :
    quota g σ t = Book.quota (siteRate g) (buyerMass (G := G) g σ) t := by
  funext v
  rcases v with (i | ⟨j,k⟩) | j
  · rfl
  · rfl
  · by_cases active : 0 < g.gain j <;>
      simp [quota, Book.quota, siteRate, active, div_eq_mul_inv, mul_comm]

def nextOptional (g : Game I J) (redirect : I → J) (x : J → ℚ) (pair : I × J) :
    Option (R I J G) :=
  let (i,j) := pair
  let z := nextQuote G (x j)
  if x j < 1 ∧ z ≠ cap G ∧ 0 < g.gain j ∧
    Holdings.quoteCost g i j z ≤ Holdings.outsideCost g redirect i then
    some (bid (realBid i j z)) else none

theorem nextOptional_spec (g : Game I J) (redirect : I → J) (x : J → ℚ) (i : I) (j : J)
    (r : R I J G) : nextOptional g redirect x (i,j) = some r ↔
    let z := nextQuote G (x j)
    x j < 1 ∧ z ≠ cap G ∧ Holdings.Eligible g redirect i j z ∧ bid (realBid i j z) = r := by
  simp only [nextOptional, Holdings.Eligible]
  split_ifs <;> simp_all

def activeSites [Fintype J] (g : Game I J) : Finset J := Finset.univ.filter fun j => 0 < g.gain j

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Encodable I] [Encodable J]
variable {g : Game I J} {bi : I → ℕ} {si : J → ℕ} {redirect : I → J}
variable {optional : I → J → Quote G → Bool} {X Y : R I J G → ℚ} {σ t u η : ℚ}

/-- Positive nonpermanent ordinary real bids at the fixed full contact. -/
def supporting (Y : R I J G → ℚ) : Finset (R I J G) :=
  let keep : R I J G → Bool := fun r => match r with
    | .inl (.inl (_,_,z)) => decide (z ≠ cap G ∧ 0 < Y r)
    | _ => false
  Finset.univ.filter fun r => keep r = true

abbrev allQuotes : I → J → Quote G → Bool := fun _ _ _ => true

abbrev retained (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (redirect : I → J)
    (optional : I → J → Quote G → Bool) : Finset (R I J G) :=
  (book g bi si redirect optional).retainedRecords

omit [DecidableEq I] [DecidableEq J] [Encodable I] [Encodable J] in
theorem mem_supporting {r : R I J G} : r ∈ supporting Y ↔
    ∃ i j z, r = bid (realBid i j z) ∧ z ≠ cap G ∧ 0 < Y r := by
  rcases r with (⟨i,j,z⟩ | ⟨j,k⟩) | v <;> simp [supporting, bid, realBid]

theorem retained_subset (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (redirect : I → J)
    (optional : I → J → Quote G → Bool) :
    retained g bi si redirect optional ⊆ retained g bi si redirect allQuotes := by
  intro r member
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp member
  apply (book g bi si redirect allQuotes).mem_retainedRecords.mpr
  rcases b with ⟨i,j,z⟩ | ⟨j,k⟩
  · exact (retained_real ..).mpr ⟨((retained_real ..).mp hb).1, Or.inr rfl⟩
  · exact (retained_private ..).mpr ((retained_private ..).mp hb)

theorem supporting_subset (full : Stable g bi si redirect allQuotes σ u Y) :
    supporting Y ⊆ retained g bi si redirect allQuotes := by
  intro r member
  obtain ⟨i,j,z,rfl,_,pos⟩ := mem_supporting.mp member
  exact full.support _ (by simp [book, market, ends]) pos

theorem covers_full_purchases (full : Stable g bi si redirect allQuotes σ u Y)
    (optional : I → J → Quote G → Bool) (r : R I J G)
    (degree : ((market g bi si).ends r).card = 2) (pos : 0 < Y r) :
    r ∈ retained g bi si redirect optional ∪ supporting Y := by
  let K := book g bi si redirect optional
  let F := book g bi si redirect (allQuotes (G := G))
  have mem := full.support r degree pos
  rcases r with (⟨i,j,z⟩ | ⟨j,k⟩) | v
  · by_cases capBid : z = cap G
    · apply Finset.mem_union_left _ (K.mem_retainedRecords.mpr _)
      exact (retained_real ..).mpr ⟨((retained_real ..).mp (F.mem_retainedRecords.mp mem)).1, Or.inl capBid⟩
    · exact Finset.mem_union_right _ (mem_supporting.mpr ⟨i,j,z,rfl,capBid,pos⟩)
  · apply Finset.mem_union_left _ (K.mem_retainedRecords.mpr _)
    exact (retained_private ..).mpr ((retained_private ..).mp (F.mem_retainedRecords.mp mem))
  · simp [market, ends] at degree

theorem supporting_card (full : Stable g bi si redirect allQuotes σ u Y) :
    (supporting Y).card ≤ Fintype.card I + (activeSites g).card := by
  let left : R I J G → V I J G := Sum.elim (fun e => .inl (buyer e)) id
  let right : R I J G → V I J G := Sum.elim (fun e => .inr (site e)) id
  have counted := Market.positive_support_card_le full (supporting Y) left right
    (by intro r hr; obtain ⟨_,_,_,_,_,pos⟩ := mem_supporting.mp hr; exact pos)
    (by intro r hr; obtain ⟨_,_,_,rfl,_,_⟩ := mem_supporting.mp hr; rfl)
    (by intro r hr; obtain ⟨_,_,_,rfl,_,_⟩ := mem_supporting.mp hr; simp [book, market, ends])
  have buyers : (supporting Y).image left ⊆ Finset.univ.image (fun i : I => Sum.inl (.inl i)) := by
    rintro v hv
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨i,j,z,rfl,_,_⟩ := mem_supporting.mp hr
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have sites : (supporting Y).image right ⊆ (activeSites g).image Sum.inr := by
    rintro v hv
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨i,j,z,rfl,_,_⟩ := mem_supporting.mp hr
    have hret := (book g bi si redirect allQuotes).mem_retainedRecords.mp (supporting_subset full hr)
    have active := ((retained_real ..).mp hret).1.1
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,active⟩,rfl⟩
  apply counted.trans (Nat.add_le_add _ _)
  · exact ((Finset.card_le_card buyers).trans Finset.card_image_le).trans_eq Finset.card_univ
  · exact (Finset.card_le_card sites).trans Finset.card_image_le

theorem next_clear_of_witness (stable : Stable g bi si redirect optional σ t X)
    (safe : ∀ pair r, nextOptional g redirect ((holdings X).physical g σ) pair = some r →
      ¬(market g bi si).Blocks X r) : (holdings X).NextClear g redirect σ := by
  intro i j below
  dsimp only
  intro eligible costBlock
  let z := nextQuote G ((holdings X).physical g σ j)
  by_cases permanent : z = cap G
  · change (holdings X).costBlock g i j z at costBlock
    change Holdings.Eligible g redirect i j z at eligible
    rw [permanent] at costBlock eligible
    exact caps_clear stable i j eligible costBlock
  · have chosen := (nextOptional_spec g redirect _ i j (bid (realBid i j z))).mpr
        ⟨below,permanent,eligible,rfl⟩
    exact safe (i,j) _ chosen (costBlock_is_block bi si _ _ _ costBlock)

def extended (g : Game I J) (redirect : I → J) (σ : ℚ) (Y : R I J G → ℚ) : Finset (R I J G) :=
  supporting Y ∪ QuoteSearch.extraQuotes (nextOptional g redirect ((holdings Y).physical g σ))

theorem extended_card (full : Stable g bi si redirect allQuotes σ u Y) :
    (extended g redirect σ Y).card ≤
      (Fintype.card I + (activeSites g).card) + Fintype.card I * Fintype.card J := by
  apply (QuoteSearch.extendedWitness_card _ _).trans
  simpa using Nat.add_le_add_right (supporting_card full) (Fintype.card (I × J))

omit [Encodable I] [Encodable J] in
/-- Only positive-gain sites can contribute a next optional quote. -/
theorem next_optional_card (g : Game I J) (redirect : I → J) (x : J → ℚ) :
    (QuoteSearch.extraQuotes (nextOptional (G := G) g redirect x)).card ≤
      Fintype.card I * (activeSites g).card := by
  classical
  let pairs := (Finset.univ : Finset I) ×ˢ activeSites g
  have restrict : QuoteSearch.extraQuotes (nextOptional (G := G) g redirect x) =
      pairs.biUnion (fun pair => (nextOptional (G := G) g redirect x pair).toFinset) := by
    ext r
    rw [QuoteSearch.mem_extraQuotes, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨i,j⟩,chosen⟩
      have active := ((nextOptional_spec ..).mp chosen).2.2.1.1
      exact ⟨(i,j),Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,active⟩⟩, by simpa using chosen⟩
    · rintro ⟨pair,_,chosen⟩
      exact ⟨pair, by simpa using chosen⟩
  rw [restrict]
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _ ∈ pairs, 1 := Finset.sum_le_sum (fun pair _ => by
      cases nextOptional (G := G) g redirect x pair <;> simp)
    _ = _ := by simp [pairs]

theorem extended_card_active (full : Stable g bi si redirect allQuotes σ u Y) :
    (extended g redirect σ Y).card ≤ Fintype.card I + (activeSites g).card +
      Fintype.card I * (activeSites g).card :=
  (Finset.card_union_le ..).trans (Nat.add_le_add (supporting_card full) (next_optional_card ..))

end Kintali.ExactRecovery.Expanded
