module

public import Kintali.ExactRecovery.Witness

/-!
# Sparse ordinal book for a selected trial

A real record is indexed by the list of explicitly retained real bids. A
private record is indexed by the list of consecutive groups. Each group uses
one representative gap for its site rank. Comparing two represented records
gives the same order as in the full grid. Computing the sparse book and its
ranks enumerates only the sparse record types.
-/

open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Sparse

structure Layout (I J : Type*) (G : ℕ) (A H : Type*) where
  real : A ↪ (I × (J × Quote G))
  representative : H ↪ (J × Fin G)
  size : H → ℕ

variable {I J A H : Type*} {G : ℕ}
abbrev B (I H : Type*) := I ⊕ H
abbrev E (A H : Type*) := A ⊕ H
abbrev V (I J H : Type*) := Vertex (B I H) J
abbrev R (I J A H : Type*) := Record (B I H) J (E A H)

namespace Layout

variable (L : Layout I J G A H)

def embedBuyer : B I H ↪ Expanded.Buyer I J G := (Function.Embedding.refl I).sumMap L.representative

def embedBid : E A H ↪ Expanded.Bid I J G := L.real.sumMap L.representative

def embedVertex : V I J H ↪ Expanded.V I J G :=
  L.embedBuyer.sumMap (Function.Embedding.refl J)

def embedRecord : R I J A H ↪ Expanded.R I J G := L.embedBid.sumMap L.embedVertex

def buyer : E A H → B I H
  | .inl a => .inl (L.real a).1
  | .inr h => .inr h

def site : E A H → J
  | .inl a => (L.real a).2.1
  | .inr h => (L.representative h).1

variable [DecidableEq I] [DecidableEq J] [DecidableEq H]

def ends : R I J A H → Finset (V I J H)
  | .inl e => {.inl (L.buyer e), .inr (L.site e)}
  | .inr v => {v}

theorem ends_embed (r : R I J A H) :
    Expanded.ends (L.embedRecord r) = (L.ends r).map L.embedVertex := by
  rcases r with (a | h) | v
  · change {Sum.inl (Expanded.buyer (.inl (L.real a))), Sum.inr (Expanded.site (.inl (L.real a)))} =
      ({.inl (.inl (L.real a).1), .inr (L.real a).2.1} : Finset (V I J H)).map L.embedVertex
    simp [Expanded.buyer, Expanded.site, embedVertex, embedBuyer]
  · change {Sum.inl (Expanded.buyer (.inr (L.representative h))), Sum.inr (Expanded.site (.inr (L.representative h)))} =
      ({.inl (.inr h), .inr (L.representative h).1} : Finset (V I J H)).map L.embedVertex
    simp [Expanded.buyer, Expanded.site, embedVertex, embedBuyer]
  · change {L.embedVertex v} = ({v} : Finset _).map L.embedVertex
    simp

end Layout

variable [Fintype I] [Fintype J] [Fintype A] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
variable [Encodable I] [Encodable J]

def rank (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) (v : V I J H)
    (r : R I J A H) : ℕ :=
  Expanded.ordinalRank (fun f => Expanded.key g bi si (L.embedVertex v) (L.embedRecord f)) r

omit [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H] in
theorem rank_lt_iff (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H)
    (v : V I J H) (r s : R I J A H) :
    rank g bi si L v r < rank g bi si L v s ↔
      Expanded.rank g bi si (L.embedVertex v) (L.embedRecord r) <
        Expanded.rank g bi si (L.embedVertex v) (L.embedRecord s) := by
  rw [rank, rank, Expanded.ordinalRank_lt_iff, Expanded.rank_lt_iff_key]

def market (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    Market (V I J H) (R I J A H) where
  ends := L.ends
  rank := rank g bi si L
  degree := by rintro (e | v) <;> simp [Layout.ends]
  rank_injective := by
    intro v e f _ _ equal
    apply L.embedRecord.injective
    apply Expanded.key_injective g bi si (L.embedVertex v)
    apply le_antisymm <;> apply le_of_not_gt <;> intro wrong
    · exact equal.not_gt (Expanded.ordinalRank_strict
        (fun r => Expanded.key g bi si (L.embedVertex v) (L.embedRecord r)) wrong)
    · exact equal.symm.not_gt (Expanded.ordinalRank_strict
        (fun r => Expanded.key g bi si (L.embedVertex v) (L.embedRecord r)) wrong)
  slack_last := by
    rintro (e | w) he v hv f hf hne
    · simp [Layout.ends] at he
    · have same : v = w := Finset.mem_singleton.mp hv
      subst v
      rcases f with e | u
      · exact (rank_lt_iff g bi si L w (.inl e) (.inr w)).mpr (Expanded.ordinary_before_slack ..)
      · exact (hne (congrArg Sum.inr (Finset.mem_singleton.mp hf).symm)).elim

variable [Encodable A] [Encodable H]

/-- All listed real bids are retained. A private group is retained precisely
at an active site. The layout's real embedding is supplied by the selected
eligible quotes and caps. -/
def book (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    Book (B I H) J (E A H) := by
  letI : LinearOrder (R I J A H) := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact
    { market := market g bi si L
      buyer := L.buyer
      site := L.site
      ends_bid := fun _ => rfl
      ends_outside := fun _ => rfl
      ends_vacancy := fun _ => rfl
      records := Finset.univ.sort
      complete := fun _ => by simp
      retained := Finset.univ.filter fun e => Sum.elim (fun _ => true)
        (fun h => decide (0 < g.gain (L.representative h).1)) e = true }

theorem real_retained (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H)
    (a : A) : Sum.inl a ∈ (book g bi si L).retained := by simp [book]

theorem group_retained (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H)
    (h : H) : Sum.inr h ∈ (book g bi si L).retained ↔ 0 < g.gain (L.representative h).1 := by
  simp [book]

def mass (g : Game I J) (σ : ℚ) (L : Layout I J G A H) : B I H → ℚ
  | .inl i => g.prior i
  | .inr h => if 0 < g.gain (L.representative h).1 then (L.size h : ℚ) * (σ / G) else 0

omit [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
  [Encodable I] [Encodable J] [Encodable A] [Encodable H] in
/-- The sparse record inventory consists of the two ordinary classes, the
two outside classes and the vacancies. -/
theorem record_count : Fintype.card (R I J A H) =
    Fintype.card A + Fintype.card H + (Fintype.card I + Fintype.card H) + Fintype.card J := by
  simp [R, E, B, Record, Nat.add_assoc]

end Kintali.ExactRecovery.Sparse
