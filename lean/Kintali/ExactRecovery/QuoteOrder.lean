module

public import Kintali.ExactRecovery.BookContact
public import Kintali.ExactRecovery.Pruning
import Mathlib.Tactic.Linarith

/-! # Quote-order tests for a trial

The ordinal ranks are initial-segment cardinalities for their mathematical
specification. Each rank comparison can instead compare its two keys directly.
Along one buyer/site pair, eligible bids form a prefix, buyer acceptance a
prefix, and site acceptance a suffix. The resulting blocking set is an interval.
-/

open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Expanded

variable {I J : Type*} {G : ℕ} [Fintype I] [Fintype J] [Encodable I] [Encodable J]

theorem rank_lt_iff_key (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    (v : V I J G) (e f : R I J G) :
    rank g bi si v e < rank g bi si v f ↔ key g bi si v e < key g bi si v f :=
  ordinalRank_lt_iff _ _ _

theorem buyer_rank_quote (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (i : I) (j : J)
    (slope : 0 ≤ g.slope i j) {z w : Quote G} (less : z < w) :
    rank g bi si (.inl (.inl i)) (bid (realBid i j z)) <
      rank g bi si (.inl (.inl i)) (bid (realBid i j w)) := by
  have step : price z ≤ price w :=
    div_le_div_of_nonneg_right (by exact_mod_cast less.le : (z.val : ℚ) ≤ w.val) (Nat.cast_nonneg _)
  have cost : Holdings.quoteCost g i j z ≤ Holdings.quoteCost g i j w :=
    add_le_add_right (mul_le_mul_of_nonneg_left step slope) _
  rcases cost.lt_or_eq with strict | equal
  · apply rank_lt_of_primary
    exact WithTop.coe_lt_coe.mpr strict
  · apply rank_strict
    apply Prod.Lex.lt_iff.mpr
    refine Or.inr ⟨congrArg (fun v : ℚ => (v : WithTop ℚ)) equal, ?_⟩
    apply Prod.Lex.lt_iff.mpr
    exact Or.inr ⟨rfl, Prod.Lex.lt_iff.mpr (Or.inl less)⟩

theorem site_rank_quote (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (i : I) (j : J)
    {z w : Quote G} (less : z < w) :
    rank g bi si (.inr j) (bid (realBid i j w)) < rank g bi si (.inr j) (bid (realBid i j z)) := by
  apply rank_lt_of_primary
  apply WithTop.coe_lt_coe.mpr
  change -(2 * (w.val : ℚ)) < -(2 * (z.val : ℚ))
  have h : (z.val : ℚ) < w.val := by exact_mod_cast less
  linarith

variable [DecidableEq I] [DecidableEq J]

/-- Testing strict preference against a finite holdings list only compares
record keys. The list need only contain every positive holding at v. -/
def acceptsAmong (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (X : R I J G → ℚ)
    (v : V I J G) (held : List (R I J G)) (e : R I J G) : Bool :=
  held.any fun f => decide (v ∈ ends f ∧ key g bi si v e < key g bi si v f ∧ 0 < X f)

theorem acceptsAmong_iff (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (X : R I J G → ℚ)
    (v : V I J G) (held : List (R I J G)) (complete : ∀ f, v ∈ ends f → 0 < X f → f ∈ held)
    (e : R I J G) :
    acceptsAmong g bi si X v held e = true ↔ (market g bi si).Accepts X v e := by
  simp only [acceptsAmong, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨f,_,inc,better,pos⟩
    exact ⟨f,inc,rank_strict g bi si v better,pos⟩
  · rintro ⟨f,inc,better,pos⟩
    exact ⟨f,complete f inc pos,inc,(rank_lt_iff_key g bi si v e f).mp better,pos⟩

variable {g : Game I J} {bi : I → ℕ} {si : J → ℕ} {X : R I J G → ℚ} {i : I} {j : J}

theorem buyer_accepts_lower (slope : 0 ≤ g.slope i j) {z w : Quote G} (le : z ≤ w)
    (accept : (market g bi si).Accepts X (.inl (.inl i)) (bid (realBid i j w))) :
    (market g bi si).Accepts X (.inl (.inl i)) (bid (realBid i j z)) := by
  rcases lt_or_eq_of_le le with less | rfl
  · obtain ⟨f,inc,better,pos⟩ := accept
    exact ⟨f,inc,(buyer_rank_quote g bi si i j slope less).trans better,pos⟩
  · exact accept

theorem site_accepts_higher {z w : Quote G} (le : z ≤ w)
    (accept : (market g bi si).Accepts X (.inr j) (bid (realBid i j z))) :
    (market g bi si).Accepts X (.inr j) (bid (realBid i j w)) := by
  rcases lt_or_eq_of_le le with less | rfl
  · obtain ⟨f,inc,better,pos⟩ := accept
    exact ⟨f,inc,(site_rank_quote g bi si i j less).trans better,pos⟩
  · exact accept

theorem blocks_iff_accepts (z : Quote G) :
    (market g bi si).Blocks X (bid (realBid i j z)) ↔
      (market g bi si).Accepts X (.inl (.inl i)) (bid (realBid i j z)) ∧
      (market g bi si).Accepts X (.inr j) (bid (realBid i j z)) := by
  change ((_ : Finset (V I J G)).card = 2 ∧
    (∀ v ∈ ({.inl (.inl i), .inr j} : Finset (V I J G)), _)) ↔ _
  simp [market, ends, buyer, site]

/-- A quote between two blocking quotes blocks as well. The pruned market
uses this on the eligible optional initial segment. -/
theorem blocks_between (slope : 0 ≤ g.slope i j) {u v w : Quote G} (uv : u ≤ v) (vw : v ≤ w)
    (low : (market g bi si).Blocks X (bid (realBid i j u)))
    (high : (market g bi si).Blocks X (bid (realBid i j w))) :
    (market g bi si).Blocks X (bid (realBid i j v)) :=
  (blocks_iff_accepts v).mpr ⟨buyer_accepts_lower slope vw ((blocks_iff_accepts w).mp high).1,
    site_accepts_higher uv ((blocks_iff_accepts u).mp low).2⟩

end Kintali.ExactRecovery.Expanded
