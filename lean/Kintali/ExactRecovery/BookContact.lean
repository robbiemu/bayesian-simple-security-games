module

public import Kintali.ExactRecovery.Book
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-! # Stable expanded holdings give the contact used in Lemma 4

The sweeper supplies a stable allocation at its budget pressure. Splitting
the buyer and site balance equations on the expanded record type gives all
the elementary holdings. A strictly better real cost, or a site with private
mass below a quote, gives actual ordinal acceptance in this book.
-/

open scoped BigOperators
open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Expanded

variable {I J : Type*} {G : ℕ}

def holdings (X : R I J G → ℚ) : Holdings I J G where
  real i j z := X (bid (realBid i j z))
  outside i := X (outside (.inl i))
  privateBuy j k := X (bid (privateBid j k))
  vacancy j := X (vacancy j)

def quota (g : Game I J) (σ t : ℚ) : V I J G → ℚ
  | .inl (.inl i) => g.prior i
  | .inl (.inr (j,_)) => if 0 < g.gain j then σ / G else 0
  | .inr j => if 0 < g.gain j then t / g.gain j else 0

variable [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J] [Encodable I] [Encodable J]
variable {g : Game I J} {bi : I → ℕ} {si : J → ℕ} {redirect : I → J}
variable {optional : I → J → Quote G → Bool} {X : R I J G → ℚ} {σ t : ℚ}

abbrev Stable (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (redirect : I → J)
    (optional : I → J → Quote G → Bool) (σ t : ℚ) (X : R I J G → ℚ) : Prop :=
  let K := book g bi si redirect optional
  K.market.StableOn K.retainedRecords (quota g σ t) X

private theorem select_row {U W : Type*} [DecidableEq U] [Fintype U] [Fintype W]
    (u : U) (f : U → W → ℚ) :
    (∑ i, ∑ w, if u = i then f i w else 0) = ∑ w, f u w := by
  rw [Finset.sum_comm]
  simp

private theorem select_table {U V W : Type*} [DecidableEq U] [Fintype U] [Fintype V] [Fintype W]
    (u : U) (f : U → V → W → ℚ) :
    (∑ i, ∑ j, ∑ w, if u = i then f i j w else 0) = ∑ j, ∑ w, f u j w := by
  calc
    _ = ∑ i, if u = i then ∑ j, ∑ w, f i j w else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases eq : u = i <;> simp [eq]
    _ = _ := by simp

variable (stable : Stable g bi si redirect optional σ t X)
include stable in
theorem real_balance (i : I) :
    (∑ j, ∑ z, (holdings X).real i j z) + (holdings X).outside i = g.prior i := by
  have hb := stable.balance (.inl (.inl i))
  change (∑ r : R I J G, if Sum.inl (.inl i) ∈ ends r then X r else 0) = g.prior i at hb
  simp [ends, buyer, Fintype.sum_sum_type, Fintype.sum_prod_type] at hb
  exact (select_table i (fun i j z => X (bid (realBid i j z)))) ▸ hb

include stable in
theorem gap_balance (j : J) (k : Fin G) :
    (holdings X).privateBuy j k + X (outside (.inr (j,k))) = if 0 < g.gain j then σ / G else 0 := by
  have hb := stable.balance (.inl (.inr (j,k)))
  change (∑ r : R I J G, if Sum.inl (.inr (j,k)) ∈ ends r then X r else 0) = _ at hb
  simpa [ends, buyer, Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.sum_ite_irrel, holdings,
    quota, ite_and] using hb

include stable in
theorem site_balance (j : J) (active : 0 < g.gain j) :
    (holdings X).realTotal j + (holdings X).privateTotal j + (holdings X).vacancy j = t / g.gain j := by
  have hb := stable.balance (.inr j)
  change (∑ r : R I J G, if Sum.inr j ∈ ends r then X r else 0) = _ at hb
  simp [ends, site, Fintype.sum_sum_type, Fintype.sum_prod_type, quota, active] at hb
  have realRow (i : I) := select_row j (fun j z => X (bid (realBid i j z)))
  have privateRow := select_row j (fun j k => X (bid (privateBid j k)))
  simp only [bid, realBid, privateBid] at realRow privateRow
  simp only [realRow, privateRow] at hb
  exact hb

omit [DecidableEq I] [DecidableEq J] in
theorem real_before_lower_gap (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (i : I) (j : J)
    {z : Quote G} {k : Fin G} (lower : k.val < z.val) :
    rank g bi si (.inr j) (bid (realBid i j z)) < rank g bi si (.inr j) (bid (privateBid j k)) := by
  apply rank_lt_of_primary
  apply WithTop.coe_lt_coe.mpr
  change -(2 * (z.val : ℚ)) < -(2 * (k.val : ℚ) + 1)
  have step : (k.val : ℚ) + 1 ≤ z.val := by exact_mod_cast lower
  linarith

omit [DecidableEq I] [DecidableEq J] in
theorem gap_before_lower_real (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (i : I) (j : J)
    {z : Quote G} {k : Fin G} (lower : z.val ≤ k.val) :
    rank g bi si (.inr j) (bid (privateBid j k)) < rank g bi si (.inr j) (bid (realBid i j z)) := by
  apply rank_lt_of_primary
  apply WithTop.coe_lt_coe.mpr
  change -(2 * (k.val : ℚ) + 1) < -(2 * (z.val : ℚ))
  have step : (z.val : ℚ) ≤ k.val := by exact_mod_cast lower
  linarith

omit [DecidableEq I] [DecidableEq J] in
theorem gap_before_lower_gap (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (j : J)
    {k u : Fin G} (lower : u.val < k.val) :
    rank g bi si (.inr j) (bid (privateBid j k)) < rank g bi si (.inr j) (bid (privateBid j u)) := by
  apply rank_lt_of_primary
  apply WithTop.coe_lt_coe.mpr
  change -(2 * (k.val : ℚ) + 1) < -(2 * (u.val : ℚ) + 1)
  have step : (u.val : ℚ) < k.val := by exact_mod_cast lower
  linarith

theorem costBlock_is_block (bi : I → ℕ) (si : J → ℕ) (i : I) (j : J) (z : Quote G)
    (block : (holdings X).costBlock g i j z) : (market g bi si).Blocks X (bid (realBid i j z)) := by
  refine ⟨by simp [market, ends], ?_⟩
  intro v incident
  change v ∈ ({.inl (.inl i), .inr j} : Finset (V I J G)) at incident
  rcases Finset.mem_insert.mp incident with rfl | atSite
  · rcases block.1 with out | ⟨k,w,purchased,dearer⟩
    · exact ⟨outside (.inl i), by simp [market, ends], ordinary_before_slack .., out⟩
    · refine ⟨bid (realBid i k w), by simp [market, ends, buyer], ?_, purchased⟩
      exact rank_lt_of_primary g bi si _ (WithTop.coe_lt_coe.mpr dearer)
  · obtain rfl := Finset.mem_singleton.mp atSite
    rcases block.2 with vac | ⟨k,lower,purchased⟩
    · exact ⟨vacancy j, by simp [market, ends], ordinary_before_slack .., vac⟩
    · exact ⟨bid (privateBid j k), by simp [market, ends, site],
        real_before_lower_gap g bi si i j lower, purchased⟩

include stable in
theorem no_private_block (j : J) (active : 0 < g.gain j) (k : Fin G) :
    ¬(holdings X).privateBlock σ j k := by
  rintro ⟨unfilled,worse⟩
  let K := book g bi si redirect optional
  have retained := (retained_private g bi si redirect optional j k).mpr active
  apply stable.stable _ (K.mem_retainedRecords.mpr retained)
  refine ⟨K.bid_degree _, ?_⟩
  intro v incident
  change v ∈ ({.inl (.inr (j,k)), .inr j} : Finset (V I J G)) at incident
  rcases Finset.mem_insert.mp incident with rfl | atSite
  · have mass := gap_balance stable j k
    rw [ite_eq_left active] at mass
    refine ⟨outside (.inr (j,k)), by simp [book, market, ends], ordinary_before_slack .., ?_⟩
    linarith
  · obtain rfl := Finset.mem_singleton.mp atSite
    rcases worse with vac | ⟨i,z,lower,hp⟩ | ⟨u,lower,hp⟩
    · exact ⟨vacancy j, by simp [book, market, ends], ordinary_before_slack .., vac⟩
    · exact ⟨bid (realBid i j z), by simp [book, market, ends, site],
        gap_before_lower_real g bi si i j lower, hp⟩
    · exact ⟨bid (privateBid j u), by simp [book, market, ends, site],
        gap_before_lower_gap g bi si j lower, hp⟩

include stable in
/-- A stable expanded allocation at budget pressure provides every balance
and private-stability condition in the elementary contact model. -/
theorem stableContact (grid : 0 < G) (scale : 0 < σ) (pressure : 0 ≤ t)
    (outsideMin : ∀ i j, Holdings.outsideCost g redirect i ≤ g.cost i j (Holdings.endpoint g j))
    (budget : (∑ j, (holdings X).physical g σ j) = g.resources) :
    (holdings X).Contact g redirect σ t := by
  refine ⟨grid, scale, pressure, fun _ _ _ => stable.nonneg _, fun _ => stable.nonneg _,
    ?_, fun _ => stable.nonneg _, real_balance stable, site_balance stable, ?_, outsideMin,
    no_private_block stable, budget⟩
  · intro j k
    refine ⟨stable.nonneg _, ?_⟩
    have hb := gap_balance stable j k
    have hn := stable.nonneg (outside (.inr (j,k)))
    have bound : (if 0 < g.gain j then σ / G else 0) ≤ σ / G := by
      split_ifs <;> first | exact le_rfl | exact div_nonneg scale.le (Nat.cast_nonneg _)
    linarith
  · intro i j z hp
    let K := book g bi si redirect optional
    have hret := K.mem_retainedRecords.mp (stable.support _ (K.bid_degree (realBid i j z)) hp)
    exact ((retained_real g bi si redirect optional i j z).mp hret).1

include stable in
theorem caps_clear : (holdings X).CapClear g redirect := by
  intro i j eligible block
  let K := book g bi si redirect optional
  have retained := (retained_real g bi si redirect optional i j (cap G)).mpr ⟨eligible, Or.inl rfl⟩
  exact stable.stable _ (K.mem_retainedRecords.mpr retained) (costBlock_is_block bi si _ _ _ block)

theorem next_clear_of_not_blocks
    (noBlock : ∀ i j, (holdings X).physical g σ j < 1 →
      let z := nextQuote G ((holdings X).physical g σ j)
      Holdings.Eligible g redirect i j z → ¬(market g bi si).Blocks X (bid (realBid i j z))) :
    (holdings X).NextClear g redirect σ := by
  intro i j below
  dsimp only
  exact fun eligible block => noBlock i j below eligible (costBlock_is_block bi si i j _ block)

def privateOutsideSet (g : Game I J) (j : J) : Finset (R I J G) :=
  if 0 < g.gain j then Finset.univ.image (fun k : Fin G => outside (.inr (j,k))) else ∅

include stable in
theorem coverage_eq_physical (scale : 0 < σ) (grid : 0 < G) (j : J) :
    Market.coverage (privateOutsideSet g) σ X j = (holdings X).physical g σ j := by
  classical
  by_cases active : 0 < g.gain j
  · have inject : Function.Injective (fun k : Fin G => (outside (.inr (j,k)) : R I J G)) := by
      intro k u same
      simpa using same
    have balance := Finset.sum_congr (s₁ := Finset.univ) rfl (fun k _ => gap_balance stable j k)
    simp only [ite_eq_left active, Finset.sum_add_distrib, gap_mass grid] at balance
    simp only [Market.coverage, privateOutsideSet, ite_eq_left active, Finset.sum_image inject.injOn,
      Holdings.physical, Holdings.privateTotal]
    field_simp [scale.ne']
    linarith
  · simp [Market.coverage, privateOutsideSet, Holdings.physical, active]

end Kintali.ExactRecovery.Expanded
