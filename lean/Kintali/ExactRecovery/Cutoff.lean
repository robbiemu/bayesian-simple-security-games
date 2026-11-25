module

public import Kintali.ExactRecovery.QuoteOrder

/-! # The exact site-acceptance rule

For an active site, the sparse trial need only know coverage, vacancy and its
positive real holdings at the queried quote. The equality case retains the
paper's buyer-index tie-break. Elementary private gaps need not be enumerated
when evaluating the rule.
-/

open scoped BigOperators
open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery

namespace Holdings

variable {I J : Type*} [Fintype I] [Fintype J] {G : ℕ} {a : Holdings I J G}
variable {g : Game I J} {redirect : I → J} {σ t : ℚ}

/-- A positive private holding *strictly* below p puts physical coverage
strictly below p: all G−z gaps above p are already full. -/
theorem above_physical_of_private_below (h : a.Contact g redirect σ t) {j : J}
    (site : 0 < g.gain j) {z : Quote G} {k : Fin G} (low : k.val < z.val)
    (positive : 0 < a.privateBuy j k) : a.physical g σ j < price z := by
  have mass : σ * (1 - price z) < a.privateTotal j := by
    rw [← mass_above_price h.grid_pos]
    apply Finset.sum_lt_sum
    · intro u _
      split_ifs with higher
      · exact (higher_gap_filled h site (low.trans_le higher) positive).ge
      · exact (h.private_bounds j u).1
    · exact ⟨k,Finset.mem_univ _,by simpa [low.not_ge] using positive⟩
  apply (mul_lt_mul_iff_left₀ h.sigma_pos).mp
  rw [physical_mul h site]
  linarith [mul_sub σ 1 (price z), mul_comm σ (price z)]

end Holdings

namespace Expanded

variable {I J : Type*} {G : ℕ} [Fintype I] [Fintype J] [Encodable I] [Encodable J]

private theorem site_same_quote_better (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    {i b : I} (j : J) (z : Quote G) (lowerIndex : bi i < bi b) :
    rank g bi si (.inr j) (bid (realBid i j z)) < rank g bi si (.inr j) (bid (realBid b j z)) := by
  apply rank_strict
  exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl,Prod.Lex.lt_iff.mpr (Or.inl lowerIndex)⟩)

theorem site_real_better_iff (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    (unique : Function.Injective bi) (i b : I) (j : J) (z w : Quote G) :
    rank g bi si (.inr j) (bid (realBid i j z)) < rank g bi si (.inr j) (bid (realBid b j w)) ↔
      w < z ∨ w = z ∧ bi i < bi b := by
  have byQuote (a c : I) {p q : Quote G} (lt : p < q) :
      rank g bi si (.inr j) (bid (realBid a j q)) < rank g bi si (.inr j) (bid (realBid c j p)) := by
    apply rank_lt_of_primary
    apply WithTop.coe_lt_coe.mpr
    change -(2 * (q.val : ℚ)) < -(2 * (p.val : ℚ))
    have h : (p.val : ℚ) < q.val := by exact_mod_cast lt
    linarith
  constructor
  · intro better
    rcases lt_trichotomy w z with lower | eq | higher
    · exact Or.inl lower
    · subst w
      refine Or.inr ⟨rfl,?_⟩
      rcases lt_trichotomy (bi i) (bi b) with yes | same | no
      · exact yes
      · obtain rfl := unique same
        exact (lt_irrefl _ better).elim
      · exact (lt_asymm better (site_same_quote_better g bi si j z no)).elim
    · exact (lt_asymm better (byQuote b i higher)).elim
  · rintro (lower | ⟨rfl,lowerIndex⟩)
    · exact byQuote i b lower
    · exact site_same_quote_better g bi si j w lowerIndex

variable [DecidableEq I] [DecidableEq J]
variable {g : Game I J} {bi : I → ℕ} {si : J → ℕ} {X : R I J G → ℚ}
variable {redirect : I → J} {σ t : ℚ}

theorem site_accepts_iff_records (unique : Function.Injective bi) (i : I) (j : J) (z : Quote G) :
    (market g bi si).Accepts X (.inr j) (bid (realBid i j z)) ↔
    0 < (holdings X).vacancy j ∨
      (∃ k : Fin G, k.val < z.val ∧ 0 < (holdings X).privateBuy j k) ∨
      ∃ b w, (w < z ∨ w = z ∧ bi i < bi b) ∧ 0 < (holdings X).real b j w := by
  constructor
  · rintro ⟨r,inc,better,pos⟩
    rcases r with (⟨b,k,w⟩ | ⟨k,u⟩) | (v | k)
    · have eq : j = k := by simpa [market, ends, site] using inc
      subst k
      exact Or.inr (Or.inr ⟨b,w,(site_real_better_iff g bi si unique i b j z w).mp better,pos⟩)
    · have eq : j = k := by simpa [market, ends, site] using inc
      subst k
      have lower : u.val < z.val := lt_of_not_ge (fun le =>
        lt_asymm better (gap_before_lower_real g bi si i j le))
      exact Or.inr (Or.inl ⟨u,lower,pos⟩)
    · simp [market, ends] at inc
    · have eq : j = k := by simpa [market, ends] using inc
      subst k
      exact Or.inl pos
  · rintro (vac | ⟨k,lower,pos⟩ | ⟨b,w,order,pos⟩)
    · exact ⟨vacancy j, by simp [market, ends], ordinary_before_slack .., vac⟩
    · exact ⟨bid (privateBid j k), by simp [market, ends, site], real_before_lower_gap g bi si i j lower,pos⟩
    · exact ⟨bid (realBid b j w), by simp [market, ends, site],
        (site_real_better_iff g bi si unique i b j z w).mpr order,pos⟩

/-- Section 2's exact cutoff, including omitted real bids: above coverage
the site always accepts, below it always refuses, and at equality only a
vacancy or a lower-priority real holding suffices. -/
theorem site_accepts_iff_cutoff (h : (holdings X).Contact g redirect σ t) (unique : Function.Injective bi)
    (i : I) (j : J) (site : 0 < g.gain j) (z : Quote G) :
    (market g bi si).Accepts X (.inr j) (bid (realBid i j z)) ↔
      (holdings X).physical g σ j < price z ∨
        (holdings X).physical g σ j = price z ∧
        (0 < (holdings X).vacancy j ∨ ∃ b, bi i < bi b ∧ 0 < (holdings X).real b j z) := by
  rw [site_accepts_iff_records unique]
  constructor
  · rintro (vac | ⟨k,lower,pos⟩ | ⟨b,w,order,pos⟩)
    · have zero := Holdings.vacancy_implies_zero h vac
      have le : (holdings X).physical g σ j ≤ price z := by
        rw [zero]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact le.lt_or_eq.imp_right (fun eq => ⟨eq,Or.inl vac⟩)
    · exact Or.inl (Holdings.above_physical_of_private_below h site lower pos)
    · have le := Holdings.purchased_quote_ge h pos
      rcases order with low | ⟨rfl,index⟩
      · exact Or.inl (le.trans_lt (div_lt_div_of_pos_right
          (by exact_mod_cast low : (w.val : ℚ) < z.val)
          (by exact_mod_cast h.grid_pos : (0 : ℚ) < G)))
      · exact le.lt_or_eq.imp_right (fun eq => ⟨eq,Or.inr ⟨b,index,pos⟩⟩)
  · rintro (above | ⟨_,vac | ⟨b,index,pos⟩⟩)
    · exact (Holdings.siteAccepts_of_above h site above).imp_right Or.inl
    · exact Or.inl vac
    · exact Or.inr (Or.inr ⟨b,z,Or.inr ⟨rfl,index⟩,pos⟩)

end Expanded
end Kintali.ExactRecovery
