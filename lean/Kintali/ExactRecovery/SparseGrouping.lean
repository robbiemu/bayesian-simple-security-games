module

public import Kintali.ExactRecovery.Geometry
public import Kintali.ExactRecovery.SparseExtension
public import Kintali.QuotaSweep.Grouping
import Mathlib.Tactic.Linarith

/-! # Consecutive gap geometry preserves the ordinal book

The arithmetic statements in `Geometry` imply the incidence, preference and
within-group order hypotheses for the generic stable expansion. Distinct
private gaps at a site are ordered by decreasing gap index. A real quote z is
above private gap k exactly when k < z.
-/

open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Sparse

variable {I J A H : Type*} {G : ℕ} [Fintype I] [Fintype J] [Encodable I] [Encodable J]

private theorem low_gap (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (s : J)
    (d : I × (J × Quote G)) (f : J × Fin G) (lower : f.2.val < d.2.2.val) :
    Expanded.rank g bi si (.inr s) (bid (.inl d)) < Expanded.rank g bi si (.inr s) (bid (.inr f)) := by
  apply Expanded.rank_lt_of_primary
  apply WithTop.coe_lt_coe.mpr
  change -(2 * (d.2.2.val : ℚ)) < -(2 * (f.2.val : ℚ) + 1)
  have step : (f.2.val : ℚ) + 1 ≤ d.2.2.val := by exact_mod_cast lower
  linarith

private theorem high_gap (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (s : J)
    (d : I × (J × Quote G)) (f : J × Fin G) (higher : d.2.2.val ≤ f.2.val) :
    Expanded.rank g bi si (.inr s) (bid (.inr f)) < Expanded.rank g bi si (.inr s) (bid (.inl d)) := by
  apply Expanded.rank_lt_of_primary
  apply WithTop.coe_lt_coe.mpr
  change -(2 * (f.2.val : ℚ) + 1) < -(2 * (d.2.2.val : ℚ))
  have step : (d.2.2.val : ℚ) ≤ f.2.val := by exact_mod_cast higher
  linarith

private theorem gap_order (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (s : J)
    (f u : J × Fin G) (order : u.2.val < f.2.val) :
    Expanded.rank g bi si (.inr s) (bid (.inr f)) < Expanded.rank g bi si (.inr s) (bid (.inr u)) := by
  apply Expanded.rank_lt_of_primary
  apply WithTop.coe_lt_coe.mpr
  change -(2 * (f.2.val : ℚ) + 1) < -(2 * (u.2.val : ℚ) + 1)
  have step : (u.2.val : ℚ) < f.2.val := by exact_mod_cast order
  linarith

private theorem gap_index_of_better (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (s : J)
    (f u : J × Fin G) (sameSite : f.1 = u.1)
    (better : Expanded.rank g bi si (.inr s) (bid (.inr f)) <
      Expanded.rank g bi si (.inr s) (bid (.inr u))) : u.2.val < f.2.val := by
  rcases lt_trichotomy u.2.val f.2.val with lt | eq | gt
  · exact lt
  · have eqF : f = u := Prod.ext sameSite (Fin.ext eq.symm)
    subst u
    exact (lt_irrefl _ better).elim
  · exact (lt_asymm better (gap_order g bi si s u f gt)).elim

variable [DecidableEq I] [DecidableEq J]
variable {P : Grouping.Partition (J × Fin G) H} {L : Layout I J G A H}

section
omit [Fintype I] [Fintype J] [Encodable I] [Encodable J]

private theorem record_at_real_buyer {i : I} {e : R I J A (J × Fin G)}
    (inc : Sum.inl (.inl i) ∈ L.elementary.ends e) :
    L.embedRecord (P.record e) = L.elementary.embedRecord e := by
  rcases e with (a | f) | ((b | u) | s)
  · rfl
  · simp [Layout.ends, Layout.buyer] at inc
  · rfl
  · simp [Layout.ends] at inc
  · rfl

private theorem record_at_private_buyer {f : J × Fin G} {e : R I J A (J × Fin G)}
    (inc : Sum.inl (.inr f) ∈ L.elementary.ends e) :
    e = bid (.inr f) ∨ e = outside (.inr f) := by
  rcases e with (a | u) | ((b | u) | s) <;>
    simp [Layout.ends, Layout.buyer, eq_comm] at inc <;> simp [inc]

private theorem records_at_site (s : J) {e : R I J A (J × Fin G)}
    (inc : Sum.inr s ∈ L.elementary.ends e) :
    (∃ a, e = bid (.inl a) ∧ s = (L.real a).2.1) ∨
    (∃ f : J × Fin G, e = bid (.inr f) ∧ s = f.1) ∨ e = vacancy s := by
  rcases e with (a | f) | (b | j)
  · exact Or.inl ⟨a,rfl,by simpa [Layout.ends, Layout.site, Layout.elementary] using inc⟩
  · exact Or.inr (Or.inl ⟨f,rfl,by simpa [Layout.ends, Layout.site, Layout.elementary] using inc⟩)
  · simp [Layout.ends] at inc
  · have eq : s = j := by simpa [Layout.ends] using inc
    exact Or.inr (Or.inr (congrArg vacancy eq.symm))

end

variable [Fintype A] [Fintype H]

theorem buyer_rank_reflect (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    (b : I ⊕ (J × Fin G)) (e f : R I J A (J × Fin G))
    (he : Sum.inl b ∈ L.elementary.ends e) (hf : Sum.inl b ∈ L.elementary.ends f)
    (better : rank g bi si L.elementary (.inl b) e < rank g bi si L.elementary (.inl b) f) :
    rank g bi si L (.inl (P.buyer b)) (P.record e) < rank g bi si L (.inl (P.buyer b)) (P.record f) := by
  have expBetter := (rank_lt_iff g bi si L.elementary (.inl b) e f).mp better
  apply (rank_lt_iff ..).mpr
  rcases b with i | gap
  · rw [record_at_real_buyer he, record_at_real_buyer hf]
    exact expBetter
  · rcases record_at_private_buyer he with rfl | rfl <;>
      rcases record_at_private_buyer hf with rfl | rfl
    · exact (lt_irrefl _ better).elim
    · exact Expanded.ordinary_before_slack ..
    · exact (lt_asymm expBetter (Expanded.ordinary_before_slack ..)).elim
    · exact (lt_irrefl _ better).elim

theorem site_rank_reflect (geo : Geometry L P) (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    (s : J) (e f : R I J A (J × Fin G))
    (he : Sum.inr s ∈ L.elementary.ends e) (hf : Sum.inr s ∈ L.elementary.ends f)
    (distinct : P.record e ≠ P.record f)
    (better : rank g bi si L.elementary (.inr s) e < rank g bi si L.elementary (.inr s) f) :
    rank g bi si L (.inr s) (P.record e) < rank g bi si L (.inr s) (P.record f) := by
  have expBetter := (rank_lt_iff g bi si L.elementary (.inr s) e f).mp better
  apply (rank_lt_iff ..).mpr
  rcases records_at_site s he with ⟨a,rfl,sa⟩ | ⟨v,rfl,sv⟩ | rfl
  · rcases records_at_site s hf with ⟨c,rfl,_⟩ | ⟨w,rfl,sw⟩ | rfl
    · exact expBetter
    · apply low_gap
      apply lt_of_not_ge
      intro no
      have wrong := (geo.quote_side a w (sa.symm.trans sw)).mpr no
      exact lt_asymm expBetter (high_gap g bi si s (L.real a) w wrong)
    · exact Expanded.ordinary_before_slack ..
  · rcases records_at_site s hf with ⟨c,rfl,sc⟩ | ⟨w,rfl,sw⟩ | rfl
    · apply high_gap
      apply (geo.quote_side c v (sc.symm.trans sv)).mp
      exact le_of_not_gt (fun wrong => lt_asymm expBetter (low_gap g bi si s (L.real c) v wrong))
    · apply gap_order
      have groups : P.group w ≠ P.group v := by
        intro eq
        apply distinct
        change (bid (.inr (P.group v)) : R I J A H) = bid (.inr (P.group w))
        rw [eq]
      exact geo.group_order w v (sw.symm.trans sv) groups
        (gap_index_of_better g bi si s v w (sv.symm.trans sw) expBetter)
    · exact Expanded.ordinary_before_slack ..
  · rcases records_at_site s hf with ⟨c,rfl,_⟩ | ⟨w,rfl,_⟩ | rfl
    · exact (lt_asymm expBetter (Expanded.ordinary_before_slack ..)).elim
    · exact (lt_asymm expBetter (Expanded.ordinary_before_slack ..)).elim
    · exact (lt_irrefl _ better).elim

variable [DecidableEq A] [DecidableEq H] [Encodable A] [Encodable H]

/-- The arithmetic cut positions imply every abstract comparison required by
the stable expansion of consecutive private groups. -/
def refinement (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (geo : Geometry L P) :
    Grouping.Refinement P (book g bi si L) (book g bi si L.elementary) where
  realOwner a := (L.real a).1
  coarse_real _ := rfl
  fine_real _ := rfl
  coarse_private _ := rfl
  fine_private _ := rfl
  sites e := by
    rcases e with a | f
    · rfl
    · exact (geo.same_site f).symm
  retained e := by
    rcases e with a | f
    · exact iff_of_true (real_retained ..) (real_retained ..)
    · change Sum.inr f ∈ (book g bi si L.elementary).retained ↔ Sum.inr (P.group f) ∈ (book g bi si L).retained
      rw [group_retained, group_retained, geo.same_site]
      rfl
  buyer_rank := buyer_rank_reflect g bi si
  site_rank := site_rank_reflect geo g bi si
  internal_rank f u group better := by
    have same := (geo.same_site f).symm.trans ((congrArg (fun h => (L.representative h).1) group).trans
      (geo.same_site u))
    apply geo.internal_order f u group
    apply gap_index_of_better g bi si f.1 f u same
    exact (rank_lt_iff g bi si L.elementary (.inr f.1) (bid (.inr f)) (bid (.inr u))).mp better

end Kintali.ExactRecovery.Sparse
