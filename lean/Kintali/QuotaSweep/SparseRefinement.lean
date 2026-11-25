module

public import Kintali.QuotaSweep.IntervalGroups
public import Kintali.ExactRecovery.Geometry
public import Kintali.RetainedQuotes

/-! # The sparse selected quotes determine a valid grouped market -/

open scoped BigOperators

@[expose] public section
namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep

variable {I J A : Type*} {G : ℕ}

/-- A retained real quote is a boundary of its own site's partition.
This guarantees comparison with every individual gap gives the same
answer as comparison with that group's representative. -/
theorem interval_geometry (real : A ↪ (I × J × Quote G)) (D : J → QuotePartition G)
    (boundaries : ∀ a, ∃ i, (D (real a).2.1).cut i = (real a).2.2.val) :
    Geometry (intervalLayout real D) (intervalGroups D) where
  size_eq _ := rfl
  same_site _ := rfl
  quote_side := by
    rintro a ⟨j,k⟩ hs
    change (real a).2.1 = j at hs
    subst j
    obtain ⟨i,hi⟩ := boundaries a
    have he := representative_lt_cut_iff (D (real a).2.1) k i
    change (real a).2.2.val ≤ k.val ↔
      (real a).2.2.val ≤ ((D (real a).2.1).representative (groupIndex (D (real a).2.1) k)).val
    omega
  group_order := by
    rintro ⟨j,k⟩ ⟨j',l⟩ hs hn hl
    change j = j' at hs
    subst j'
    have hdiff : groupIndex (D j) k ≠ groupIndex (D j) l :=
      fun he => hn (congrArg (Sigma.mk j) he)
    exact representative_strict (D j) hdiff hl
  internal_order := by
    rintro ⟨j,k⟩ ⟨j',l⟩ he hl
    have hs : j = j' := congrArg Sigma.fst he
    subst j'
    have eq : groupIndex (D j) k = groupIndex (D j) l := by simpa using he
    exact position_strict (D j) eq.symm hl

variable {k m : ℕ}

/-- This constructor uses just the selected real-bid list and finite
boundary lists in its runtime record types. -/
def selectedLayout (g : Game (Fin k) (Fin m)) (redirect : Fin k → Fin m)
    (s : QuoteSearch.Selection (k*m)) :=
  intervalLayout (realEmbedding (G := G) g redirect s) (partition g redirect s)

theorem selectedGeometry (g : Game (Fin k) (Fin m)) (redirect : Fin k → Fin m)
    (s : QuoteSearch.Selection (k*m)) :
    Geometry (selectedLayout (G := G) g redirect s) (intervalGroups (partition g redirect s)) := by
  apply interval_geometry
  intro a
  let v := realEmbedding (G := G) g redirect s a
  exact retained_at_boundary g redirect s v.1 v.2.1 v.2.2
    ((realEmbedding_range g redirect s v).mp ⟨a, rfl⟩)

end Kintali.ExactRecovery.Sparse
