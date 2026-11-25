module

public import Kintali.ExactRecovery.Sparse
public import Kintali.QuotaSweep.GroupLayout

/-! # Integer geometry of consecutive groups

The partition numbers each group from the highest gap down. There is no
retained real quote strictly inside a group. Distinct groups at a common
site appear in the same order as their representatives.
-/

@[expose] public section
namespace Kintali.ExactRecovery.Sparse

variable {I J A H : Type*} {G : ℕ}

structure Geometry (L : Layout I J G A H) (P : QuotaSweep.Grouping.Partition (J × Fin G) H) : Prop where
  size_eq : ∀ h, P.size h = L.size h
  same_site : ∀ f, (L.representative (P.group f)).1 = f.1
  quote_side : ∀ (a : A) (f : J × Fin G), (L.real a).2.1 = f.1 →
    ((L.real a).2.2.val ≤ f.2.val ↔ (L.real a).2.2.val ≤ (L.representative (P.group f)).2.val)
  group_order : ∀ (f u : J × Fin G), f.1 = u.1 → P.group f ≠ P.group u → f.2.val < u.2.val →
    (L.representative (P.group f)).2.val < (L.representative (P.group u)).2.val
  internal_order : ∀ (f u : J × Fin G), P.group f = P.group u → u.2.val < f.2.val →
    P.index f < P.index u

end Kintali.ExactRecovery.Sparse
