module

public import Kintali.QuotaSweep.QuotePartitions
public import Kintali.QuotaSweep.Grouping
public import Kintali.ExactRecovery.Sparse

/-! # Private interval groups, representatives, and comparison at retained cuts -/

@[expose] public section
namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep

variable {I J A : Type*} {G : ℕ}

abbrev IntervalGroup (D : J → QuotePartition G) := (j : J) × Fin (D j).groups

def intervalLayout (real : A ↪ (I × J × Quote G)) (D : J → QuotePartition G) :
    Layout I J G A (IntervalGroup D) where
  real := real
  representative := ⟨fun h => (h.1, (D h.1).representative h.2), by
    rintro ⟨j,h⟩ ⟨l,k⟩ he
    obtain e : j = l := congrArg Prod.fst he
    subst l
    exact congrArg (Sigma.mk j) ((D j).representative_injective (congrArg Prod.snd he))⟩
  size h := (D h.1).size h.2

/-- The analytic regrouping enumerates elementary gaps in descending rank
inside each of the consecutive intervals. The executable layout stores
only `representative` and `size`. -/
noncomputable def intervalGroups (D : J → QuotePartition G) :
    Grouping.Partition (J × Fin G) (IntervalGroup D) where
  size h := (D h.1).size h.2
  enumerate :=
    { toFun := fun jk =>
        let t := (D jk.1).equivalence.symm jk.2
        ⟨⟨jk.1,t.1⟩,t.2⟩
      invFun := fun p => (p.1.1, (D p.1.1).gapAt ⟨p.1.2, p.2⟩)
      left_inv := by
        rintro ⟨j,k⟩
        exact congrArg (Prod.mk j) ((D j).equivalence.apply_symm_apply k)
      right_inv := by
        rintro ⟨⟨j,h⟩,k⟩
        have he := (D j).equivalence.symm_apply_apply ⟨h,k⟩
        exact congrArg (fun a : (h : Fin (D j).groups) × Fin ((D j).size h) =>
          (⟨⟨j,a.1⟩,a.2⟩ : (u : IntervalGroup D) × Fin ((D u.1).size u.2))) he }

noncomputable def groupIndex (D : QuotePartition G) (k : Fin G) : Fin D.groups :=
  (D.equivalence.symm k).1

noncomputable def position (D : QuotePartition G) (k : Fin G) : ℕ :=
  (D.equivalence.symm k).2.val

@[simp] theorem group_at (D : J → QuotePartition G) (j : J) (k : Fin G) :
    (intervalGroups D).group (j,k) = ⟨j, groupIndex (D j) k⟩ := rfl

@[simp] theorem index_at (D : J → QuotePartition G) (j : J) (k : Fin G) :
    (intervalGroups D).index (j,k) = position (D j) k := rfl

theorem gap_in_group (D : QuotePartition G) (k : Fin G) :
    D.lo (groupIndex D k) ≤ k.val ∧ k.val < D.hi (groupIndex D k) := by
  have hb := D.gapAt_bounds (D.equivalence.symm k)
  have he : D.gapAt (D.equivalence.symm k) = k := D.equivalence.apply_symm_apply k
  rw [he] at hb
  exact hb

theorem representative_in_group (D : QuotePartition G) (h : Fin D.groups) :
    D.lo h ≤ (D.representative h).val ∧ (D.representative h).val < D.hi h :=
  D.gapAt_bounds ⟨h, ⟨0, Nat.sub_pos_of_lt (D.lo_lt_hi h)⟩⟩

theorem representative_lt_cut_iff (D : QuotePartition G) (k : Fin G)
    (q : Fin (D.groups+1)) :
    (D.representative (groupIndex D k)).val < D.cut q ↔ k.val < D.cut q := by
  have hk := gap_in_group D k
  have hr := representative_in_group D (groupIndex D k)
  rcases D.cut_outside_open (groupIndex D k) q with h | h <;> omega

theorem representative_strict (D : QuotePartition G) {k l : Fin G}
    (hne : groupIndex D k ≠ groupIndex D l) (h : k < l) :
    D.representative (groupIndex D k) < D.representative (groupIndex D l) := by
  have hk := gap_in_group D k
  have hl := gap_in_group D l
  have hrk := representative_in_group D (groupIndex D k)
  have hrl := representative_in_group D (groupIndex D l)
  rcases lt_or_gt_of_ne hne with horder | horder
  · exact hrk.2.trans_le ((D.separated horder).trans hrl.1)
  · have sep := D.separated horder
    exact False.elim (not_lt_of_ge (hk.1.trans' (sep.trans' hl.2.le)) h)

theorem position_strict (D : QuotePartition G) {k l : Fin G}
    (he : groupIndex D k = groupIndex D l) (h : k < l) : position D l < position D k := by
  have hk := congrArg Fin.val (D.equivalence.apply_symm_apply k)
  have hl := congrArg Fin.val (D.equivalence.apply_symm_apply l)
  change D.hi (groupIndex D k) - 1 - position D k = k.val at hk
  change D.hi (groupIndex D l) - 1 - position D l = l.val at hl
  rw [he] at hk
  change k.val < l.val at h
  omega

end Kintali.ExactRecovery.Sparse
