module

public import Kintali.ExactRecovery.Sparse
public import Kintali.QuotaSweep.Restriction

/-! # Extending an elementary sparse book by zero

After splitting groups, a sparse book still contains only the selected real
indices. Embedding their records and filling omitted records with zero gives
stability on precisely the corresponding restriction of the full real grid.
-/

open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Sparse

variable {I J A H : Type*} {G : ℕ}

def Layout.elementary (L : Layout I J G A H) : Layout I J G A (J × Fin G) where
  real := L.real
  representative := Function.Embedding.refl _
  size := fun _ => 1

@[simp] theorem Layout.elementary_vertex (L : Layout I J G A H) (v : Expanded.V I J G) :
    L.elementary.embedVertex v = v := by
  rcases v with (i | f) | j <;> rfl

variable [Fintype I] [Fintype J] [Fintype A] [DecidableEq I] [DecidableEq J] [DecidableEq A]
variable [Encodable I] [Encodable J] [Encodable A]
variable {g : Game I J} {bi : I → ℕ} {si : J → ℕ} {redirect : I → J}
variable {optional : I → J → Quote G → Bool} {L : Layout I J G A H}

/-- The sparse real index contains exactly the retained grid quotes. -/
def ListsReal (L : Layout I J G A H) (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    (redirect : I → J) (optional : I → J → Quote G → Bool) : Prop :=
  ∀ d : I × (J × Quote G), (∃ a, L.real a = d) ↔
    Sum.inl d ∈ (Expanded.book g bi si redirect optional).retained

theorem elementary_retained_image (listed : ListsReal L g bi si redirect optional) :
    ((book g bi si L.elementary).retainedRecords.map L.elementary.embedRecord) =
      Expanded.retained g bi si redirect optional := by
  let S := book g bi si L.elementary
  let K := Expanded.book g bi si redirect optional
  ext r
  constructor
  · rintro member
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hs
    apply K.mem_retainedRecords.mpr
    rcases b with a | ⟨j,k⟩
    · exact (listed (L.real a)).mp ⟨a,rfl⟩
    · exact (Expanded.retained_private ..).mpr ((group_retained ..).mp hb)
  · rintro member
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp member
    rcases b with d | ⟨j,k⟩
    · obtain ⟨a,rfl⟩ := (listed d).mpr hb
      exact Finset.mem_map.mpr ⟨bid (.inl a), S.mem_retainedRecords.mpr (real_retained ..), rfl⟩
    · exact Finset.mem_map.mpr ⟨bid (.inr (j,k)), S.mem_retainedRecords.mpr
        ((group_retained ..).mpr ((Expanded.retained_private ..).mp hb)), rfl⟩

theorem elementary_stable_extend (listed : ListsReal L g bi si redirect optional)
    {q : Expanded.V I J G → ℚ} {x : R I J A (J × Fin G) → ℚ}
    (stable : (book g bi si L.elementary).market.StableOn (book g bi si L.elementary).retainedRecords q x) :
    (Expanded.market g bi si).StableOn (Expanded.retained g bi si redirect optional) q
      (Restriction.extend L.elementary.embedRecord x) := by
  rw [← elementary_retained_image listed]
  apply Restriction.stable_extend L.elementary.embedRecord _ _ stable
  · intro a
    rw [show (Expanded.market g bi si).ends (L.elementary.embedRecord a) =
      (L.elementary.ends a).map L.elementary.embedVertex from L.elementary.ends_embed a]
    ext v
    simp [Layout.elementary_vertex]
    rfl
  · intro v a b _ _ better
    apply (rank_lt_iff g bi si L.elementary v a b).mpr
    rw [Layout.elementary_vertex]
    exact better

end Kintali.ExactRecovery.Sparse
