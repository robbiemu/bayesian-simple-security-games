module

public import Kintali.QuotaSweep.Rates

/-!
# Zero extension from an explicitly listed restriction

Use one record type for the sparse executable and another for the full
grid market in the comparison proof. An injection preserving incident
endpoints and their strict orders embeds every retained record. All records
outside the image receive zero mass.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Restriction

variable {V A R : Type*} [DecidableEq V] [DecidableEq A] [DecidableEq R] [Fintype A]

def extend (i : A ↪ R) (x : A → ℚ) (r : R) : ℚ :=
  ∑ a, if i a = r then x a else 0

@[simp] theorem extend_image (i : A ↪ R) (x : A → ℚ) (a : A) :
    extend i x (i a) = x a := by
  simp [extend, i.injective.eq_iff]

omit [DecidableEq A] in
theorem extend_zero {i : A ↪ R} (x : A → ℚ) {r : R} (h : ∀ a, i a ≠ r) :
    extend i x r = 0 := by simp [extend, h]

theorem positive_image {i : A ↪ R} {x : A → ℚ} {r : R} (h : 0 < extend i x r) :
    ∃ a, i a = r ∧ 0 < x a := by
  by_cases hm : ∃ a, i a = r
  · obtain ⟨a, rfl⟩ := hm
    exact ⟨a, rfl, by simpa using h⟩
  · have hz := extend_zero x (fun a ha => hm ⟨a, ha⟩)
    simp [hz] at h

/-- Lift a stable restricted allocation into the same restriction expressed
inside the larger grid. This conclusion concerns the retained image bids. -/
theorem stable_extend [Fintype R] {small : Market V A} {big : Market V R}
    (i : A ↪ R) (ends : ∀ a, big.ends (i a) = small.ends a)
    (rank : ∀ v a b, v ∈ small.ends a → v ∈ small.ends b →
      big.rank v (i a) < big.rank v (i b) → small.rank v a < small.rank v b)
    {retained : Finset A} {q : V → ℚ} {x : A → ℚ} (hx : small.StableOn retained q x) :
    big.StableOn (retained.map i) q (extend i x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r
    exact Finset.sum_nonneg fun _ _ => by split; exact hx.nonneg _; exact le_rfl
  · intro v
    unfold extend
    rw [Book.sum_assign]
    simpa only [ends] using hx.balance v
  · intro r hcard hpos
    obtain ⟨a, rfl, ha⟩ := positive_image hpos
    exact Finset.mem_map.mpr ⟨a, hx.support a (by simpa only [ends] using hcard) ha, rfl⟩
  · intro r hr hblock
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hr
    apply hx.stable a ha
    refine ⟨by simpa only [ends] using hblock.1, ?_⟩
    intro v hv
    obtain ⟨s, hs, hlt, hp⟩ := hblock.2 v (by simpa only [ends] using hv)
    obtain ⟨b, rfl, hb⟩ := positive_image hp
    rw [ends] at hs
    exact ⟨b, hs, rank v a b hv hs hlt, hb⟩

end Kintali.QuotaSweep.Restriction
