module

public import Kintali.QuotaSweep.GraphCycle
import Mathlib.Tactic.Linarith

/-!
# First exhaustion or the upper pressure

The smallest strictly positive ratio of a worst holding to its release rate
is an exhaustion time. In an acyclic graph the remaining pressure interval
is also a candidate. Internal and simultaneous events obey one strict
cardinality decrease.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] (K : Book B S E)

def speed (x : Record B S E → ℚ) : ℚ := if K.hasCycle x then 0 else 1

def through (x : Record B S E → ℚ) (rate : S → ℚ) (v : Vertex B S) : ℚ :=
  if K.hasCycle x then K.aroundCycle x v
  else Routing.pathRate (K.next x) (injection rate) v

theorem through_nonneg {rate : S → ℚ} (hr : ∀ s, 0 ≤ rate s) (x : Record B S E → ℚ)
    (v : Vertex B S) : 0 ≤ K.through x rate v := by
  unfold through
  split
  · rcases K.aroundCycle_zero_or_one x v with h | h <;> simp [h]
  · exact Routing.path_nonneg (fun u => by cases u <;> simp [injection, hr]) v

theorem through_conservation (x : Record B S E → ℚ) (rate : S → ℚ) (v : Vertex B S) :
    K.through x rate v = K.speed x * injection rate v +
      Routing.incoming (K.next x) (K.through x rate) v := by
  by_cases h : K.hasCycle x = true
  · have he : K.through x rate = K.aroundCycle x := funext fun z => by simp [through, h]
    simpa [he, speed, h] using (K.aroundCycle_conservation x v).symm
  · have h' := K.no_cyclic_vertex h
    have he : K.through x rate = Routing.pathRate (K.next x) (injection rate) :=
      funext fun z => by simp [through, h]
    simpa [he, speed, h] using Routing.path_conservation h' (injection rate) v

theorem cycle_buyer {x : Record B S E → ℚ} (hc : K.hasCycle x = true) (rate : S → ℚ) :
    ∃ b, 0 < K.through x rate (.inl b) := by
  obtain ⟨b, hb⟩ := K.aroundCycle_seed hc
  exact ⟨b, by simp [through, hc, hb]⟩

/-- Even a book with zero-mass dummy buyers works. Positive release flow at
a buyer comes from an ordinary proposal that the buyer accepts. -/
theorem worst_positive_of_flow {x : Record B S E → ℚ} {rate : S → ℚ}
    (hr : ∀ s, 0 ≤ rate s) {b : B} (hb : 0 < K.through x rate (.inl b)) :
    0 < x (K.worst x b) := by
  have hflow := K.through_conservation x rate (.inl b)
  simp [injection, Routing.incoming, Fintype.sum_sum_type] at hflow
  rw [hflow] at hb
  obtain ⟨s, _, hs⟩ := (Finset.sum_pos_iff_of_nonneg (fun s _ => by
    split <;> simp [K.through_nonneg hr])).mp hb
  by_cases hn : K.next x (.inr s) = some (.inl b)
  · obtain ⟨e, he, _, hp⟩ := K.buyer_accepts_proposal ((K.incoming_at_buyer x s b).mp hn)
    exact (K.mem_holdings.mp (K.worst_mem (K.mem_holdings.mpr ⟨he, hp⟩))).2
  · simp [hn] at hs

def exhaustions (x : Record B S E → ℚ) (rate : S → ℚ) : Finset ℚ :=
  (Finset.univ.filter fun b => 0 < K.through x rate (.inl b)).image
    (fun b => x (K.worst x b) / K.through x rate (.inl b))

@[simp] theorem mem_exhaustions {x : Record B S E → ℚ} {rate : S → ℚ} {d : ℚ} :
    d ∈ K.exhaustions x rate ↔ ∃ b, 0 < K.through x rate (.inl b) ∧
      x (K.worst x b) / K.through x rate (.inl b) = d := by
  simp [exhaustions]

def times (x : Record B S E → ℚ) (rate : S → ℚ) (t upper : ℚ) : Finset ℚ :=
  if K.hasCycle x then K.exhaustions x rate else insert (upper - t) (K.exhaustions x rate)

theorem times_nonempty (x : Record B S E → ℚ) (rate : S → ℚ) (t upper : ℚ) :
    (K.times x rate t upper).Nonempty := by
  by_cases hc : K.hasCycle x = true
  · obtain ⟨b, hb⟩ := K.cycle_buyer hc rate
    refine ⟨x (K.worst x b) / K.through x rate (.inl b), ?_⟩
    simpa only [times, hc, ↓reduceIte, K.mem_exhaustions] using
      (show ∃ c, 0 < K.through x rate (.inl c) ∧
        x (K.worst x c) / K.through x rate (.inl c) =
          x (K.worst x b) / K.through x rate (.inl b) from ⟨b, hb, rfl⟩)
  · simp [times, hc]

/-- Exact end of the current graph stage, before applying a budget stop. -/
def duration (x : Record B S E → ℚ) (rate : S → ℚ) (t upper : ℚ) : ℚ :=
  (K.times x rate t upper).min' (K.times_nonempty x rate t upper)

theorem duration_mem (x : Record B S E → ℚ) (rate : S → ℚ) (t upper : ℚ) :
    K.duration x rate t upper ∈ K.times x rate t upper :=
  Finset.min'_mem _ _

theorem duration_pos {x : Record B S E → ℚ} {rate : S → ℚ} {t upper : ℚ}
    (hw : ∀ b, 0 < K.through x rate (.inl b) → 0 < x (K.worst x b)) (ht : t < upper) :
    0 < K.duration x rate t upper := by
  have hp {d : ℚ} (hd : d ∈ K.exhaustions x rate) : 0 < d := by
    obtain ⟨b, hb, rfl⟩ := K.mem_exhaustions.mp hd
    exact div_pos (hw b hb) hb
  have hd := K.duration_mem x rate t upper
  by_cases hc : K.hasCycle x = true
  · exact hp (by simpa [times, hc] using hd)
  · simp only [times, Bool.not_eq_true _ |>.mp hc, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert] at hd
    exact hd.elim (fun h => h ▸ sub_pos.mpr ht) hp

theorem no_overdraft {x : Record B S E → ℚ} {rate : S → ℚ} {t upper δ : ℚ}
    (hx : ∀ e, 0 ≤ x e) (hr : ∀ s, 0 ≤ rate s) (hδ : δ ≤ K.duration x rate t upper) (b : B) :
    δ * K.through x rate (.inl b) ≤ x (K.worst x b) := by
  by_cases hb : 0 < K.through x rate (.inl b)
  · apply (le_div_iff₀ hb).mp
    apply hδ.trans (Finset.min'_le _ _ ?_)
    have hm := K.mem_exhaustions.mpr (show ∃ c, 0 < K.through x rate (.inl c) ∧
      x (K.worst x c) / K.through x rate (.inl c) =
        x (K.worst x b) / K.through x rate (.inl b) from ⟨b, hb, rfl⟩)
    by_cases hc : K.hasCycle x = true <;> simp [times, hc, hm]
  · rw [le_antisymm (le_of_not_gt hb) (K.through_nonneg hr x (.inl b)), mul_zero]
    exact hx _

theorem pressure_le_upper {x : Record B S E → ℚ} {rate : S → ℚ} {t upper : ℚ}
    (ht : t ≤ upper) :
    t + K.duration x rate t upper * K.speed x ≤ upper := by
  by_cases hc : K.hasCycle x = true
  · simpa [speed, hc] using ht
  · have h : K.duration x rate t upper ≤ upper - t :=
      Finset.min'_le _ _ (by simp [times, hc])
    simpa [speed, hc] using (by linarith : t + K.duration x rate t upper ≤ upper)

theorem upper_or_exhaustion (x : Record B S E → ℚ) (rate : S → ℚ) (t upper : ℚ) :
    t + K.duration x rate t upper * K.speed x = upper ∨
    ∃ b, 0 < K.through x rate (.inl b) ∧
      K.move x (K.through x rate) (K.duration x rate t upper) (K.worst x b) = 0 := by
  let δ := K.duration x rate t upper
  have exhaustion (he : δ ∈ K.exhaustions x rate) :
      ∃ b, 0 < K.through x rate (.inl b) ∧ K.move x (K.through x rate) δ (K.worst x b) = 0 := by
    obtain ⟨b, hb, hδ⟩ := K.mem_exhaustions.mp he
    exact ⟨b, hb, by simp [← hδ, hb.ne']⟩
  have hd : δ ∈ K.times x rate t upper := K.duration_mem x rate t upper
  by_cases hc : K.hasCycle x = true
  · exact Or.inr (exhaustion (by simpa [times, hc] using hd))
  · simp only [times, Bool.not_eq_true _ |>.mp hc, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert] at hd
    rcases hd with h | he
    · exact Or.inl (by change t + δ * K.speed x = upper; simp [h, speed, hc])
    · exact Or.inr (exhaustion he)

theorem stable_segment [Fintype E] {x : Record B S E → ℚ} {rate : S → ℚ} {mass : B → ℚ}
    {t upper δ : ℚ} (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x)
    (hr : ∀ s, 0 ≤ rate s) (hδ : 0 ≤ δ) (hle : δ ≤ K.duration x rate t upper) :
    K.market.StableOn K.retainedRecords (quota rate mass (t + δ * K.speed x))
      (K.move x (K.through x rate) δ) :=
  K.stable_move hx (K.through_nonneg hr x) hδ (K.no_overdraft hx.nonneg hr hle)
    (K.through_conservation x rate)

end Kintali.QuotaSweep.Book
