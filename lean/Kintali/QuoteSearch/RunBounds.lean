module

public import Kintali.QuoteSearch.TraceBounds

/-! # Individual words of the compressed search state -/

@[expose] public section

namespace Kintali.QuoteSearch

namespace Runs

theorem length_le_count {rs : List WeightRun} {r : WeightRun} (h : r ∈ rs) :
    r.length ≤ quoteCount rs := by
  induction rs with
  | nil => simp at h
  | cons a as ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

theorem splitAt_exponents (rs : List WeightRun) (cut t : ℕ)
    (h : ∀ r ∈ rs, r.doublings ≤ t) :
    (∀ a ∈ (splitAt cut rs).1, a.doublings ≤ t) ∧
      ∀ a ∈ (splitAt cut rs).2, a.doublings ≤ t := by
  induction rs generalizing cut with
  | nil => simp [splitAt]
  | cons r rs ih =>
    have hr := h r (by simp)
    have hs : ∀ a ∈ rs, a.doublings ≤ t := fun a ha => h a (by simp [ha])
    by_cases hz : cut = 0
    · simpa [splitAt, hz, hr] using hs
    by_cases hc : cut < r.length
    · simpa [splitAt, hz, hc, hr] using hs
    · obtain ⟨fst, snd⟩ := ih (cut - r.length) hs
      simpa [splitAt, hz, hc, hr] using And.intro fst snd

theorem doubleInterval_exponents (rs : List WeightRun) (lo hi t : ℕ)
    (h : ∀ r ∈ rs, r.doublings ≤ t) :
    ∀ r ∈ doubleInterval lo hi rs, r.doublings ≤ t + 1 := by
  by_cases stop : hi ≤ lo
  · simpa [doubleInterval, stop] using fun r hr => (h r hr).trans (Nat.le_succ _)
  obtain ⟨a, b⟩ := splitAt_exponents rs lo t h
  obtain ⟨c, d⟩ := splitAt_exponents _ (hi-lo) t b
  intro r hr
  simp only [doubleInterval, ite_eq_right stop, List.append_assoc, List.mem_append] at hr
  rcases hr with before | inside | after
  · exact (a r before).trans (Nat.le_succ _)
  · obtain ⟨s, hs, eq⟩ := List.mem_map.mp inside
    rw [← eq]
    exact Nat.succ_le_succ (c s hs)
  · exact (d r after).trans (Nat.le_succ _)

theorem afterUpdates_exponents (interval : ℕ → ℕ × ℕ) (quotes t : ℕ) :
    ∀ r ∈ afterUpdates interval quotes t, r.doublings ≤ t := by
  induction t with
  | zero => by_cases h : quotes = 0 <;> simp [afterUpdates, initial, h]
  | succ t ih => exact doubleInterval_exponents _ _ _ _ ih

end Runs

variable {pairs : ℕ} {Answer : Type*}

theorem runExponent_bound (J : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (p : Fin pairs) (t : ℕ) (r : WeightRun)
    (hr : r ∈ (stateAt J trial (initialTable quotes) t)[p]) : r.doublings ≤ t := by
  rw [stateAt_runs] at hr
  exact Runs.afterUpdates_exponents _ _ _ _ hr

theorem runLength_bound (J : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (p : Fin pairs) (t : ℕ) (r : WeightRun)
    (hr : r ∈ (stateAt J trial (initialTable quotes) t)[p]) : r.length ≤ quotes[p] := by
  rw [← stateAt_count J trial quotes t p]
  exact Runs.length_le_count hr

end Kintali.QuoteSearch
