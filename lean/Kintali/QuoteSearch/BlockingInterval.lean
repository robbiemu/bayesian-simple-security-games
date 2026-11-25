module

public import Kintali.QuoteSearch.Algorithm
public import Kintali.QuoteSearch.PrefixSearch

/-!
# Exact intervals of blocking quotes

The buyer accepts a prefix and the site accepts a suffix of eligible
quotes. Binary search on each endpoint also handles equality at the
site cutoff. Every test is at one eligible quote index.
-/

@[expose] public section

namespace Kintali.QuoteSearch

def intervalFor (buyer site : ℕ → Bool) (eligible : ℕ) : Interval :=
  let lo := prefixLength (fun j => !(site j)) eligible
  let hi := prefixLength buyer eligible
  ⟨min lo hi, hi⟩

theorem intervalFor_spec (buyer site : ℕ → Bool) (eligible : ℕ)
    (buyer_prefix : ∀ a b, a ≤ b → b < eligible → buyer b = true → buyer a = true)
    (site_suffix : ∀ a b, a ≤ b → b < eligible → site a = true → site b = true) :
    let result := intervalFor buyer site eligible
    result.lo ≤ result.hi ∧ result.hi ≤ eligible ∧
      ∀ j < eligible, result.Contains j ↔ buyer j = true ∧ site j = true := by
  have hReject : ∀ a b, a ≤ b → b < eligible →
      (!(site b)) = true → (!(site a)) = true := by
    intro a b hab hb h
    cases ha : site a with
    | false => simp
    | true =>
      have hs := site_suffix a b hab hb ha
      simp [hs] at h
  obtain ⟨hbSize, hb⟩ := prefixLength_spec eligible buyer_prefix
  obtain ⟨_, hneg⟩ := prefixLength_spec eligible hReject
  let hi := prefixLength buyer eligible
  let lo := prefixLength (fun j => !(site j)) eligible
  have hSite (j : ℕ) (hj : j < eligible) : site j = true ↔ lo ≤ j := by
    have h := hneg j hj
    cases hs : site j with
    | false =>
      have hh : j < lo := h.mp (by simp [hs])
      constructor
      · intro bad
        cases bad
      · exact fun bound => (hh.not_ge bound).elim
    | true =>
      have bound : lo ≤ j := by
        by_contra! less
        have bad := h.mpr less
        simp [hs] at bad
      exact ⟨fun _ => bound, fun _ => rfl⟩
  refine ⟨Nat.min_le_right _ _, hbSize, ?_⟩
  intro j hj
  change (min lo hi ≤ j ∧ j < hi) ↔ _
  rw [hb j hj, hSite j hj]
  omega

end Kintali.QuoteSearch
