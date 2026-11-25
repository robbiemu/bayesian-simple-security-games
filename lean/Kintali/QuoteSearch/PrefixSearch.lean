module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# Finding eligible and accepted prefixes

An exact comparison oracle on quote indices is enough. The count
returned by this search is the first rejected index, with the end of
the list serving as a sentinel.
-/

@[expose] public section

namespace Kintali.QuoteSearch

/-- Bounded binary search on a closed interval of possible prefix lengths. -/
def locate (accepts : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo then lo else
      let mid := lo + (hi - lo) / 2
      if accepts mid then locate accepts fuel (mid + 1) hi
      else locate accepts fuel lo mid

def prefixLength (accepts : ℕ → Bool) (quotes : ℕ) : ℕ :=
  locate accepts (quotes.log2 + 1) 0 quotes

private theorem locate_eq {accepts : ℕ → Bool} {n k lo hi fuel : ℕ}
    (hCut : ∀ i < n, accepts i = true ↔ i < k)
    (hlo : lo ≤ k) (hhi : k ≤ hi) (hn : hi ≤ n) (hWidth : hi - lo < 2 ^ fuel) :
    locate accepts fuel lo hi = k := by
  induction fuel generalizing lo hi with
  | zero =>
    simp only [locate]
    simp only [pow_zero] at hWidth
    omega
  | succ t ih =>
    by_cases hStop : hi ≤ lo
    · rw [locate, ite_eq_left hStop]
      omega
    · let mid := lo + (hi - lo) / 2
      have hmn : mid < n := by dsimp [mid]; omega
      have hml : lo ≤ mid := by dsimp [mid]; omega
      have hmh : mid < hi := by dsimp [mid]; omega
      rw [pow_succ] at hWidth
      have hleft : mid - lo < 2 ^ t := by dsimp [mid]; omega
      have hright : hi - (mid + 1) < 2 ^ t := by dsimp [mid]; omega
      rw [locate, ite_eq_right hStop]
      change (if accepts mid then locate accepts t (mid + 1) hi
        else locate accepts t lo mid) = k
      cases he : accepts mid
      · have hk : k ≤ mid := by
          by_contra! hlt
          have htrue := (hCut mid hmn).mpr hlt
          simp [he] at htrue
        simp only [Bool.false_eq_true, ite_false]
        exact ih hlo hk (hmh.le.trans hn) hleft
      · have hk : mid < k := (hCut mid hmn).mp he
        simp only [ite_true]
        exact ih hk hhi hn hright

theorem prefixLength_eq {accepts : ℕ → Bool} {quotes k : ℕ} (hk : k ≤ quotes)
    (hCut : ∀ i < quotes, accepts i = true ↔ i < k) :
    prefixLength accepts quotes = k :=
  locate_eq hCut (Nat.zero_le k) hk (Nat.le_refl _) Nat.lt_log2_self

/-- If acceptance is prefix-closed, the executable search yields its
entire prefix. The search performs at most `quotes.log2 + 1` oracle
comparisons. -/
theorem prefixLength_spec {accepts : ℕ → Bool} (quotes : ℕ)
    (hClosed : ∀ a b, a ≤ b → b < quotes → accepts b = true → accepts a = true) :
    prefixLength accepts quotes ≤ quotes ∧
      ∀ i < quotes, accepts i = true ↔ i < prefixLength accepts quotes := by
  let existsStop : ∃ i, quotes ≤ i ∨ accepts i = false := ⟨quotes, Or.inl (Nat.le_refl _)⟩
  let k := Nat.find existsStop
  have hk : k ≤ quotes := Nat.find_min' existsStop (Or.inl (Nat.le_refl _))
  have hCut (i : ℕ) (hi : i < quotes) : accepts i = true ↔ i < k := by
    constructor
    · intro ht
      by_contra! hki
      have hfalse : accepts k = false :=
        (Nat.find_spec existsStop).resolve_left (by omega)
      have htrue := hClosed k i hki hi ht
      simp [hfalse] at htrue
    · intro hlt
      have hno := Nat.find_min existsStop hlt
      cases he : accepts i
      · exact (hno (Or.inr he)).elim
      · rfl
  rw [prefixLength_eq hk hCut]
  exact ⟨hk, hCut⟩

/-- The intersection of a buyer's accepted prefix and a site's
accepted suffix is the interval used for a doubling. If they are
disjoint the interval is empty. -/
theorem accepted_interval {buyer site : ℕ → Bool} {quotes stop start : ℕ}
    (hBuyer : ∀ i < quotes, buyer i = true ↔ i < stop)
    (hSite : ∀ i < quotes, site i = true ↔ start ≤ i)
    {i : ℕ} (hi : i < quotes) :
    (buyer i = true ∧ site i = true) ↔ start ≤ i ∧ i < stop := by
  rw [hBuyer i hi, hSite i hi, and_comm]

end Kintali.QuoteSearch
