module

public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.Ring.Pow

/-!
# Compressed quote weights

A run stores the length of an interval of quotes and the common number
of doublings. The algorithm scans runs. Expansion is used to state
what the compressed operations compute.
-/

@[expose] public section

namespace Kintali.QuoteSearch

/-- Every quote in this run has weight `2 ^ doublings`. -/
structure WeightRun where
  length : ℕ
  doublings : ℕ
  deriving DecidableEq, Repr

namespace Runs

def initial (quotes : ℕ) : List WeightRun :=
  if quotes = 0 then [] else [⟨quotes, 0⟩]

def quoteCount : List WeightRun → ℕ
  | [] => 0
  | r :: rs => r.length + quoteCount rs

def weight : List WeightRun → ℕ
  | [] => 0
  | r :: rs => r.length * 2 ^ r.doublings + weight rs

/-- The reference list of exponents, with one entry per eligible quote. -/
def expand : List WeightRun → List ℕ
  | [] => []
  | r :: rs => List.replicate r.length r.doublings ++ expand rs

@[simp] theorem expand_append (a b : List WeightRun) :
    expand (a ++ b) = expand a ++ expand b := by
  induction a with
  | nil => simp [expand]
  | cons r rs ih => simp [expand, ih, List.append_assoc]

@[simp] theorem expand_initial (n : ℕ) : expand (initial n) = List.replicate n 0 := by
  by_cases h : n = 0 <;> simp [initial, expand, h]

@[simp] theorem expand_length (rs : List WeightRun) : (expand rs).length = quoteCount rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [expand, quoteCount, ih]

theorem weight_eq_expand (rs : List WeightRun) :
    weight rs = ((expand rs).map fun e => 2 ^ e).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [weight, expand, ih]

/-- Split at a prefix length without expanding any quote. A split
inside a run creates one additional run. -/
def splitAt (cut : ℕ) (rs : List WeightRun) : List WeightRun × List WeightRun :=
  match rs with
  | [] => ([], [])
  | r :: tail =>
    if cut = 0 then ([], rs)
    else if cut < r.length then ([⟨cut, r.doublings⟩], ⟨r.length - cut, r.doublings⟩ :: tail)
    else
      let (before, after) := splitAt (cut - r.length) tail
      (r :: before, after)

theorem expand_splitAt (cut : ℕ) (rs : List WeightRun) :
    (expand (splitAt cut rs).1, expand (splitAt cut rs).2) =
      ((expand rs).take cut, (expand rs).drop cut) := by
  induction rs generalizing cut with
  | nil => simp [splitAt, expand]
  | cons r tail ih =>
    by_cases hzero : cut = 0
    · simp [hzero, splitAt, expand]
    by_cases hcut : cut < r.length
    · simp [splitAt, hzero, hcut, expand, List.take_append, List.drop_append,
        Nat.min_eq_left hcut.le, Nat.sub_eq_zero_of_le hcut.le]
    · have ht := ih (cut - r.length)
      have hp : expand (splitAt (cut - r.length) tail).1 = (expand tail).take (cut - r.length) :=
        congrArg Prod.fst ht
      have hs : expand (splitAt (cut - r.length) tail).2 = (expand tail).drop (cut - r.length) :=
        congrArg Prod.snd ht
      have hle : r.length ≤ cut := Nat.le_of_not_gt hcut
      simp [splitAt, hzero, hcut, expand, List.take_append, List.drop_append,
        hp, hs, Nat.min_eq_right hle, Nat.sub_eq_zero_of_le hle]

theorem splitAt_count (cut : ℕ) (rs : List WeightRun) :
    (splitAt cut rs).1.length + (splitAt cut rs).2.length ≤ rs.length + 1 := by
  induction rs generalizing cut with
  | nil => simp [splitAt]
  | cons r tail ih =>
    by_cases hzero : cut = 0
    · simp [splitAt, hzero]
    by_cases hcut : cut < r.length
    · simp [splitAt, hzero, hcut]
      omega
    · have h := ih (cut - r.length)
      rcases hs : splitAt (cut - r.length) tail with ⟨before, after⟩
      simp only [hs, splitAt, ite_eq_right hzero, ite_eq_right hcut, List.length_cons] at h ⊢
      omega

def raise (rs : List WeightRun) : List WeightRun :=
  rs.map fun r => {r with doublings := r.doublings + 1}

@[simp] theorem expand_raise (rs : List WeightRun) :
    expand (raise rs) = (expand rs).map (· + 1) := by
  induction rs with
  | nil => rfl
  | cons r tail ih =>
    simp only [raise] at ih
    simp [raise, expand, ih]

/-- Double weights at the half-open interval `[lo, hi)`. -/
def doubleInterval (lo hi : ℕ) (rs : List WeightRun) : List WeightRun :=
  if hi ≤ lo then rs else
    let (before, rest) := splitAt lo rs
    let (inside, after) := splitAt (hi - lo) rest
    before ++ raise inside ++ after

theorem expand_doubleInterval (lo hi : ℕ) (rs : List WeightRun) (h : lo ≤ hi) :
    expand (doubleInterval lo hi rs) =
      (expand rs).take lo ++ (((expand rs).drop lo).take (hi - lo)).map (· + 1) ++
        (expand rs).drop hi := by
  rcases eq_or_lt_of_le h with heq | hlt
  · subst hi
    simp [doubleInterval]
  · have h₁ := expand_splitAt lo rs
    rcases ha : splitAt lo rs with ⟨before, rest⟩
    have h₂ := expand_splitAt (hi - lo) rest
    rcases hb : splitAt (hi - lo) rest with ⟨inside, after⟩
    simp only [ha, hb, Prod.mk.injEq] at h₁ h₂
    have hadd : lo + (hi - lo) = hi := by omega
    simp [doubleInterval, not_le.mpr hlt, ha, hb, h₁.1, h₁.2, h₂.1, h₂.2,
      List.drop_drop, hadd]

theorem doubleInterval_count (lo hi : ℕ) (rs : List WeightRun) :
    (doubleInterval lo hi rs).length ≤ rs.length + 2 := by
  by_cases h : hi ≤ lo
  · simp [doubleInterval, h]
  · have h₁ := splitAt_count lo rs
    rcases ha : splitAt lo rs with ⟨before, rest⟩
    have h₂ := splitAt_count (hi - lo) rest
    rcases hb : splitAt (hi - lo) rest with ⟨inside, after⟩
    simp only [ha, hb] at h₁ h₂
    simp [doubleInterval, h, ha, hb, raise]
    omega

theorem doubleInterval_quoteCount (lo hi : ℕ) (rs : List WeightRun) :
    quoteCount (doubleInterval lo hi rs) = quoteCount rs := by
  by_cases h : hi ≤ lo
  · simp [doubleInterval, h]
  · have hlt := Nat.lt_of_not_ge h
    rw [← expand_length, ← expand_length, expand_doubleInterval lo hi rs hlt.le]
    have hslice := congrArg List.length (List.take_append_drop (hi - lo) ((expand rs).drop lo))
    have hrest := congrArg List.length (List.take_append_drop lo (expand rs))
    have hadd : lo + (hi - lo) = hi := by omega
    simp only [List.length_append, List.length_map, List.drop_drop, hadd]
      at hslice hrest ⊢
    omega

/-- Over `T` updates the representation grows by at most two runs
per step, independently of the number of quotes. -/
def afterUpdates (interval : ℕ → ℕ × ℕ) (quotes : ℕ) : ℕ → List WeightRun
  | 0 => initial quotes
  | t + 1 => doubleInterval (interval t).1 (interval t).2 (afterUpdates interval quotes t)

theorem afterUpdates_count (interval : ℕ → ℕ × ℕ) (quotes T : ℕ) :
    (afterUpdates interval quotes T).length ≤ 1 + 2 * T := by
  induction T with
  | zero => by_cases h : quotes = 0 <;> simp [afterUpdates, initial, h]
  | succ t ih =>
    have h := doubleInterval_count (interval t).1 (interval t).2 (afterUpdates interval quotes t)
    simp only [afterUpdates]
    omega

@[simp] theorem afterUpdates_quoteCount (interval : ℕ → ℕ × ℕ) (quotes T : ℕ) :
    quoteCount (afterUpdates interval quotes T) = quotes := by
  induction T with
  | zero => by_cases h : quotes = 0 <;> simp [afterUpdates, initial, h, quoteCount]
  | succ t ih => rw [afterUpdates, doubleInterval_quoteCount, ih]

end Runs
end Kintali.QuoteSearch
