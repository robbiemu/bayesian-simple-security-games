module

public import Kintali.QuoteSearch.Selection
public import Mathlib.Data.Nat.Size

/-!
# Weight updates and their sizes

Relate the compressed update to individual quote weights and to the
measured weight between its endpoints.
-/

@[expose] public section

namespace Kintali.QuoteSearch.Runs

def exponentAt (rs : List WeightRun) (j : ℕ) : ℕ :=
  ((expand rs)[j]?).getD 0

@[simp] theorem exponentAt_initial (quotes j : ℕ) :
    exponentAt (initial quotes) j = 0 := by
  simp only [exponentAt, expand_initial, List.getElem?_replicate]
  split <;> rfl

theorem exponentAt_doubleInterval (rs : List WeightRun) {lo hi j : ℕ}
    (hiCap : hi ≤ quoteCount rs) (hj : j < quoteCount rs) :
    exponentAt (doubleInterval lo hi rs) j =
      exponentAt rs j + (if lo ≤ j ∧ j < hi then 1 else 0) := by
  by_cases he : hi ≤ lo
  · have hOut : ¬(lo ≤ j ∧ j < hi) := by omega
    simp [doubleInterval, he, hOut]
  · have hh : lo ≤ hi := by omega
    unfold exponentAt
    rw [expand_doubleInterval lo hi rs hh]
    set xs := expand rs
    have hl : xs.length = quoteCount rs := expand_length rs
    have ht : (xs.take lo).length = lo := List.length_take_of_le (by omega)
    have hm : ((xs.drop lo).take (hi - lo)).length = hi - lo := by
      apply List.length_take_of_le
      rw [List.length_drop, hl]
      omega
    have hLeft : (xs.take lo ++ (((xs.drop lo).take (hi - lo)).map (· + 1))).length = hi := by
      rw [List.length_append, List.length_map, ht, hm]
      omega
    by_cases hBefore : j < lo
    · have hOut : ¬(lo ≤ j ∧ j < hi) := by omega
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
        List.getElem?_take_of_lt hBefore]
      simp [hOut]
    · by_cases hInside : j < hi
      · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega),
          ht, List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
        have hindex : lo + (j - lo) = j := by omega
        have hSome := List.getElem?_eq_getElem (l := xs) (i := j) (by omega)
        have hIn : lo ≤ j ∧ j < hi := ⟨Nat.le_of_not_lt hBefore, hInside⟩
        simp only [hindex, hSome, Option.map_some, Option.getD_some,
          ite_eq_left hIn]
      · rw [List.getElem?_append_right (by omega), hLeft, List.getElem?_drop]
        have hindex : hi + (j - hi) = j := by omega
        simp [hindex, hInside]

private theorem sum_raise (xs : List ℕ) :
    (xs.map fun e => 2 ^ (e + 1)).sum = 2 * (xs.map fun e => 2 ^ e).sum := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [pow_succ, Nat.mul_add, Nat.mul_comm (2 ^ e) 2]

/-- The update adds exactly the weight in its half-open interval. -/
theorem weight_doubleInterval (rs : List WeightRun) {lo hi : ℕ} (h : lo ≤ hi) :
    weight (doubleInterval lo hi rs) = weight rs + (prefixWeight rs hi - prefixWeight rs lo) := by
  rw [weight_eq_expand, expand_doubleInterval lo hi rs h]
  set xs := expand rs
  set before := xs.take lo
  set inside := (xs.drop lo).take (hi - lo)
  set after := xs.drop hi
  have hSplit : before ++ inside = xs.take hi := by
    have hl := List.take_append_drop lo (xs.take hi)
    rw [List.take_take, Nat.min_eq_left h, List.drop_take] at hl
    exact hl
  have hWhole : before ++ inside ++ after = xs := by
    rw [hSplit]
    exact List.take_append_drop hi xs
  have hPrefix := congrArg (fun l : List ℕ => (l.map fun e => 2 ^ e).sum) hSplit
  have hTotal := congrArg (fun l : List ℕ => (l.map fun e => 2 ^ e).sum) hWhole
  simp only [List.map_append, List.sum_append_nat] at hPrefix hTotal
  rw [weight_eq_expand]
  unfold prefixWeight
  change (List.map (fun e => 2 ^ e) (before ++ inside.map (· + 1) ++ after)).sum =
    (xs.map fun e => 2 ^ e).sum +
      (((xs.take hi).map fun e => 2 ^ e).sum - (before.map fun e => 2 ^ e).sum)
  simp only [List.map_append, List.map_map, List.sum_append_nat, Function.comp_def, sum_raise]
  omega

theorem expand_maxDoublings (interval : ℕ → ℕ × ℕ) (quotes t : ℕ) :
    ∀ e ∈ expand (afterUpdates interval quotes t), e ≤ t := by
  induction t with
  | zero =>
    intro e he
    have hz := List.eq_of_mem_replicate
      (by simpa [afterUpdates] using he : e ∈ List.replicate quotes 0)
    simp [hz]
  | succ t ih =>
    intro e he
    let lo := (interval t).1
    let hi := (interval t).2
    let old := afterUpdates interval quotes t
    by_cases h : hi ≤ lo
    · change e ∈ expand (doubleInterval lo hi old) at he
      have hOld : e ∈ expand old := by simpa [doubleInterval, h] using he
      exact (ih e hOld).trans (Nat.le_succ _)
    · change e ∈ expand (doubleInterval lo hi old) at he
      rw [expand_doubleInterval lo hi old (by omega)] at he
      rcases List.mem_append.mp he with hpre | hpost
      · rcases List.mem_append.mp hpre with hBefore | hInside
        · exact (ih e (List.mem_of_mem_take hBefore)).trans (Nat.le_succ _)
        · obtain ⟨x, hx, heq⟩ := List.mem_map.mp hInside
          rw [← heq]
          exact Nat.succ_le_succ (ih x (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
      · exact (ih e (List.mem_of_mem_drop hpost)).trans (Nat.le_succ _)

theorem weight_le_of_expand (rs : List WeightRun) (t : ℕ)
    (h : ∀ e ∈ expand rs, e ≤ t) : weight rs ≤ quoteCount rs * 2 ^ t := by
  rw [weight_eq_expand, ← expand_length]
  generalize expand rs = xs at h ⊢
  induction xs with
  | nil => simp
  | cons e es ih =>
    have he : 2 ^ e ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (h e (by simp))
    have hs := ih (fun f hf => h f (by simp [hf]))
    simpa [Nat.add_mul, Nat.add_comm] using Nat.add_le_add he hs

theorem afterUpdates_weight_size (interval : ℕ → ℕ × ℕ) (quotes t : ℕ) :
    (weight (afterUpdates interval quotes t)).size ≤ quotes.size + t := by
  have h := weight_le_of_expand _ t (expand_maxDoublings interval quotes t)
  rw [afterUpdates_quoteCount] at h
  apply Nat.size_le.mpr
  refine h.trans_lt ?_
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (Nat.pow_pos (by decide))

theorem exponentWeight_le (rs : List WeightRun) {j : ℕ} (hj : j < quoteCount rs) :
    2 ^ exponentAt rs j ≤ weight rs := by
  have hj' : j < (expand rs).length := by simpa using hj
  rw [exponentAt, List.getElem?_eq_getElem hj', Option.getD_some, weight_eq_expand]
  have hm : 2 ^ (expand rs)[j] ∈ (expand rs).map (fun e => 2 ^ e) :=
    List.mem_map.mpr ⟨_, List.getElem_mem hj', rfl⟩
  generalize (expand rs).map (fun e => 2 ^ e) = xs at hm ⊢
  generalize 2 ^ (expand rs)[j] = w at hm ⊢
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    rcases List.mem_cons.mp hm with he | hr
    · subst w
      simp
    · exact (ih hr).trans (Nat.le_add_left _ _)

end Kintali.QuoteSearch.Runs
