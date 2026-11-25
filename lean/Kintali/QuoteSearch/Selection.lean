module

public import Kintali.QuoteSearch.Runs
public import Kintali.QuoteSearch

/-!
# Selecting quantiles from compressed runs

The quantile index is the number of quotes strictly before the first
prefix that reaches its threshold. A scan skips an entire run at once.
-/

@[expose] public section

namespace Kintali.QuoteSearch.Runs

/-- Cumulative weight preceding quote `cut`, used in the specification. -/
def prefixWeight (rs : List WeightRun) (cut : ℕ) : ℕ :=
  (((expand rs).take cut).map fun e => 2 ^ e).sum

@[simp] theorem prefixWeight_zero (rs : List WeightRun) : prefixWeight rs 0 = 0 := by
  simp [prefixWeight]

theorem prefixWeight_cons (r : WeightRun) (rs : List WeightRun) (cut : ℕ) :
    prefixWeight (r :: rs) cut =
      min cut r.length * 2 ^ r.doublings + prefixWeight rs (cut - r.length) := by
  simp [prefixWeight, expand, List.take_append]

theorem prefixWeight_mono (rs : List WeightRun) {a b : ℕ} (hab : a ≤ b) :
    prefixWeight rs a ≤ prefixWeight rs b := by
  have h := List.take_append_drop a ((expand rs).take b)
  rw [List.take_take, Nat.min_eq_left hab] at h
  have hs := congrArg (fun l : List ℕ => (l.map fun e => 2 ^ e).sum) h
  simp only [List.map_append, List.sum_append_nat] at hs
  unfold prefixWeight
  omega

theorem prefixWeight_eq_weight (rs : List WeightRun) (cut : ℕ) (h : quoteCount rs ≤ cut) :
    prefixWeight rs cut = weight rs := by
  rw [prefixWeight, List.take_of_length_le (by simpa using h), weight_eq_expand]

theorem prefixWeight_le_weight (rs : List WeightRun) (cut : ℕ) :
    prefixWeight rs cut ≤ weight rs := by
  have hm := prefixWeight_mono rs (Nat.le_max_left cut (quoteCount rs))
  rwa [prefixWeight_eq_weight rs _ (Nat.le_max_right _ _)] at hm

/-- Ceiling division on a positive numerator. -/
def ceiling (n d : ℕ) : ℕ := (n - 1) / d + 1

private theorem ceiling_bounds {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (ceiling n d - 1) * d < n ∧ n ≤ ceiling n d * d := by
  have hFloor := Nat.div_mul_le_self (n - 1) d
  have hRem := Nat.mod_add_div (n - 1) d
  have hMod := Nat.mod_lt (n - 1) hd
  constructor
  · simp [ceiling]
    omega
  · simp only [ceiling, Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm ((n - 1) / d) d]
    omega

/-- Return the first prefix length at a positive threshold within the
total. The specification below supplies these conditions. -/
def firstPrefix (threshold : ℕ) : List WeightRun → ℕ
  | [] => 0
  | r :: rest =>
    let unit := 2 ^ r.doublings
    let w := r.length * unit
    if threshold ≤ w then ceiling threshold unit
    else r.length + firstPrefix (threshold - w) rest

theorem firstPrefix_spec (rs : List WeightRun) (threshold : ℕ)
    (hp : 0 < threshold) (ht : threshold ≤ weight rs) :
    let k := firstPrefix threshold rs
    0 < k ∧ k ≤ quoteCount rs ∧ prefixWeight rs (k - 1) < threshold ∧
      threshold ≤ prefixWeight rs k := by
  induction rs generalizing threshold with
  | nil => simp [weight] at ht; omega
  | cons r rs ih =>
    let unit : ℕ := 2 ^ r.doublings
    have hu : 0 < unit := Nat.pow_pos (by decide)
    change threshold ≤ r.length * unit + weight rs at ht
    by_cases hhead : threshold ≤ r.length * unit
    · let c := ceiling threshold unit
      have hFirst : firstPrefix threshold (r :: rs) = c := by
        change (if threshold ≤ r.length * unit then c else
          r.length + firstPrefix (threshold - r.length * unit) rs) = c
        exact ite_eq_left hhead
      dsimp only
      rw [hFirst]
      have hPos : 0 < c := Nat.zero_lt_succ _
      obtain ⟨hBefore, hThrough⟩ := ceiling_bounds hp hu
      have hWithin : c ≤ r.length := by
        by_contra! hn
        have h := Nat.mul_le_mul_right unit (show r.length ≤ c - 1 from by omega)
        exact hBefore.not_ge (hhead.trans h)
      have hPrev : c - 1 ≤ r.length := by omega
      have h₁ : prefixWeight (r :: rs) (c - 1) = (c - 1) * unit := by
        simp [prefixWeight_cons, unit, Nat.min_eq_left hPrev, Nat.sub_eq_zero_of_le hPrev]
      have h₂ : prefixWeight (r :: rs) c = c * unit := by
        simp [prefixWeight_cons, unit, Nat.min_eq_left hWithin, Nat.sub_eq_zero_of_le hWithin]
      exact ⟨hPos, hWithin.trans (Nat.le_add_right _ _),
        h₁.symm ▸ hBefore, h₂.symm ▸ hThrough⟩
    · let remaining := threshold - r.length * unit
      let k := firstPrefix remaining rs
      have hremain : 0 < remaining := by dsimp [remaining]; omega
      have hw : remaining ≤ weight rs := by dsimp [remaining]; omega
      obtain ⟨hk, hkRange, hBefore, hThrough⟩ := ih remaining hremain hw
      change 0 < k at hk
      change k ≤ quoteCount rs at hkRange
      change prefixWeight rs (k - 1) < remaining at hBefore
      change remaining ≤ prefixWeight rs k at hThrough
      have hFirst : firstPrefix threshold (r :: rs) = r.length + k := by
        change (if threshold ≤ r.length * unit then ceiling threshold unit else
          r.length + k) = r.length + k
        exact ite_eq_right hhead
      dsimp only
      rw [hFirst]
      have h₁ : prefixWeight (r :: rs) (r.length + k - 1) =
          r.length * unit + prefixWeight rs (k - 1) := by
        have hadd : r.length + k - 1 = r.length + (k - 1) := by omega
        rw [hadd, prefixWeight_cons, Nat.min_eq_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      have h₂ : prefixWeight (r :: rs) (r.length + k) =
          r.length * unit + prefixWeight rs k := by
        rw [prefixWeight_cons, Nat.min_eq_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      refine ⟨by omega, Nat.add_le_add_left hkRange r.length, ?_, ?_⟩
      · rw [h₁]
        dsimp only [remaining] at hBefore
        omega
      · rw [h₂]
        dsimp only [remaining] at hThrough
        omega

/-- The selected zero-based quote for a threshold `sV/J`. -/
def quantile (rs : List WeightRun) (J s : ℕ) : ℕ :=
  firstPrefix (ceiling (s * weight rs) J) rs - 1

theorem quantile_spec (rs : List WeightRun) {J s : ℕ}
    (hs : 0 < s) (hsJ : s < J) (hV : 0 < weight rs) :
    let q := quantile rs J s
    q < quoteCount rs ∧ J * prefixWeight rs q < s * weight rs ∧
      s * weight rs ≤ J * prefixWeight rs (q + 1) := by
  let n := s * weight rs
  let threshold := ceiling n J
  have ht : 0 < threshold := Nat.zero_lt_succ _
  obtain ⟨hBefore, hThrough⟩ :=
    ceiling_bounds (Nat.mul_pos hs hV) (Nat.zero_lt_of_lt hsJ)
  have hLimit : threshold ≤ weight rs := by
    by_contra! hn
    have hMul := Nat.mul_le_mul_right J (show weight rs ≤ threshold - 1 from by omega)
    have hnV : n ≤ weight rs * J := by rw [Nat.mul_comm (weight rs) J]; exact Nat.mul_le_mul_right _ hsJ.le
    exact (not_lt_of_ge (hnV.trans hMul)) hBefore
  let k := firstPrefix threshold rs
  obtain ⟨hk, hkRange, hkBefore, hkThrough⟩ := firstPrefix_spec rs threshold ht hLimit
  change 0 < k at hk
  change k ≤ quoteCount rs at hkRange
  change prefixWeight rs (k - 1) < threshold at hkBefore
  change threshold ≤ prefixWeight rs k at hkThrough
  change k - 1 < quoteCount rs ∧ J * prefixWeight rs (k - 1) < n ∧
    n ≤ J * prefixWeight rs (k - 1 + 1)
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.mul_comm J]
    exact (Nat.mul_le_mul_right J (show prefixWeight rs (k - 1) ≤ threshold - 1 from by omega)).trans_lt
      hBefore
  · rw [show k - 1 + 1 = k from by omega, Nat.mul_comm J]
    exact hThrough.trans (Nat.mul_le_mul_right J hkThrough)

/-- Retain at most `J-1` optional quotes per pair. An empty prefix has
no quantiles. Repeated indices can be deduplicated by the caller. -/
def selected (rs : List WeightRun) (J : ℕ) : List ℕ :=
  if weight rs = 0 then []
  else (List.range (J - 1)).map fun a => quantile rs J (a + 1)

theorem selected_count (rs : List WeightRun) (J : ℕ) : (selected rs J).length ≤ J - 1 := by
  unfold selected
  split <;> simp

theorem quantile_mem_selected (rs : List WeightRun) {J s : ℕ}
    (hV : 0 < weight rs) (hs : 0 < s) (hsJ : s < J) :
    quantile rs J s ∈ selected rs J := by
  simp only [selected, ite_eq_right (Nat.ne_of_gt hV), List.mem_map, List.mem_range]
  exact ⟨s - 1, by omega, by rw [show s - 1 + 1 = s from by omega]⟩

/-- The cumulative weight between the ends of an interval missing all
selected quotes is at most the allowed share. -/
theorem selected_interval_bound (rs : List WeightRun) (J lo hi : ℕ) (hlo : lo ≤ hi)
    (hMiss : ∀ q ∈ selected rs J, ¬(lo ≤ q ∧ q < hi)) :
    J * (prefixWeight rs hi - prefixWeight rs lo) ≤ weight rs := by
  apply unmarked_interval_bound (prefixWeight_mono rs hlo) (prefixWeight_le_weight rs hi)
  intro s hs hsJ
  by_cases hV : weight rs = 0
  · simp [hV]
  · have hPos := Nat.pos_of_ne_zero hV
    obtain ⟨_, hBefore, hThrough⟩ := quantile_spec rs hs hsJ hPos
    have hOut := hMiss (quantile rs J s) (quantile_mem_selected rs hPos hs hsJ)
    by_cases hleft : quantile rs J s < lo
    · exact Or.inl (hThrough.trans (Nat.mul_le_mul_left J
        (prefixWeight_mono rs (by omega))))
    · have hright : hi ≤ quantile rs J s := by
        by_contra! hn
        exact hOut ⟨Nat.le_of_not_gt hleft, hn⟩
      exact Or.inr ((Nat.mul_le_mul_left J (prefixWeight_mono rs hright)).trans_lt hBefore)

end Kintali.QuoteSearch.Runs
