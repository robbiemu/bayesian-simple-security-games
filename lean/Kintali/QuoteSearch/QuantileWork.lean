module

public import Kintali.QuoteSearch.RunBounds
public import Kintali.LinearProgramming.ScalarRun

/-! # Selecting one weighted quantile in indexed binary words -/

@[expose] public section

namespace Kintali.QuoteSearch.Runs

open StochasticGames.CompilerRun StochasticGames.BinarySize
open Kintali.LinearProgramming.ScalarRun

def runWeight (r : WeightRun) : Run ℕ := do
  let unit ← power 2 r.doublings
  natMul r.length unit

@[simp] theorem runWeight_value (r : WeightRun) :
    (runWeight r).value = r.length * 2 ^ r.doublings := by simp [runWeight, natMul]

def totalWork : List WeightRun → Run ℕ
  | [] => step 0 0
  | r :: rs => do
    let w ← runWeight r
    let v ← totalWork rs
    let _ ← step 0 ()
    natAdd w v

@[simp] theorem totalWork_value (rs : List WeightRun) :
    (totalWork rs).value = weight rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [totalWork, natAdd, weight, ih]

def ceilingWork (n d : ℕ) : Run ℕ := do
  let t ← natSub n 1
  let q ← step (max t.size d.size) (t / d)
  natAdd q 1

@[simp] theorem ceilingWork_value (n d : ℕ) :
    (ceilingWork n d).value = ceiling n d := by
  simp [ceilingWork, ceiling, natSub, natAdd]

def seekWork (threshold : ℕ) : List WeightRun → Run ℕ
  | [] => step 0 0
  | r :: rs => do
    let unit ← power 2 r.doublings
    let w ← natMul r.length unit
    let first ← step (max threshold.size w.size) (threshold ≤ w : Bool)
    if first then ceilingWork threshold unit else
      let rest ← natSub threshold w
      let q ← seekWork rest rs
      natAdd r.length q

@[simp] theorem seekWork_value (threshold : ℕ) (rs : List WeightRun) :
    (seekWork threshold rs).value = firstPrefix threshold rs := by
  induction rs generalizing threshold with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : threshold ≤ r.length * 2 ^ r.doublings <;>
      simp [seekWork, firstPrefix, h, ih, natSub, natMul, natAdd]

def quantileWork (rs : List WeightRun) (J s : ℕ) : Run ℕ := do
  let v ← totalWork rs
  let n ← natMul s v
  let t ← ceilingWork n J
  let q ← seekWork t rs
  natSub q 1

@[simp] theorem quantileWork_value (rs : List WeightRun) (J s : ℕ) :
    (quantileWork rs J s).value = quantile rs J s := by simp [quantileWork, quantile, natSub, natMul]

private theorem twoPower_size (t : ℕ) : (2 ^ t : ℕ).size ≤ t + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < (2 : ℕ) ^ t := Nat.pow_pos (by decide)
  omega

private theorem length_bits {rs : List WeightRun} {r : WeightRun} (hr : r ∈ rs)
    {W : ℕ} (dim : (quoteCount rs).size ≤ W) : r.length.size ≤ W :=
  (Nat.size_le_size (length_le_count hr)).trans dim

private theorem precision_bits {r : WeightRun} {t W : ℕ}
    (exp : r.doublings ≤ t) (wide : t + 2 ≤ W) :
    (power 2 r.doublings).Bound (1 + 2 * t) W := by
  have counter := (size_le_self t).trans (by omega : t ≤ W)
  have u : (2 : ℕ).size ≤ W := by change 2 ≤ W; omega
  exact (power_work 2 _ _ _ exp (by decide) counter u ((twoPower_size t).trans (by omega))).weaken
    (by omega) le_rfl

private theorem runWeight_bound (r : WeightRun) {t W : ℕ}
    (hr : r.doublings ≤ t) (size : r.length.size ≤ W) (wide : t + 2 ≤ W) :
    (runWeight r).Bound (2 + 2*t) W := by
  have p := precision_bits hr wide
  have u := (twoPower_size r.doublings).trans (by omega : r.doublings+1 ≤ W)
  constructor
  · change (power 2 r.doublings).work.slots + 1 ≤ _
    have := p.1
    omega
  · exact max_le p.2 (max_le size (by simpa using u))

private theorem weight_tail_le (r : WeightRun) (rs : List WeightRun) : weight rs ≤ weight (r::rs) :=
  Nat.le_add_left _ _

theorem totalWork_bound (rs : List WeightRun) {t W : ℕ}
    (h : ∀ r ∈ rs, r.doublings ≤ t) (count : (quoteCount rs).size ≤ W)
    (weightWidth : (weight rs).size ≤ W) (wide : t + 2 ≤ W) :
    (totalWork rs).Bound (1 + rs.length * (4 + 2*t)) W := by
  induction rs with
  | nil => simp [totalWork, Run.Bound]
  | cons r rs ih =>
    have hHead := runWeight_bound r (h _ (by simp)) (length_bits (by simp) count) wide
    have hTail := ih (fun a ha => h a (by simp [ha]))
      ((Nat.size_le_size (Nat.le_add_left (quoteCount rs) r.length)).trans count)
      ((Nat.size_le_size (weight_tail_le r rs)).trans weightWidth)
    have wHead : (runWeight r).value.size ≤ W := by
      rw [runWeight_value]
      exact (Nat.size_le_size (Nat.le_add_right (r.length * 2^r.doublings) (weight rs))).trans weightWidth
    have wTail := (Nat.size_le_size (weight_tail_le r rs)).trans weightWidth
    constructor
    · change (runWeight r).work.slots + ((totalWork rs).work.slots + (1 + 1)) ≤ _
      have := hTail.1
      have := hHead.1
      rw [List.length_cons, Nat.succ_mul]
      omega
    · exact max_le hHead.2 (max_le hTail.2
        (max_le (Nat.zero_le _) (max_le wHead (by simpa using wTail))))

private theorem ceilingWork_bound (n d W : ℕ) (hn : n.size ≤ W) (hd : d.size ≤ W) (hw : 1 ≤ W) :
    (ceilingWork n d).Bound 3 W := by
  have hsub := (Nat.size_le_size (Nat.sub_le n 1)).trans hn
  have hdiv := (Nat.size_le_size (Nat.div_le_self (n-1) d)).trans hsub
  exact ⟨le_rfl, max_le (max_le hn hw) (max_le (max_le hsub hd) (max_le hdiv hw))⟩

private theorem firstPrefix_le (rs : List WeightRun) (x : ℕ) :
    firstPrefix x rs ≤ quoteCount rs + 1 := by
  induction rs generalizing x with
  | nil => simp [firstPrefix, quoteCount]
  | cons r rs ih =>
    rw [firstPrefix]
    split
    next h =>
      have d : (x - 1) / 2 ^ r.doublings ≤ r.length :=
        Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; omega)
      simp only [ceiling, quoteCount]
      omega
    next =>
      have := ih (x - r.length * 2^r.doublings)
      simp only [quoteCount]
      omega

theorem seekWork_bound (rs : List WeightRun) (x : ℕ) {t W : ℕ}
    (h : ∀ r ∈ rs, r.doublings ≤ t) (count : (quoteCount rs + 1).size ≤ W)
    (weightWidth : (weight rs).size ≤ W) (xWidth : x.size ≤ W) (wide : t+2 ≤ W) :
    (seekWork x rs).Bound (1 + rs.length * (7 + 2*t)) W := by
  induction rs generalizing x with
  | nil => simp [seekWork, Run.Bound]
  | cons r rs ih =>
    let unit := (2 : ℕ) ^ r.doublings
    let w := r.length * unit
    have expo := h r (by simp)
    have wunit : unit.size ≤ W := (twoPower_size _).trans (by omega)
    have powerBudget := precision_bits expo wide
    have count0 := (Nat.size_le_size (Nat.le_succ (quoteCount (r::rs)))).trans count
    have hlen := length_bits (r := r) (by simp) count0
    have ww : w.size ≤ W := (Nat.size_le_size (Nat.le_add_right w (weight rs))).trans weightWidth
    have wback : (quoteCount rs+1).size ≤ W :=
      (Nat.size_le_size (Nat.add_le_add_right (Nat.le_add_left (quoteCount rs) r.length) 1)).trans count
    have xback : (x - w).size ≤ W := (Nat.size_le_size (Nat.sub_le x w)).trans xWidth
    have resultWidth : (firstPrefix (x - w) rs).size ≤ W :=
      (Nat.size_le_size (firstPrefix_le _ _)).trans wback
    by_cases front : x ≤ w
    · have hfront := ceilingWork_bound x unit W xWidth wunit (by omega)
      constructor
      · simp only [seekWork, Run.bind_slots, natMul, step_slots, step_value,
          power_value, show (x ≤ r.length * 2 ^ r.doublings) from front, decide_true, ite_true]
        have := powerBudget.1
        have := hfront.1
        dsimp [unit] at this
        rw [List.length_cons, Nat.succ_mul]
        omega
      · simp only [seekWork, Run.bind_width, natMul, step_width, step_value,
          power_value, show (x ≤ r.length * 2 ^ r.doublings) from front, decide_true, ite_true]
        exact max_le powerBudget.2 (max_le (max_le hlen wunit) (max_le (max_le xWidth ww) hfront.2))
    · have hback := ih (x-w) (fun a ha => h a (by simp [ha])) wback
        ((Nat.size_le_size (weight_tail_le r rs)).trans weightWidth) xback
      constructor
      · simp only [seekWork, Run.bind_slots, natMul, natAdd, natSub, step_slots, step_value,
          power_value, show ¬(x ≤ r.length * 2 ^ r.doublings) from front, decide_false,
          Bool.false_eq_true, ite_false]
        have := powerBudget.1
        have := hback.1
        dsimp [w, unit] at this
        rw [List.length_cons, Nat.succ_mul]
        omega
      · simp only [seekWork, Run.bind_width, natMul, natAdd, natSub, step_width, step_value,
          power_value, show ¬(x ≤ r.length * 2 ^ r.doublings) from front, decide_false,
          Bool.false_eq_true, ite_false, seekWork_value]
        exact max_le powerBudget.2 (max_le (max_le hlen wunit) (max_le (max_le xWidth ww)
          (max_le (max_le xWidth ww) (max_le hback.2 (max_le hlen resultWidth)))))

/-- Select one quantile with a number of operations linear in the
number of runs and the largest doubling exponent. -/
theorem quantileWork_bound (rs : List WeightRun) (J s : ℕ) {t W : ℕ}
    (h : ∀ r ∈ rs, r.doublings ≤ t) (count : (quoteCount rs+1).size ≤ W)
    (weightWidth : (weight rs).size + s.size + 1 ≤ W) (jSize : J.size ≤ W)
    (wide : t + 2 ≤ W) :
    (quantileWork rs J s).Bound (8 + rs.length * (11 + 4*t)) W := by
  have w0 : (weight rs).size ≤ W := by omega
  have ws : s.size ≤ W := by omega
  have count0 := (Nat.size_le_size (Nat.le_succ (quoteCount rs))).trans count
  have tot := totalWork_bound rs h count0 w0 wide
  have hn := (size_mul_le s (weight rs)).trans (by omega : s.size + (weight rs).size ≤ W)
  have hc := ceilingWork_bound (s * weight rs) J W hn jSize (by omega)
  have ht : (ceiling (s * weight rs) J).size ≤ W := by
    have hh := size_succ_le ((s * weight rs - 1) / J)
    have hh' := (Nat.size_le_size
      ((Nat.div_le_self (s * weight rs - 1) J).trans (Nat.sub_le _ _))).trans (size_mul_le s (weight rs))
    unfold ceiling
    omega
  have search := seekWork_bound rs (ceiling (s * weight rs) J) h count w0 ht wide
  have hq := (Nat.size_le_size (firstPrefix_le rs (ceiling (s*weight rs) J))).trans count
  have w1 : (1 : ℕ).size ≤ W := by change 1 ≤ W; omega
  constructor
  · simp only [quantileWork, Run.bind_slots, totalWork_value, natMul, natSub, step_slots,
      step_value, ceilingWork_value]
    have ht := tot.1
    have hc := hc.1
    have hs := search.1
    rw [show 11 + 4*t = (4+2*t)+(7+2*t) by omega, Nat.mul_add]
    omega
  · simp only [quantileWork, Run.bind_width, totalWork_value, natMul, natSub, step_width,
      step_value, ceilingWork_value, seekWork_value, max_le_iff]
    exact ⟨tot.2, ⟨ws, w0⟩, hc.2, search.2, hq, w1⟩

end Kintali.QuoteSearch.Runs
