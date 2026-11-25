module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# The weighted quote search

Section 3 of Kintali's short paper keeps a fixed set of witness bids.
Every failed trial doubles the weight of some witness, while every
pair's total grows by at most a factor of `1 + 1 / (4 * h)`.
The argument below uses rational powers and the integer base-two
logarithm (`Nat.log2`).
-/

open scoped BigOperators

@[expose] public section

namespace Kintali
namespace QuoteSearch

/-- A cumulative interval with no selected internal quantile weighs at
most one `J`-th of the total. The quantile `s` selects the first prefix
whose weight reaches `s * V / J`, so it lies in the interval exactly when
`J * a < s * V ≤ J * b`. -/
theorem unmarked_interval_bound {J V a b : ℕ} (ha : a ≤ b) (hb : b ≤ V)
    (hMiss : ∀ s : ℕ, 0 < s → s < J → s * V ≤ J * a ∨ J * b < s * V) :
    J * (b - a) ≤ V := by
  by_contra! hLarge
  have hV : 0 < V := by
    by_contra! h
    have hab : b - a = 0 := by omega
    simp [hab] at hLarge
  let s := J * a / V + 1
  have hFloor := Nat.div_mul_le_self (J * a) V
  have hRem := Nat.mod_add_div (J * a) V
  have hMod := Nat.mod_lt (J * a) hV
  have hBefore : J * a < s * V := by
    dsimp [s]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (J * a / V) V]
    omega
  have hSplit : J * (b - a) + J * a = J * b := by
    rw [← Nat.mul_add, Nat.sub_add_cancel ha]
  have hThrough : s * V < J * b := by
    dsimp [s]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hInternal : s < J := by
    by_contra! hs
    exact (not_lt_of_ge ((Nat.mul_le_mul_left J hb).trans (Nat.mul_le_mul_right V hs))) hThrough
  exact (hMiss s (Nat.zero_lt_succ _) hInternal).elim hBefore.not_ge hThrough.not_gt

variable {Bid Pair : Type*} [DecidableEq Bid]

/-- Count the rounds in which a bid's weight was doubled. -/
def hits (marked : ℕ → Finset Bid) (bid : Bid) : ℕ → ℕ
  | 0 => 0
  | t + 1 => hits marked bid t + if bid ∈ marked t then 1 else 0

def weight (marked : ℕ → Finset Bid) (bid : Bid) (t : ℕ) : ℚ :=
  2 ^ hits marked bid t

def totalWeight (marked : ℕ → Finset Bid) (bids : Finset Bid) (t : ℕ) : ℚ :=
  ∑ bid ∈ bids, weight marked bid t

private theorem totalWeight_succ (marked : ℕ → Finset Bid) (bids : Finset Bid) (t : ℕ) :
    totalWeight marked bids (t + 1) = totalWeight marked bids t +
      totalWeight marked (bids.filter (· ∈ marked t)) t := by
  unfold totalWeight
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hm : b ∈ marked t
  · simp [weight, hits, hm, pow_succ, mul_two]
  · simp [weight, hits, hm]

private theorem block_growth {h : ℕ} (hh : 0 < h) :
    (1 + 1 / (4 * (h : ℚ))) ^ (2 * h) ≤ 2 := by
  let z : ℚ := 1 / (4 * (h : ℚ))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hd : (4 : ℚ) ≤ 4 * (h : ℚ) := by
    have h' : (1 : ℚ) ≤ h := by exact_mod_cast hh
    linarith
  have hzSmall : z ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
  have hzEq : 1 + ((2 * h : ℕ) : ℚ) * (-z) = 1 / 2 := by
    push_cast
    dsimp [z]
    field_simp
    norm_num
  have hBern := one_add_mul_le_pow (R := ℚ) (a := -z) (by linarith) (2 * h)
  rw [hzEq, ← sub_eq_add_neg] at hBern
  have hprod : (1 + z) ^ (2 * h) * (1 - z) ^ (2 * h) ≤ 1 := by
    rw [← mul_pow]
    calc
      _ ≤ (1 : ℚ) ^ (2 * h) := pow_le_pow_left₀
        (mul_nonneg (by linarith) (by linarith)) (by nlinarith [sq_nonneg z]) _
      _ = 1 := one_pow _
  have hUpper := (mul_le_mul_of_nonneg_left hBern (by positivity :
    0 ≤ (1 + z) ^ (2 * h))).trans hprod
  change (1 + z) ^ (2 * h) ≤ 2
  linarith

private theorem hits_witness_sum (marked : ℕ → Finset Bid) (witness : Finset Bid) {T : ℕ}
    (hHit : ∀ t < T, ∃ b ∈ witness, b ∈ marked t) :
    T ≤ ∑ b ∈ witness, hits marked b T := by
  induction T with
  | zero => simp
  | succ t ih =>
    have ht := ih (fun s hs => hHit s (by omega))
    obtain ⟨b, hb, hm⟩ := hHit t (by omega)
    have hone : 1 ≤ ∑ b ∈ witness, if b ∈ marked t then 1 else 0 := by
      simpa [hm] using (Finset.single_le_sum
        (f := fun b => if b ∈ marked t then (1 : ℕ) else 0) (fun _ _ => Nat.zero_le _) hb)
    simp only [hits, Finset.sum_add_distrib]
    omega

/-- The growth argument needs only the weights of the fixed witness
and the group totals. This form also applies to compressed runs. -/
theorem failure_bound_of_growth (marked : ℕ → Finset Bid) (witness : Finset Bid)
    (pair : Bid → Pair) (total : Pair → ℕ → ℚ) {T h G : ℕ}
    (hh : 0 < h) (hSize : witness.card ≤ h) (hInitial : ∀ p, total p 0 ≤ G)
    (hWithin : ∀ b ∈ witness, ∀ t ≤ T, weight marked b t ≤ total (pair b) t)
    (hHit : ∀ t < T, ∃ b ∈ witness, b ∈ marked t)
    (hStep : ∀ t < T, ∀ p, total p (t + 1) ≤ total p t * (1 + 1 / (4 * (h : ℚ)))) :
    T < 2 * h * (G.log2 + 1) := by
  let k := G.log2 + 1
  let t₀ := (2 * h) * k
  let rate : ℚ := 1 + 1 / (4 * (h : ℚ))
  have hRate : 0 ≤ rate := by dsimp [rate]; positivity
  have hk : 0 < k := by dsimp [k]; omega
  by_contra! hLong
  have hPrefix : t₀ ≤ T := hLong
  have hGrowth (t : ℕ) (ht : t ≤ T) (p : Pair) : total p t ≤ (G : ℚ) * rate ^ t := by
    induction t with
    | zero => simpa using hInitial p
    | succ t ih =>
      exact (hStep t (by omega) p).trans
        (by rw [pow_succ, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (ih (by omega)) hRate)
  have hMany : ∃ b ∈ witness, 2 * k ≤ hits marked b t₀ := by
    by_contra! hFew
    have hTotal := hits_witness_sum marked witness (T := t₀)
      (fun t ht => hHit t (ht.trans_le hPrefix))
    have hUpper : (∑ b ∈ witness, hits marked b t₀) ≤ witness.card * (2 * k - 1) := by
      calc
        _ ≤ ∑ b ∈ witness, (2 * k - 1) :=
          Finset.sum_le_sum (fun b hb => by have hf := hFew b hb; omega)
        _ = _ := by simp
    have hLt : h * (2 * k - 1) < h * (2 * k) :=
      Nat.mul_lt_mul_of_pos_left (by omega) hh
    have hSwap : h * (2 * k) = t₀ := by dsimp [t₀]; ac_rfl
    exact (not_lt_of_ge hTotal) (hUpper.trans_lt
      ((Nat.mul_le_mul_right (2 * k - 1) hSize).trans_lt (hLt.trans_eq hSwap)))
  obtain ⟨b, hb, hDoubled⟩ := hMany
  have hG : (G : ℚ) < (2 : ℚ) ^ k := by exact_mod_cast (Nat.lt_log2_self (n := G))
  have hLower : (2 : ℚ) ^ (2 * k) ≤ total (pair b) t₀ := by
    apply (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hDoubled).trans
    exact hWithin b hb t₀ hPrefix
  have hUpper : total (pair b) t₀ ≤ (G : ℚ) * (2 : ℚ) ^ k := by
    apply (hGrowth t₀ hPrefix (pair b)).trans
    dsimp only [t₀]
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (block_growth hh) k) (by positivity)
  rw [two_mul, pow_add] at hLower
  exact (not_lt_of_ge (hLower.trans hUpper)) (mul_lt_mul_of_pos_right hG (by positivity))

/-- Starting with unit weights, the number of failed trials is smaller
than `2 * h * (G.log2 + 1)`. Each group starts with at most `G` bids and
the marked weight in that group is at most its total divided by `4 * h`.
Every failed trial marks a member of the same witness set, of size at
most `h`. -/
theorem failure_bound (marked : ℕ → Finset Bid) (witness : Finset Bid)
    (pair : Bid → Pair) (bids : Pair → Finset Bid) {T h G : ℕ}
    (hh : 0 < h) (hSize : witness.card ≤ h) (hGroups : ∀ p, (bids p).card ≤ G)
    (hBelongs : ∀ b ∈ witness, b ∈ bids (pair b))
    (hHit : ∀ t < T, ∃ b ∈ witness, b ∈ marked t)
    (hMarked : ∀ t < T, ∀ p, totalWeight marked ((bids p).filter (· ∈ marked t)) t ≤
      totalWeight marked (bids p) t / (4 * (h : ℚ))) :
    T < 2 * h * (G.log2 + 1) := by
  refine failure_bound_of_growth marked witness pair (fun p => totalWeight marked (bids p))
    hh hSize ?_ ?_ hHit ?_
  · intro p
    simpa [totalWeight, weight, hits] using (show ((bids p).card : ℚ) ≤ G by exact_mod_cast hGroups p)
  · intro b hb t _
    exact Finset.single_le_sum (f := fun a => weight marked a t)
      (fun _ _ => by unfold weight; positivity) (hBelongs b hb)
  · intro t ht p
    rw [totalWeight_succ, mul_add, mul_one, ← mul_div_assoc, mul_one]
    exact add_le_add_right (hMarked t ht p) _

end QuoteSearch
end Kintali
