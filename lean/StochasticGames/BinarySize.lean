module

public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum

/-! Elementary binary length bounds for arithmetic and indexing. -/

public section

namespace StochasticGames.BinarySize

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (by positivity))

theorem size_succ_le (a : ℕ) : (a + 1).size ≤ a.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have below := Nat.lt_size_self a
  omega

theorem size_le_self (a : ℕ) : a.size ≤ a := by
  apply Nat.size_le.mpr
  induction a with
  | zero => decide
  | succ a ih =>
    rw [pow_succ]
    omega

theorem size_mul_pow_two_le (d k : ℕ) : (d * 2 ^ k).size ≤ d.size + k := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self d) (by positivity)

theorem size_mul_pow_three_le (d k : ℕ) : (d * 3 ^ k).size ≤ d.size + 2 * k := by
  have bound : 3 ^ k ≤ 2 ^ (2 * k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by decide : 3 ≤ 2 ^ 2) _
  exact (Nat.size_le_size (Nat.mul_le_mul_left d bound)).trans (size_mul_pow_two_le d _)

end StochasticGames.BinarySize
