module

public import StochasticGames.CompilerRun
public import Mathlib.Data.Nat.BinaryRec

/-! # The binary logarithm used in the trial budget -/

@[expose] public section

namespace Kintali.QuoteSearch.ClockWork

open StochasticGames.CompilerRun

def logRun (n : ℕ) : Run ℕ :=
  if _h : 1 < n then do
    let _ ← step n.size ()
    let half := n >>> 1
    let _ ← step n.size half
    let v ← logRun half
    natAdd v 1
  else step n.size 0
termination_by n
decreasing_by
  simp only [Nat.shiftRight_eq_div_pow, pow_one]
  exact Nat.div_lt_self (by omega) (by decide)

@[simp] theorem logRun_value (n : ℕ) : (logRun n).value = n.log2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [logRun]
    by_cases h : 1 < n
    · simp only [dite_eq_left h, Run.bind_value, step_value, natAdd]
      have hn : n >>> 1 ≠ 0 := by rw [Nat.shiftRight_eq_div_pow, pow_one]; omega
      have ht : n >>> 1 < n := by rw [Nat.shiftRight_eq_div_pow, pow_one]; omega
      rw [ih _ ht, Nat.log2_eq_succ_log2_shiftRight hn]
    · have hn : n = 0 ∨ n = 1 := by omega
      rcases hn with rfl | rfl <;> rfl

theorem logRun_work (n : ℕ) {w : ℕ} (hw : n.size ≤ w) (one : 1 ≤ w) :
    (logRun n).Bound (1+3*n.log2) w := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [logRun]
    by_cases h : 1 < n
    · have hhalf : n >>> 1 = n / 2 := by rw [Nat.shiftRight_eq_div_pow, pow_one]
      have hn : n >>> 1 ≠ 0 := by rw [hhalf]; omega
      have ht : n >>> 1 < n := by rw [hhalf]; omega
      have hd := (Nat.size_le_size ht.le).trans hw
      have prior := ih _ ht hd
      have val : ((n >>> 1).log2).size ≤ w := by
        apply (Nat.size_le_size ?_).trans hd
        exact (Nat.log2_le_self _)
      constructor
      · simp only [dite_eq_left h, Run.bind_slots, step_slots, natAdd]
        have := prior.1
        rw [Nat.log2_eq_succ_log2_shiftRight hn]
        omega
      · simp only [dite_eq_left h, Run.bind_width, step_width, logRun_value, natAdd]
        exact max_le hw (max_le hw (max_le prior.2 (max_le val one)))
    · rw [dite_eq_right h]
      exact ⟨by simp, hw⟩

end Kintali.QuoteSearch.ClockWork
