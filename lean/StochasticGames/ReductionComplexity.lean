module

public import StochasticGames.ThresholdReduction
public import StochasticGames.CompilationCost
import all StochasticGames.ThresholdReduction
import all StochasticGames.ThresholdInput
import Mathlib.Tactic.GCongr

/-! # The reduction in the binary cost model

The nonterminal case uses the cost of the explicit construction. The other
cases read the input and write the single-loop table. Dispatch charges two
signed comparisons, a terminal tag inspection, and the branch choice.
-/

@[expose] public section
namespace StochasticGames.ThresholdReduction

open CompilationCost TrivialThreshold

variable {n : ℕ} (input : ThresholdInput n)

def compileBits : List Bool := tableBits (compile input)

def compileBitWork : ℕ :=
  4 * slotBitCost (inputLength input) +
    if input.numerator ≤ 0 then (inputBits input).length + (tableBits (loop true)).length
    else if (input.denominator : ℤ) < input.numerator then
      (inputBits input).length + (tableBits (loop false)).length
    else match input.start with
      | .inr terminal => (inputBits input).length + (tableBits (loop terminal)).length
      | .inl s => bitWork input s

def reductionPolynomial (L : ℕ) : ℕ :=
  4 * slotBitCost L + (polynomial L + L + 64)

private theorem loop_bits_le (b : Bool) : (tableBits (loop b)).length ≤ 64 := by
  cases b <;> decide

private theorem dispatched_weight_bound (s : Fin n)
    (pos : 0 < input.numerator) (notTooHigh : ¬ (input.denominator : ℤ) < input.numerator) :
    ∀ a ∈ (mainTable input s).arcs, a.weight.natAbs ≤ vertexCount input s * scale input + 1 := by
  have hi : input.threshold ≤ 1 :=
    le_of_not_gt fun h => notTooHigh (input.one_lt_threshold_iff.mp h)
  rw [← (table_lengths input s).1]
  exact ThresholdCompiler.table_weight_le input s pos hi

theorem compileBits_le :
    (compileBits input).length ≤ 16000 * (inputBits input).length ^ 3 := by
  let L := (inputBits input).length
  have minLength : 1 ≤ L := by
    have h := inputLength_le_bits input
    unfold inputLength at h
    omega
  have oneLoop (b : Bool) : (tableBits (loop b)).length ≤ 16000 * L ^ 3 := by
    have cube : 1 ≤ L ^ 3 := one_le_pow₀ minLength
    exact (loop_bits_le b).trans (by omega)
  unfold compileBits compile
  split
  · exact oneLoop true
  · rename_i positive
    split
    · exact oneLoop false
    · rename_i notTooHigh
      cases input.start with
      | inr b => exact oneLoop b
      | inl s =>
        apply (table_bits_le input s
          (dispatched_weight_bound input s (lt_of_not_ge positive) notTooHigh)).trans
        gcongr
        exact inputLength_le_bits input

theorem compileBitWork_le :
    compileBitWork input ≤ reductionPolynomial (inputBits input).length := by
  unfold compileBitWork reductionPolynomial
  apply Nat.add_le_add
  · unfold slotBitCost
    gcongr
    exact inputLength_le_bits input
  · have oneLoop (b : Bool) :
        (inputBits input).length + (tableBits (loop b)).length ≤
          polynomial (inputBits input).length + (inputBits input).length + 64 := by
      have h := loop_bits_le b
      omega
    split
    · exact oneLoop true
    · rename_i positive
      split
      · exact oneLoop false
      · rename_i notTooHigh
        cases input.start with
        | inr b => exact oneLoop b
        | inl s =>
          change bitWork input s ≤ _
          have h := bitWork_le_serialized_input input s
            (dispatched_weight_bound input s (lt_of_not_ge positive) notTooHigh)
          omega

/-- The same executable compiler satisfies the semantic decision theorem
and the bit-work bound in the specified binary cost model. -/
theorem checked_reduction :
    (compile input).Valid ∧
    ((input.threshold : ℝ) ≤ (Source.value input.rows.get input.start : ℝ) ↔
      (compile input).Nonnegative) ∧
    compileBitWork input ≤ reductionPolynomial (inputBits input).length :=
  ⟨compile_valid input, compile_correct input, compileBitWork_le input⟩

end StochasticGames.ThresholdReduction
