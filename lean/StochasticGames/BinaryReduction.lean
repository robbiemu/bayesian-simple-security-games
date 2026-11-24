module

public import StochasticGames.BinaryEncoding
public import StochasticGames.CompilerExecution
public import StochasticGames.PaperArena
public import StochasticGames.PositionalMeanPayoff

/-! # The executable binary reduction

The public encoder projects the output from the measured execution. The
polynomial-time theorem and the exact threshold theorem refer to that output.
`PaperArena` relates the explicit pins of Section 5 to the emitted arena.
`PositionalMeanPayoff` supplies Section 6's affine value identity.
-/

@[expose] public section
namespace StochasticGames.ThresholdReduction

open BinaryEncoding CompilationCost

def compileBinary (bits : List Bool) : Option (List Bool) :=
  (CompilerExecution.run bits).value

theorem compileBinary_value (bits : List Bool) :
    compileBinary bits = (decodeInput bits).map (fun ⟨_, input⟩ => compileBits input) :=
  CompilerExecution.run_value bits

/-- For every accepted binary encoding, this encoder emits one valid table
with the exact answer within the same fixed bit-time polynomial. -/
theorem compileBinary_polynomial_time {n : ℕ} {bits : List Bool} {input : ThresholdInput n}
    (accepted : decodeInput bits = some ⟨n,input⟩) :
    ∃ out : List Bool, ∃ table : ArenaEncoding.Table,
      compileBinary bits = some out ∧ decodeTable out = some table ∧ table.Valid ∧
      ((input.threshold : ℝ) ≤ (Source.value input.rows.get input.start : ℝ) ↔ table.Nonnegative) ∧
      CompilerExecution.bitWork bits ≤ CompilerExecution.polynomial bits.length := by
  refine ⟨compileBits input, compile input, ?_, ?_, ?_, ?_, ?_⟩
  · rw [compileBinary_value, accepted]
    rfl
  · exact decodeTable_tableBits _
  · exact compile_valid input
  · exact compile_correct input
  · exact CompilerExecution.bitWork_le accepted

theorem compileBinary_inputBits {n : ℕ} (input : ThresholdInput n) :
    compileBinary (inputBits input) = some (compileBits input) := by
  simp [compileBinary_value]

theorem compileBinary_decodes_output {n : ℕ} (input : ThresholdInput n) :
    (compileBinary (inputBits input)).bind decodeTable = some (compile input) := by
  rw [compileBinary_inputBits]
  exact decodeTable_tableBits _

/-- The graph decoded from the binary output answers the source threshold. -/
theorem compileBinary_correct {n : ℕ} (input : ThresholdInput n) :
    (input.threshold : ℝ) ≤ (Source.value input.rows.get input.start : ℝ) ↔
      ∃ table : ArenaEncoding.Table,
        (compileBinary (inputBits input)).bind decodeTable = some table ∧ table.Nonnegative := by
  rw [compileBinary_decodes_output, compile_correct]
  constructor
  · intro nonnegative
    exact ⟨compile input, rfl, nonnegative⟩
  · rintro ⟨table, h, nonnegative⟩
    rwa [Option.some.inj h]

end StochasticGames.ThresholdReduction
