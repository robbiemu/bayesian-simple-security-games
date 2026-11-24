module

public import StochasticGames.BinaryEncoding
public import StochasticGames.ReductionComplexity

/-! A bit-string entry point for the same compiler. -/

@[expose] public section
namespace StochasticGames.ThresholdReduction

open BinaryEncoding CompilationCost

def compileBinary (bits : List Bool) : Option (List Bool) :=
  (decodeInput bits).map fun ⟨_, input⟩ => compileBits input

theorem compileBinary_inputBits {n : ℕ} (input : ThresholdInput n) :
    compileBinary (inputBits input) = some (compileBits input) := by
  simp [compileBinary]

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

/-- Extend the binary cost model by allowing sixteen arithmetic or list slots
per decoded input bit. This covers width counts, reconstruction by binary
digits, and checking and assembling the decoded fields. -/
def parsingCharge (length : ℕ) : ℕ := 16 * length * slotBitCost length

def binaryBitWork {n : ℕ} (input : ThresholdInput n) : ℕ :=
  parsingCharge (inputBits input).length + compileBitWork input

def binaryReductionPolynomial (length : ℕ) : ℕ :=
  parsingCharge length + reductionPolynomial length

theorem binaryBitWork_le {n : ℕ} (input : ThresholdInput n) :
    binaryBitWork input ≤ binaryReductionPolynomial (inputBits input).length :=
  Nat.add_le_add_left (compileBitWork_le input) _

end StochasticGames.ThresholdReduction
