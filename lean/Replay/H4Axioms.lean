import StochasticGames.BinaryReduction
import StochasticGames.RealCompilation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``StochasticGames.Source.value_lt_iff_dualFeasible,
    ``StochasticGames.SourcePrecision.strict_witness_iff,
    ``StochasticGames.SourcePrecision.exact_iff_compiled,
    ``StochasticGames.MeanPayoff.Game.swap_nonnegative_iff,
    ``StochasticGames.MeanPayoff.Game.positional_saddle,
    ``StochasticGames.MeanPayoff.Game.swap_value,
    ``StochasticGames.ThresholdReduction.compile_valid,
    ``StochasticGames.ThresholdReduction.compile_correct,
    ``StochasticGames.ThresholdReduction.compileBits_le,
    ``StochasticGames.ThresholdReduction.checked_reduction,
    ``StochasticGames.BinaryEncoding.decodeInput_inputBits,
    ``StochasticGames.BinaryEncoding.decodeTable_tableBits,
    ``StochasticGames.ThresholdReduction.compileBinary_correct,
    ``StochasticGames.ThresholdReduction.binaryBitWork_le,
    ``StochasticGames.SourcePrecision.tightened_minimum_slack,
    ``StochasticGames.RealCompilation.exact_extends_by_evaluation,
    ``StochasticGames.RealCompilation.compiled_selects_attaining_branch,
    ``StochasticGames.PaperArena.table_correct,
    ``StochasticGames.ThresholdReduction.compileBinary_polynomial_time]
  for theoremName in theorems do
    let axioms ← collectAxioms theoremName
    let unexpected := axioms.filter fun name => !allowed.contains name
    unless unexpected.isEmpty do
      throwError "{theoremName} uses unexpected axioms {unexpected.toList}"
    logInfo m!"{theoremName} depends on {axioms.toList}"
