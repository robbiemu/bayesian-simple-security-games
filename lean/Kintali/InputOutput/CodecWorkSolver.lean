module

public import Kintali.InputOutput.CodecWork
public import Kintali.InputOutput.Solver

/-! # Composing the actual binary boundary with a traced exact solver

A run on a valid encoded market receives the solver's transition and width
bounds and its compact output length bound. Each of these may be replaced
by a polynomial in the public input length. The cost of a concrete
implementation of the solver is an explicit hypothesis.
-/

@[expose] public section

namespace Kintali.InputOutput.CodecWork

open Binary StochasticGames.CompilerRun

def solveRun (core : Input → Run Output) (xs : Stream) : Run Stream := do
  let decoded ← inputReader.run xs
  match ← step 0 decoded with
  | none => step 0 []
  | some a => do
    let e ← core a
    outputWriter.run e

theorem solveRun_value (core : Input → Run Output) (exactCore : ∀ a, (core a).value = solve a)
    (xs : Stream) : (solveRun core xs).value = solveBits xs := by
  cases hd : inputCodec.decode xs <;> simp [solveRun,input_value,hd,solveBits,exactCore,outputWriter.correct]

def solveSlots (S K B : ℕ) := inputLimit S+1+K+72*(B+1)
def solveWidth (S W B : ℕ) := S+8+W+B+3

theorem solveRun_work (core : Input → Run Output) (a : Input) {K W B : ℕ}
    (coreWork : (core a).Bound K W) (outFit : (output (core a).value).length ≤ B) :
    (solveRun core (input a)).Bound (solveSlots (lengthInput a) K B) (solveWidth (lengthInput a) W B) := by
  have read := input_work (input a)
  have write := output_work (core a).value
  simp only [solveRun,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,step_value,
    input_value,read_input,solveSlots,solveWidth,lengthInput] at *
  constructor
  · omega
  · omega

/-- Specializing the solver costs and output length to polynomials gives a
polynomial binary word bound on the exact equilibrium bitstream. -/
theorem solveRun_correct (core : Input → Run Output) (a : Input) (valid : a.Valid)
    {K W B : ℕ} (coreValue : (core a).value = solve a) (coreWork : (core a).Bound K W)
    (outFit : (output (solve a)).length ≤ B) :
    let r := solveRun core (input a)
    r.value = solveBits (input a) ∧
    outputCodec.decode r.value = some (solve a) ∧ a.IsBayesNash (solve a) ∧
    LinearProgramming.RecoveryRun.binaryWork (lengthInput a) r.work ≤
      binaryLimit (lengthInput a) (solveSlots (lengthInput a) K B) (solveWidth (lengthInput a) W B) := by
  have val : (solveRun core (input a)).value = output (solve a) := by
    simp [solveRun,input_value,coreValue,outputWriter.correct]
  exact ⟨val.trans (solveBits_input a).symm, val ▸ read_output _, solve_correct a valid,
    addressed_bound _ (solveRun_work core a coreWork (coreValue ▸ outFit))⟩

end Kintali.InputOutput.CodecWork
