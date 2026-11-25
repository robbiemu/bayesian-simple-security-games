module

public import Kintali.Machine.BitStacks
public import Kintali.InputOutput.Solver
import Mathlib.Tactic.Choose

/-! # Sufficient machine executions for the public equilibrium question

One fixed program must emit a canonically encoded output for every typed
input within one polynomial clock. On valid games it suffices to identify
the emitted value with the checked solver. Each invalid game may receive
any canonically encoded output.
-/

public section

namespace Kintali.Machine

open BitStacks InputOutput

/-- Reduce the public existence question to actual finite-program executions. -/
theorem exists_polyTime_bayesNash_of_runs {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (p : Program K L) (time : Polynomial ℕ)
    (runs : ∀ a : Input, ∃ (e : Output) (ticks : ℕ),
      ticks ≤ time.eval (Binary.input a).length ∧
      p.Steps ticks (p.init (Binary.input a)) (p.final (Binary.output e)) ∧
      (a.Valid → e = solve a)) :
    ∃ f : Input → Output,
      Nonempty (Turing.TM2ComputableInPolyTime Binary.input Binary.output f) ∧
      ∀ a : Input, a.Valid → a.IsBayesNash (f a) := by
  choose f ticks bounded executed agrees using runs
  refine ⟨f, ⟨p.polyTime Binary.input Binary.output f time fun a =>
    ⟨⟨ticks a, executed a⟩, bounded a⟩⟩, ?_⟩
  intro a valid
  rw [agrees a valid]
  exact solve_correct a valid

end Kintali.Machine
