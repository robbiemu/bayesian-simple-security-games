module

public import Kintali.Solver
public import Kintali.InputOutput.Codec
public import Kintali.InputOutput.Lottery

/-! # Exact solver on the public rational payoff tables and on their bitstrings -/

@[expose] public section

namespace Kintali.InputOutput

def solve (a : Input) : Output :=
  if hm : 0 < a.targets then
    ((a.game.solve hm).map writeStrategy).getD ([], [])
  else ([], [])

theorem solve_correct (a : Input) (h : a.Valid) : a.IsBayesNash (solve a) := by
  have valid := ((a.valid_iff).1 h).1
  obtain ⟨s, hs, hEq⟩ := a.game.solve_correct valid
  apply (a.equilibrium_iff _).2
  simpa only [solve, dite_eq_left valid.targets, hs, Option.map_some, Option.getD_some,
    shape_write, read_write, true_and] using hEq

/-- Realize the compact defender output as a sparse list of legal pure defenses. -/
def defenses (a : Input) : List (Lottery.Outcome a.targets) :=
  Lottery.recover (readStrategy (solve a) a.types a.targets).coverage

theorem defenses_correct (a : Input) (h : a.Valid) :
    (defenses a).length ≤ a.targets ∧
    (∀ p ∈ defenses a, p.1.card = a.1 ∧ 0 < p.2) ∧
    Lottery.expected (defenses a) (fun _ => 1) = 1 ∧
    ∀ j, Lottery.expected (defenses a) (fun b => if j ∈ b then 1 else 0) =
      (readStrategy (solve a) a.types a.targets).coverage j := by
  have heq := ((a.equilibrium_iff _).1 (solve_correct a h)).2
  exact Lottery.recover_correct _ h.1 _ heq.coverage_bounds heq.coverage_sum

/-- Total bitstring program. Invalid bitstrings may return any value. -/
def solveBits (bits : List Bool) : List Bool :=
  ((Binary.inputCodec.decode bits).map (fun a => Binary.output (solve a))).getD []

@[simp] theorem solveBits_input (a : Input) : solveBits (Binary.input a) = Binary.output (solve a) := by
  simp [solveBits]

theorem solveBits_correct (a : Input) (h : a.Valid) :
    ∃ e, Binary.outputCodec.decode (solveBits (Binary.input a)) = some e ∧ a.IsBayesNash e :=
  ⟨solve a, by simp, solve_correct a h⟩

end Kintali.InputOutput
