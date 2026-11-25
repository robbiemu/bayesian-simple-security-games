"""Replay against unmodified declarations extracted from the pinned Formal Conjectures sources.

Run from the Lean project with `python3 Kintali/InputOutput/check_upstream.py <upstream-checkout>`
after building Kintali.Machine.PublicSolver and Kintali.Machine.Delimiter. The
checkout must contain the pinned commit. The replay checks the model, encoding,
and polynomial-time definition. It uses the question's exact proposition as a
conditional target and omits the upstream proof placeholder.
"""

import subprocess
import sys
from pathlib import Path


REVISION = "9bd16c570aed942e00ae000c7522dd42ebbb25eb"
MODEL = "FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean"
ENCODING = "FormalConjecturesForMathlib/Computability/BitstringEncoding.lean"
COMPLEXITY = "FormalConjecturesForMathlib/Computability/Complexity.lean"


def source(repo, path):
    return subprocess.check_output(
        ["git", "-C", repo, "show", f"{REVISION}:{path}"], text=True
    )


def main(repo):
    encoding = source(repo, ENCODING)
    model = source(repo, MODEL)
    complexity = source(repo, COMPLEXITY)
    ns = "namespace Arxiv.«2610.08796»"
    question = model.split("theorem exists_isPolyTime_bayesNash :", 1)[1].split(" := by", 1)[0]
    lean = (
        "import Kintali.Machine.PublicSolver\nimport Kintali.Machine.Delimiter\n"
        + encoding[encoding.index("open Computability"):]
        + "\n"
        + complexity[complexity.index("open Computability Turing"):complexity.index("/-- The identity")]
        + "\nend ComplexityTheory\n"
        + model[model.index(ns):model.index("/-- Can one deterministic")]
        + "\nend Arxiv.«2610.08796»\n"
        + CHECKS
        + MACHINE_CHECK.replace("__UPSTREAM_PROPOSITION__", question)
    )
    subprocess.run(["lake", "env", "lean", "--stdin"], input=lean, text=True, check=True)


CHECKS = """open Kintali.InputOutput Arxiv.«2610.08796»
example (a : Input) : a.Valid ↔ GameInput.Valid a := Iff.rfl
example (a : Input) (e : Output) : a.IsBayesNash e ↔ GameInput.IsBayesNash a e := Iff.rfl
example (a : GameInput) (valid : GameInput.Valid a) :
    GameInput.IsBayesNash a (solve a) := solve_correct a valid
private theorem block_eq (l : List Bool) : Binary.block l = BitstringEncoding.delimit l := by
  induction l with
  | nil => rfl
  | cons b l h => simp [Binary.block, BitstringEncoding.delimit, h]
private theorem pair_eq {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {a : α → List Bool} {b : β → List Bool} (ha : a = BitstringEncoding.bitEncode)
    (hb : b = BitstringEncoding.bitEncode) : Binary.pair a b = BitstringEncoding.bitEncode := by
  subst a b
  funext p
  unfold Binary.pair
  rw [block_eq]
  rfl
private theorem many_eq {α : Type} [BitstringEncoding α] {a : α → List Bool} (ha : a = BitstringEncoding.bitEncode) :
    Binary.many a = BitstringEncoding.bitEncode := by
  subst a
  funext xs
  change xs.flatMap _ = ((xs.map _).map _).flatten
  induction xs with
  | nil => rfl
  | cons x xs h =>
    simp only [List.flatMap_cons, List.map_cons, List.flatten_cons]
    exact congrArg₂ List.append (block_eq _) h
private theorem int_eq : Binary.integer = BitstringEncoding.bitEncode := by
  funext z
  unfold Binary.integer
  exact congrFun (pair_eq (a := encodeNat) (b := encodeNat) rfl rfl) _
private theorem rat_eq : Binary.rational = BitstringEncoding.bitEncode := by
  funext q
  unfold Binary.rational
  exact congrFun (pair_eq (b := encodeNat) int_eq rfl) _
private theorem input_bits_eq : Binary.input = BitstringEncoding.bitEncode :=
  pair_eq rfl (pair_eq (many_eq (pair_eq rat_eq rat_eq)) (many_eq (pair_eq rat_eq (many_eq (pair_eq rat_eq rat_eq)))))
private theorem output_bits_eq : Binary.output = BitstringEncoding.bitEncode :=
  pair_eq (many_eq rat_eq) (many_eq (many_eq rat_eq))
"""

MACHINE_CHECK = """open ComplexityTheory Kintali.Machine
example : Nonempty (Turing.TM2ComputableInPolyTime id id BitstringEncoding.delimit) := by
  simpa only [← funext block_eq] using Nonempty.intro Delimiter.polyTime
example {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (p : BitStacks.Program K L) (time : Polynomial ℕ)
    (runs : ∀ a : Input, ∃ (e : Output) (ticks : ℕ),
      ticks ≤ time.eval (Binary.input a).length ∧
      p.Steps ticks (p.init (Binary.input a)) (p.final (Binary.output e)) ∧
      (a.Valid → e = solve a)) : __UPSTREAM_PROPOSITION__ := by
  obtain ⟨f, poly, correct⟩ := exists_polyTime_bayesNash_of_runs p time runs
  refine ⟨f, ?_, correct⟩
  change Nonempty (Turing.TM2ComputableInPolyTime
    (BitstringEncoding.bitEncode (α := Input)) (BitstringEncoding.bitEncode (α := Output)) f)
  simpa only [input_bits_eq, output_bits_eq] using poly
"""

if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: check_upstream.py <formal-conjectures-checkout>")
    main(Path(sys.argv[1]))
