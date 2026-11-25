module

public import Kintali.Machine.BitStacks
public import Kintali.InputOutput.Binary
import Mathlib.Tactic.DeriveFintype

/-! # A Mathlib stack machine for the public binary block format

The main stack initially holds the payload. The scan moves it to a second
stack, seeds the main stack with the terminating zero, then emits the saved
bits in reverse scan order, each preceded by one. Both loops empty their
source stack. The program halts after exactly `5 * n + 4` instructions.
-/

@[expose] public section

namespace Kintali.Machine.Delimiter

open BitStacks InputOutput.Binary StateTransition

inductive Label where
  | scan
  | save (bit : Bool)
  | seed
  | emit
  | write (bit : Bool)
  | mark
  | done
  deriving DecidableEq, Fintype

def program : Program Bool Label where
  input := false
  output := false
  entry := .scan
  code
    | .scan => .pop false .seed (.save false) (.save true)
    | .save b => .push true b .scan
    | .seed => .push false false .emit
    | .emit => .pop true .done (.write false) (.write true)
    | .write b => .push false b .mark
    | .mark => .push false true .emit
    | .done => .halt

private def cells (main scratch : List Bool) : Bool → List Bool
  | false => main
  | true => scratch

private def cfg (pc : Option Label) (main scratch : List Bool) : Cfg Bool Label :=
  ⟨pc, cells main scratch⟩

@[simp] private theorem cells_false (xs ys : List Bool) : cells xs ys false = xs := rfl
@[simp] private theorem cells_true (xs ys : List Bool) : cells xs ys true = ys := rfl

@[simp] private theorem update_false (xs ys zs : List Bool) :
    Function.update (cells xs ys) false zs = cells zs ys := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_true (xs ys zs : List Bool) :
    Function.update (cells xs ys) true zs = cells xs zs := by
  funext k
  cases k <;> rfl

private theorem scan_bit (b : Bool) (xs ys : List Bool) :
    program.step (cfg (some .scan) (b :: xs) ys) = some (cfg (some (.save b)) xs ys) := by
  cases b <;> simp [cfg, Program.step, program, destination]

private theorem save_bit (b : Bool) (xs ys : List Bool) :
    program.step (cfg (some (.save b)) xs ys) = some (cfg (some .scan) xs (b :: ys)) := by
  simp [cfg, Program.step, program]

private theorem scan_empty (ys : List Bool) :
    program.step (cfg (some .scan) [] ys) = some (cfg (some .seed) [] ys) := by
  simp [cfg, Program.step, program, destination]

private theorem seed_zero (ys : List Bool) :
    program.step (cfg (some .seed) [] ys) = some (cfg (some .emit) [false] ys) := by
  simp [cfg, Program.step, program]

private theorem emit_bit (b : Bool) (xs ys : List Bool) :
    program.step (cfg (some .emit) xs (b :: ys)) = some (cfg (some (.write b)) xs ys) := by
  cases b <;> simp [cfg, Program.step, program, destination]

private theorem write_bit (b : Bool) (xs ys : List Bool) :
    program.step (cfg (some (.write b)) xs ys) = some (cfg (some .mark) (b :: xs) ys) := by
  simp [cfg, Program.step, program]

private theorem mark_bit (xs ys : List Bool) :
    program.step (cfg (some .mark) xs ys) = some (cfg (some .emit) (true :: xs) ys) := by
  simp [cfg, Program.step, program]

private theorem emit_empty (xs : List Bool) :
    program.step (cfg (some .emit) xs []) = some (cfg (some .done) xs []) := by
  simp [cfg, Program.step, program, destination]

private theorem stop (xs : List Bool) :
    program.step (cfg (some .done) xs []) = some (cfg none xs []) := rfl

private theorem scan (xs ys : List Bool) :
    program.Steps (2 * xs.length) (cfg (some .scan) xs ys)
      (cfg (some .scan) [] (xs.reverse ++ ys)) := by
  induction xs generalizing ys with
  | nil => simpa using Program.Steps.refl program (cfg (some .scan) [] ys)
  | cons b xs ih =>
    simpa [Nat.mul_add, List.append_assoc] using
      Program.Steps.head (scan_bit b xs ys) (Program.Steps.head (save_bit b xs ys) (ih (b :: ys)))

private def prefixBits (xs : List Bool) := xs.flatMap fun b => [true, b]

private theorem emit (xs ys : List Bool) :
    program.Steps (3 * ys.length) (cfg (some .emit) xs ys)
      (cfg (some .emit) (prefixBits ys.reverse ++ xs) []) := by
  induction ys generalizing xs with
  | nil => simpa [prefixBits] using Program.Steps.refl program (cfg (some .emit) xs [])
  | cons b ys ih =>
    simpa [Nat.mul_add, prefixBits, List.flatMap_append, List.append_assoc] using
      Program.Steps.head (emit_bit b xs ys) (Program.Steps.head (write_bit b xs ys)
        (Program.Steps.head (mark_bit (b :: xs) ys) (ih (true :: b :: xs))))

private theorem prefix_terminator (xs : List Bool) : prefixBits xs ++ [false] = block xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa [prefixBits, block] using congrArg (fun ys => true :: b :: ys) ih

private theorem init_eq (xs : List Bool) : program.init xs = cfg (some .scan) xs [] := by
  unfold Program.init cfg
  congr 1
  funext k
  cases k <;> rfl

private theorem final_eq (xs : List Bool) : program.final xs = cfg none xs [] := by
  unfold Program.final cfg
  congr 1
  funext k
  cases k <;> rfl

theorem steps (xs : List Bool) : program.Steps (5 * xs.length + 4)
    (program.init xs) (program.final (block xs)) := by
  rw [init_eq, final_eq]
  have scanRun := scan xs []
  have emitRun := emit [false] xs.reverse
  simp only [List.append_nil] at scanRun
  simp only [List.length_reverse, List.reverse_reverse, prefix_terminator] at emitRun
  have haltRun := Program.Steps.head (emit_empty (block xs))
    (Program.Steps.head (stop (block xs)) (Program.Steps.refl program _))
  have afterScan := Program.Steps.head (scan_empty xs.reverse)
    (Program.Steps.head (seed_zero xs.reverse) (emitRun.trans haltRun))
  convert scanRun.trans afterScan using 1
  omega

/-- A fixed Mathlib machine for the shared public delimiter, on raw bit stacks. -/
noncomputable def polyTime : Turing.TM2ComputableInPolyTime id id block :=
  program.polyTime id id block (5 * Polynomial.X + 4) fun xs =>
    { steps := 5 * xs.length + 4
      evals_in_steps := steps xs
      steps_le_m := by simp }

end Kintali.Machine.Delimiter
