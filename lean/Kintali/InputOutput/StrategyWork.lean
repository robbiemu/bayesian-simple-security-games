module

public import Kintali.InputOutput.CodecWorkOutput
public import Kintali.InputOutput.Solver
public import StochasticGames.CompilerRun

/-! # Writing stored strategy vectors to the public compact lists

The exact repair's strategy retains a coverage vector and a vector of attack
rows. This writer copies each stored rational by reference and constructs
the lists. The public bit encoder separately writes each rational.
-/

@[expose] public section
namespace Kintali.InputOutput.StrategyWork

open StochasticGames.CompilerRun StochasticGames.BinarySize

def row {m : ℕ} (xs : Vector ℚ m) (indices : List (Fin m)) : Run (List ℚ) :=
  StochasticGames.CompilerRun.mapM (fun j => step m.size xs[j.val]) indices

@[simp] theorem row_value {m : ℕ} (xs : Vector ℚ m) :
    (row xs (List.finRange m)).value = List.ofFn (fun j : Fin m => xs[j.val]) := by simp [row,List.ofFn_eq_map]

def run {k m : ℕ} (x : Vector ℚ m) (q : Vector (Vector ℚ m) k) : Run Output := do
  let js ← finRange m
  let is ← finRange k
  let coverage ← row x js
  let attacks ← StochasticGames.CompilerRun.mapM (fun i : Fin k => do
    let v ← step k.size q[i.val]
    row v js) is
  step 0 (coverage,attacks)

theorem run_value {k m : ℕ} (x : Vector ℚ m) (q : Vector (Vector ℚ m) k) :
    (run x q).value = writeStrategy (⟨fun j => x[j.val],fun i j => q[i.val][j.val]⟩ : Strategy k m) := by
  simp [run,writeStrategy,List.ofFn_eq_map]

def slots (S : ℕ) := 2*(2*S+1)+(3*S+1)+(S*(3*S+4)+1)+1

theorem run_work {k m S : ℕ} (x : Vector ℚ m) (q : Vector (Vector ℚ m) k) (kd : k ≤ S) (md : m ≤ S) :
    (run x q).Bound (slots S) S := by
  have kw := (size_le_self _).trans kd
  have mw := (size_le_self _).trans md
  have r (v : Vector ℚ m) : (row v (List.finRange m)).Bound (3*S+1) S := by
    apply (mapM_bound _ _ 1 S (fun j _ => (bound_step _ _).weaken le_rfl mw)).weaken _ le_rfl
    simp [Nat.mul_comm]
    omega
  have a := mapM_bound (fun i : Fin k => step k.size q[i.val] >>= (fun v => row v (List.finRange m)))
    (List.finRange k) (1+(3*S+1)) S (fun i _ => bound_bind ((bound_step _ _).weaken le_rfl kw) (r q[i.val]))
  have rs := r x
  have ir := finRange_bound k
  have jr := finRange_bound m
  have pr := Nat.mul_le_mul_right (3*S+4) kd
  simp only [run,Run.Bound,Run.bind_slots,Run.bind_width,finRange_value,step_slots,step_width,List.length_finRange,slots] at *
  rw [show 1+(3*S+1)+2=3*S+4 by omega] at a
  omega

end Kintali.InputOutput.StrategyWork
