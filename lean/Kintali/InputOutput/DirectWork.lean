module

public import Kintali.InputOutput.DirectWorkResponse
public import Kintali.InputOutput.CodecWorkSolver

/-! # The complete direct branch on the public binary input

The detector runs once. The output stores each defense indicator and computes
one least-index best response per attacker row. All typed traversals,
comparisons, and the materialized compact output are charged.
-/

@[expose] public section
namespace Kintali.InputOutput.DirectWork

open Binary StochasticGames.CompilerRun StochasticGames.BinarySize

def typeIDs (a : Input) : Run (List (Fin a.types)) := indices a.2.2
@[simp] theorem typeIDs_value (a : Input) : (typeIDs a).value = List.finRange a.types := indices_value _

def covered (a : Input) (d : List (Fin a.targets)) (j : Fin a.targets) : Run ℚ := do
  let b ← member j d
  step 0 (if b then 1 else 0)

@[simp] theorem covered_value (a : Input) (j : Fin a.targets) :
    (covered a (chosen a) j).value = coverage a j := by simp [covered,coverage,chosen_mem]

def flag {m : ℕ} (winner : Option (Fin m)) (j : Fin m) : Run ℚ :=
  match winner with
  | none => step 0 0
  | some b => step (max j.val.size b.val.size) (if j = b then 1 else 0)

theorem flag_work {m S : ℕ} (winner : Option (Fin m)) (j : Fin m) (h : m ≤ S) :
    (flag winner j).Bound 1 (width S) := by
  cases winner with
  | none => exact (bound_step _ _).weaken le_rfl (Nat.zero_le _)
  | some b =>
    have js := (size_le_self j.val).trans (j.isLt.le.trans h)
    have bs := (size_le_self b.val).trans (b.isLt.le.trans h)
    exact (bound_step _ _).weaken le_rfl (by unfold width; omega)

def row (a : Input) (d js : List (Fin a.targets)) (i : Fin a.types) : Run (List ℚ) := do
  let h ← best a d i js
  StochasticGames.CompilerRun.mapM (flag h) js

theorem row_value (a : Input) (hm : 0 < a.targets) (i : Fin a.types) :
    (row a (chosen a) (List.finRange a.targets) i).value = List.ofFn ((a.game.earlyStrategy hm).attacks i) := by
  rw [row,Run.bind_value,best_value a hm i,mapM_value,List.ofFn_eq_map]
  rfl

def rowSlots (S : ℕ) := S*(6*S+12)+2+3*S+1

theorem row_work (a : Input) (v : a.Valid) (i : Fin a.types) :
    (row a (chosen a) (List.finRange a.targets) i).Bound (rowSlots (lengthInput a)) (width (lengthInput a)) := by
  let js := List.finRange a.targets
  have jl : js.length ≤ lengthInput a := by simpa [js] using (dimensions a).1
  have b := best_work a v i jl
  have f := mapM_bound (flag (best a (chosen a) i js).value) js 1 (width (lengthInput a))
    (fun j _ => flag_work _ j (dimensions a).1)
  simp only [row,Run.Bound,Run.bind_width,Run.bind_slots,rowSlots] at *
  change _ ≤ _ ∧ _ ≤ _
  dsimp only [js] at *
  omega

def strategy (a : Input) (d : List (Fin a.targets)) : Run Output := do
  let js ← targetIDs a
  let is ← typeIDs a
  let x ← StochasticGames.CompilerRun.mapM (covered a d) js
  let q ← StochasticGames.CompilerRun.mapM (row a d js) is
  step 0 (x,q)

theorem strategy_value (a : Input) (hm : 0 < a.targets) :
    (strategy a (chosen a)).value = writeStrategy (a.game.earlyStrategy hm) := by
  simp only [strategy,Run.bind_value,typeIDs_value,targetIDs_value,mapM_value,
    covered_value,row_value a hm,step_value,writeStrategy,List.ofFn_eq_map]
  rfl

def strategySlots (S : ℕ) := 2*(3*S+2)+(S*(S+4)+1)+(S*(rowSlots S+2)+1)+1

theorem strategy_work (a : Input) (v : a.Valid) :
    (strategy a (chosen a)).Bound (strategySlots (lengthInput a)) (width (lengthInput a)) := by
  let S := lengthInput a
  have md : a.targets ≤ S := (dimensions a).1
  have kd : a.types ≤ S := (dimensions a).2.1
  have tt : (targetIDs a).Bound (3*S+2) (width S) := indices_work _ md
  have ii : (typeIDs a).Bound (3*S+2) (width S) := indices_work _ kd
  have cc (j : Fin a.targets) : (covered a (chosen a) j).Bound (S+2) (width S) := by
    have mem := member_work j (chosen a) md
    have len := chosen_length a v
    simp only [covered,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width] at *
    dsimp only [S] at *
    omega
  have cov := mapM_bound (covered a (chosen a)) (List.finRange a.targets) (S+2) (width S) (fun j _ => cc j)
  have rows := mapM_bound (row a (chosen a) (List.finRange a.targets)) (List.finRange a.types)
    (rowSlots S) (width S) (fun i _ => row_work a v i)
  simp only [List.length_finRange] at cov rows
  have cs := cov.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ md) 1)
  change _ ≤ S*(S+4)+1 at cs
  have rs := rows.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ kd) 1)
  simp only [strategy,Run.Bound,Run.bind_slots,Run.bind_width,targetIDs_value,typeIDs_value,
    step_slots,step_width,strategySlots] at *
  change _ ≤ 2*(3*S+2)+(S*(S+4)+1)+(S*(rowSlots S+2)+1)+1 ∧ _ ≤ width S
  omega

/-- Dispatch to a supplied interior implementation only when the charged test fails. -/
def dispatch (interior : Input → Run Output) (a : Input) : Run Output := do
  let p ← plan a
  match ← step 0 p.1 with
  | true => strategy a p.2
  | false => interior a

theorem dispatch_direct (interior : Input → Run Output) (a : Input) (v : a.Valid) (d : a.game.DirectCase) :
    (dispatch interior a).value = solve a := by
  simp [dispatch,plan_value,d,strategy_value a v.1,solve,Game.solve,Game.solveWithTrials,v.1]

theorem dispatch_interior (interior : Input → Run Output) (a : Input) (normal : ¬a.game.DirectCase) :
    (dispatch interior a).value = (interior a).value := by simp [dispatch,plan_value,normal]

def directSlots (S : ℕ) := planSlots S+1+strategySlots S

theorem dispatch_direct_work (interior : Input → Run Output) (a : Input) (v : a.Valid) (d : a.game.DirectCase) :
    (dispatch interior a).Bound (directSlots (lengthInput a)) (width (lengthInput a)) := by
  have p := plan_work a v
  have q := strategy_work a v
  simp [dispatch,Run.Bound,plan_value,d,directSlots] at *
  omega

theorem dispatch_interior_work (interior : Input → Run Output) (a : Input) (v : a.Valid) (normal : ¬a.game.DirectCase)
    {k w : ℕ} (cost : (interior a).Bound k w) : (dispatch interior a).Bound (planSlots (lengthInput a)+1+k)
    (max (width (lengthInput a)) w) := by
  have p := plan_work a v
  simp [dispatch,Run.Bound,plan_value,normal] at *
  omega

def directLength (S : ℕ) := 34*S+1+S*(34*S+1)

theorem direct_output_length (a : Input) (v : a.Valid) (d : a.game.DirectCase) :
    (output (solve a)).length ≤ directLength (lengthInput a) := by
  let s := a.game.earlyStrategy v.1
  have cov (j : Fin a.targets) : (s.coverage j).num.natAbs.size ≤ 1 ∧ (s.coverage j).den.size ≤ 1 := by
    dsimp [s,Game.earlyStrategy]
    split <;> decide
  have att (i : Fin a.types) (j : Fin a.targets) :
      (s.attacks i j).num.natAbs.size ≤ 1 ∧ (s.attacks i j).den.size ≤ 1 := by
    dsimp [s,Game.earlyStrategy]
    split <;> decide
  have h := strategy_width s cov att
  have e : solve a = writeStrategy s := by simp [s,solve,Game.solve,Game.solveWithTrials,v.1,d]
  rw [e]
  apply h.trans
  change 2*(a.targets*17)+1+a.types*(2*(a.targets*17)+1) ≤ directLength (lengthInput a)
  have mt := Nat.mul_le_mul_left 34 (dimensions a).1
  change _ ≤ 34*lengthInput a+1+lengthInput a*(34*lengthInput a+1)
  rw [show 2*(a.targets*17)=34*a.targets by ring]
  gcongr
  exact (dimensions a).2.1

theorem bits_correct (interior : Input → Run Output) (a : Input) (v : a.Valid) (d : a.game.DirectCase) :
    let S := lengthInput a
    let r := CodecWork.solveRun (dispatch interior) (input a)
    r.value = solveBits (input a) ∧ outputCodec.decode r.value = some (solve a) ∧ a.IsBayesNash (solve a) ∧
    LinearProgramming.RecoveryRun.binaryWork S r.work ≤ CodecWork.binaryLimit S
      (CodecWork.solveSlots S (directSlots S) (directLength S)) (CodecWork.solveWidth S (width S) (directLength S)) :=
  CodecWork.solveRun_correct _ a v (dispatch_direct interior a v d) (dispatch_direct_work interior a v d)
    (direct_output_length a v d)

end Kintali.InputOutput.DirectWork
