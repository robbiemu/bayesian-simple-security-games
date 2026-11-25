module

public import Mathlib.Computability.TuringMachine.Computable

/-! # Finite programs on bit stacks

A program has finitely many labels and stacks. Each instruction can branch on
the top bit, pop or push one bit, jump, or halt. The compiler uses one Mathlib
`FinTM2.step` per instruction and resets its temporary register at every jump.
The output theorem requires the exact Mathlib final configuration with empty
scratch stacks.
-/

@[expose] public section

namespace Kintali.Machine.BitStacks

open Turing StateTransition

inductive Instr (K L : Type) where
  | jump (next : L)
  | push (stack : K) (bit : Bool) (next : L)
  | peek (stack : K) (empty zero one : L)
  | pop (stack : K) (empty zero one : L)
  | halt

structure Program (K L : Type) where
  input : K
  output : K
  entry : L
  code : L → Instr K L

structure Cfg (K L : Type) where
  label : Option L
  store : K → List Bool

variable {K L : Type} [DecidableEq K]

def destination (empty zero one : L) : Option Bool → L
  | none => empty
  | some false => zero
  | some true => one

def Program.step (p : Program K L) (c : Cfg K L) : Option (Cfg K L) :=
  c.label.map fun l =>
    match p.code l with
    | .jump next => ⟨some next, c.store⟩
    | .push k b next => ⟨some next, Function.update c.store k (b :: c.store k)⟩
    | .peek k empty zero one =>
      ⟨some (destination empty zero one (c.store k).head?), c.store⟩
    | .pop k empty zero one =>
      ⟨some (destination empty zero one (c.store k).head?),
        Function.update c.store k (c.store k).tail⟩
    | .halt => ⟨none, c.store⟩

def Program.init (p : Program K L) (xs : List Bool) : Cfg K L :=
  ⟨some p.entry, fun k => if k = p.input then xs else []⟩

def Program.final (p : Program K L) (ys : List Bool) : Cfg K L :=
  ⟨none, fun k => if k = p.output then ys else []⟩

/-- Exactly `n` instructions take configuration `a` to configuration `b`. -/
def Program.Steps (p : Program K L) (n : ℕ) (a b : Cfg K L) : Prop :=
  (flip Bind.bind p.step)^[n] (some a) = some b

theorem Program.Steps.refl (p : Program K L) (c : Cfg K L) : p.Steps 0 c c := rfl

theorem Program.Steps.head {p : Program K L} {n : ℕ} {a b c : Cfg K L}
    (h : p.step a = some b) (tail : p.Steps n b c) : p.Steps (n + 1) a c := by
  unfold Program.Steps
  rw [Function.iterate_succ_apply]
  change (flip Bind.bind p.step)^[n] (p.step a) = some c
  rw [h]
  exact tail

theorem Program.Steps.trans {p : Program K L} {n m : ℕ} {a b c : Cfg K L}
    (h : p.Steps n a b) (tail : p.Steps m b c) : p.Steps (n + m) a c := by
  unfold Program.Steps at *
  rw [Nat.add_comm, Function.iterate_add_apply, h, tail]

abbrev Stmt (K L : Type) := TM2.Stmt (fun _ : K => Bool) L (Option Bool)

def jumpReset (l : L) : Stmt K L := .load (fun _ => none) (.goto fun _ => l)

def dispatch (empty zero one : L) : Stmt K L :=
  .branch Option.isSome
    (.branch (fun v => v.getD false) (jumpReset one) (jumpReset zero)) (jumpReset empty)

def compile : Instr K L → Stmt K L
  | .jump l => .goto fun _ => l
  | .push k b l => .push k (fun _ => b) (.goto fun _ => l)
  | .peek k empty zero one => .peek k (fun _ b => b) (dispatch empty zero one)
  | .pop k empty zero one => .pop k (fun _ b => b) (dispatch empty zero one)
  | .halt => .halt

variable [Fintype K] [Fintype L]

def Program.machine (p : Program K L) : FinTM2 where
  K := K
  k₀ := p.input
  k₁ := p.output
  Γ _ := Bool
  Λ := L
  main := p.entry
  σ := Option Bool
  initialState := none
  m l := compile (p.code l)

def Program.embed (p : Program K L) (c : Cfg K L) : p.machine.Cfg :=
  ⟨c.label, none, c.store⟩

theorem Program.step_embed (p : Program K L) (c : Cfg K L) :
    p.machine.step (p.embed c) = (p.step c).map p.embed := by
  obtain ⟨_ | l, cells⟩ := c
  · rfl
  change some (TM2.stepAux (compile (p.code l)) none cells) = _
  cases h : p.code l with
  | jump next | push _ _ next | halt => simp [Program.step, h, compile, Program.embed]; rfl
  | peek k empty zero one | pop k empty zero one =>
    cases ht : (cells k).head? with
    | none => simp [Program.step, h, compile, dispatch, jumpReset, ht, destination, Program.embed]; rfl
    | some b => cases b <;>
        simp [Program.step, h, compile, dispatch, jumpReset, ht, destination, Program.embed] <;> rfl

private theorem Program.iterate_embed (p : Program K L) (n : ℕ) (c : Option (Cfg K L)) :
    (flip Bind.bind p.machine.step)^[n] (c.map p.embed) =
      ((flip Bind.bind p.step)^[n] c).map p.embed := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    cases c with
    | none => exact ih none
    | some c =>
      change (flip Bind.bind p.machine.step)^[n] (p.machine.step (p.embed c)) = _
      rw [p.step_embed]
      exact ih (p.step c)

private theorem Program.embed_init (p : Program K L) (xs : List Bool) :
    p.embed (p.init xs) = initList p.machine xs := by
  unfold Program.embed Program.init initList
  congr 1

private theorem Program.embed_final (p : Program K L) (ys : List Bool) :
    p.embed (p.final ys) = haltList p.machine ys := by
  unfold Program.embed Program.final haltList
  congr 1

/-- An instruction execution gives a Mathlib execution with the same step count. -/
def Program.outputs (p : Program K L) (xs ys : List Bool) {t : ℕ}
    (run : EvalsToInTime p.step (p.init xs) (some (p.final ys)) t) :
    TM2OutputsInTime p.machine xs (some ys) t where
  steps := run.steps
  steps_le_m := run.steps_le_m
  evals_in_steps := by
    change (flip Bind.bind p.machine.step)^[run.steps] (some (initList p.machine xs)) =
      some (haltList p.machine ys)
    rw [← p.embed_init, ← p.embed_final]
    exact (p.iterate_embed run.steps (some (p.init xs))).trans
      (congrArg (Option.map p.embed) run.evals_in_steps)

/-- Supply one fixed finite program and bound actual executions on each encoded input. -/
def Program.polyTime {α β : Type} (p : Program K L) (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (time : Polynomial ℕ)
    (run : ∀ a, EvalsToInTime p.step (p.init (ea a)) (some (p.final (eb (f a))))
      (time.eval (ea a).length)) : TM2ComputableInPolyTime ea eb f where
  tm := p.machine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := time
  outputsFun a := by
    change TM2OutputsInTime p.machine ((ea a).map (id : Bool → Bool))
      (some ((eb (f a)).map (id : Bool → Bool))) _
    simpa only [Program.machine, List.map_id] using p.outputs (ea a) (eb (f a)) (run a)

end Kintali.Machine.BitStacks
