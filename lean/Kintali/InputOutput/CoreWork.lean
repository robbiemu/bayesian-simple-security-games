module

public import Kintali.SolverWork
public import Kintali.InputOutput.DirectWork
public import Kintali.ContactSize.Polynomial

/-! # Composing preparation, the quote driver and public output

The composition consumes measured implementations of the interior
preparation and trials. The direct cases and all loop control are
computed here.
-/

@[expose] public section

namespace Kintali.InputOutput.CoreWork

open StochasticGames.CompilerRun
open LinearProgramming.ArithmeticRun
open MarketTrial QuoteSearch

def initialWork {n : ℕ} (q : Vector ℕ n) : Run (WeightTable n) :=
  tabulate n fun i => do
    let count ← step n.size q[i.val]
    let empty ← step count.size (count == 0)
    step 0 (if empty then [] else [⟨count,0⟩])

@[simp] theorem initialWork_value {n : ℕ} (q : Vector ℕ n) :
    (initialWork q).value = initialTable q := by
  simp [initialWork, initialTable, Runs.initial]

theorem initialWork_bound {n w : ℕ} (q : Vector ℕ n)
    (idx : n.size ≤ w) (words : ∀ i : Fin n, q[i].size ≤ w) :
    (initialWork q).Bound (3*(n+1)+3*n) w := by
  rw [Nat.mul_comm 3 n]
  unfold initialWork
  apply tabulate_bound _ idx
  intro i
  exact ⟨le_rfl, max_le idx (max_le (words i) (Nat.zero_le w))⟩

structure Prepared (a : Input) where
  quantiles : ℕ
  trials : ℕ
  quotes : Vector ℕ (a.types*a.targets)

def prepared (a : Input) (hm : 0 < a.targets) : Prepared a :=
  let H := witnessBound a.game
  let G := grid a.game
  ⟨4*H, 2*H*(G.log2+1), eligible a.game hm⟩

abbrev TrialFor (a : Input) :=
  Prepared a → DriverWork.ChargedTrial (a.types*a.targets) (Strategy a.types a.targets)

def interior (a : Input) (setup : Run (Prepared a)) (trial : TrialFor a)
    (emit : Strategy a.types a.targets → Run Output) : Run Output := do
  let P ← setup
  let weights ← initialWork P.quotes
  let result ← DriverWork.search P.quantiles (trial P) P.trials weights
  match ← step 0 result with
  | none => step 0 ([],[])
  | some answer => emit answer

theorem interior_value (a : Input) (hm : 0 < a.targets) (normal : ¬a.game.DirectCase)
    (setup : Run (Prepared a)) (trial : TrialFor a)
    (emit : Strategy a.types a.targets → Run Output)
    (setupEq : setup.value = prepared a hm)
    (trialEq : ∀ s, (trial (prepared a hm) s).value =
      MarketTrial.run a.game hm (sparseView a.game hm) s)
    (emitEq : ∀ s, (emit s).value = writeStrategy s) :
    (interior a setup trial emit).value = solve a := by
  have eq := InputOutput.interior_value a hm normal (trial (prepared a hm)) trialEq
  change (DriverWork.search (prepared a hm).quantiles (trial (prepared a hm))
    (prepared a hm).trials (initialTable (prepared a hm).quotes)).value = a.game.solve hm at eq
  simp only [interior, Run.bind_value, setupEq, initialWork_value, step_value, eq, solve, dite_eq_left hm]
  cases a.game.solve hm <;> simp [emitEq]

def interiorSlots (L setupSlots trialSlots emitSlots : ℕ) : ℕ :=
  setupSlots + (3*(L*L+1)+3*(L*L)) + searchSlots L trialSlots + emitSlots + 2

theorem interior_work (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (setup : Run (Prepared a)) (trial : TrialFor a)
    (emit : Strategy a.types a.targets → Run Output)
    (setupEq : setup.value = prepared a valid.1)
    (trialEq : ∀ s, (trial (prepared a valid.1) s).value =
      MarketTrial.run a.game valid.1 (sparseView a.game valid.1) s)
    {S C E W : ℕ}
    (setupWork : setup.Bound S W)
    (trialWork : ∀ s, ValidSelection (prepared a valid.1).quantiles (prepared a valid.1).quotes s →
      (trial (prepared a valid.1) s).Bound C W)
    (emitWork : ∀ s, a.game.IsBayesNash s.coverage s.attacks → (emit s).Bound E W) :
    (interior a setup trial emit).Bound (interiorSlots (Binary.lengthInput a) S C E)
      (searchWidth (Binary.lengthInput a) + W) := by
  let L := Binary.lengthInput a
  let P := prepared a valid.1
  let count := a.types*a.targets
  let Width := searchWidth L + W
  let r := DriverWork.search P.quantiles (trial P) P.trials (initialTable P.quotes)
  have vg : a.game.Valid := ((a.valid_iff).mp valid).1
  have spec := prepare_correct a.game vg normal (sparseView a.game valid.1)
    (fun s _ => sparseView_matches a.game vg normal s)
  have fits : (grid a.game).size ≤ Binary.gridBitBound L := Binary.grid_size a valid
  have dims := Binary.dimensions a
  have countLimit : count ≤ L*L := Nat.mul_le_mul dims.2.1 dims.1
  have idx := (StochasticGames.BinarySize.size_le_self count).trans countLimit
  have gridWidth : (grid a.game).size ≤ Width := by unfold Width searchWidth; omega
  have idxWidth : count.size ≤ Width := by unfold Width searchWidth; omega
  have qbits (j : Fin count) : P.quotes[j].size ≤ Width :=
    (Nat.size_le_size (spec.2.1 j)).trans gridWidth
  have init := initialWork_bound P.quotes idxWidth qbits
  have run := InputOutput.interior_work a valid normal (trial P) trialEq trialWork
  change r.Bound (searchSlots L C) Width at run
  have eq := InputOutput.interior_value a valid.1 normal (trial P) trialEq
  change r.value = a.game.solve valid.1 at eq
  obtain ⟨s, hx, hs⟩ := a.game.solve_correct vg
  have actual : r.value = some s := eq.trans hx
  have emitB := emitWork s hs
  have setupB := setupWork.weaken le_rfl (Nat.le_add_left W (searchWidth L))
  have width : W ≤ Width := Nat.le_add_left _ _
  let finishRun : Option (Strategy a.types a.targets) → Run Output := fun
    | none => step 0 ([],[])
    | some x => emit x
  have finish : (step 0 r.value >>= finishRun).Bound (1+E) Width := by
    rw [actual]
    exact ⟨Nat.add_le_add_left emitB.1 _, max_le (Nat.zero_le _) (emitB.2.trans width)⟩
  have quoteRun : (r >>= fun result => step 0 result >>= finishRun).Bound
      (searchSlots L C + (1+E)) Width :=
    bound_bind (f := fun result => step 0 result >>= finishRun) run finish
  let restart (Y : WeightTable count) :=
    DriverWork.search P.quantiles (trial P) P.trials Y >>= fun result => step 0 result >>= finishRun
  have body : (restart (initialWork P.quotes).value).Bound (searchSlots L C + (1+E)) Width := by
    rw [initialWork_value]
    exact quoteRun
  have all := bound_bind (f := restart) init body
  have go : (interior a setup trial emit).Bound
      (S + ((3*(count+1)+3*count) + (searchSlots L C + (1+E)))) Width := by
    unfold interior
    refine bound_bind setupB ?_
    rw [setupEq]
    exact all
  refine go.weaken ?_ le_rfl
  have h := Nat.mul_le_mul_left 6 countLimit
  change _ ≤ interiorSlots L S C E
  unfold interiorSlots
  omega


end Kintali.InputOutput.CoreWork
