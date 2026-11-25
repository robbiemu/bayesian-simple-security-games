module

public import Kintali.InputOutput.PrepareWork
public import Kintali.InputOutput.ToleranceWork

/-! # Initializing the restricted market on the public payoff tables

Compute and retain the normalized fields, contact tolerance, grid and private
scale, least outside targets and costs, witness bound, and eligible prefixes.
The input is an already decoded table. All these computations are priced
before a restricted trial is started.
-/

@[expose] public section
namespace Kintali.InputOutput.InitializationWork

open Binary NormalizedWork ExactRecovery MarketTrial TrialWork StochasticGames.CompilerRun

structure State (k m : ℕ) where
  tables : Tables k m
  tolerance : ℚ
  denominator : ℕ
  coefficient : ℕ
  prepared : PrepareWork.Prepared k m

def finish {k m : ℕ} (t : Tables k m) (hm : 0 < m) : Run (State k m) := do
  let constants ← ToleranceWork.parameters t
  let p ← PrepareWork.fromTables t hm constants.tolerance
  step 0 ⟨t,constants.tolerance,constants.denominator,constants.coefficient,p⟩

/-- Only the erased indices change. The runtime dimensions are read from the
materialized vectors once and supplied to all downstream tabulations. -/
def atShape (build : ∀ {k m}, Tables k m → (0 < m) → Run (State k m)) {k m K M : ℕ} (hk : K = k) (hM : M = m) (t : Tables k m) (pos : 0 < m) : Run (State k m) :=
  let source : Tables K M := hk.symm ▸ hM.symm ▸ t
  let p := build source (hM.symm ▸ pos)
  ⟨hk ▸ hM ▸ p.value,p.work⟩

theorem atShape_eq (build : ∀ {k m}, Tables k m → (0 < m) → Run (State k m)) {k m K M : ℕ} (hk : K = k) (hM : M = m) (t : Tables k m) (pos : 0 < m) :
    atShape build hk hM t pos = build t pos := by subst K; subst M; rfl

def stored {k m : ℕ} (t : Tables k m) (pos : 0 < m) : Run (State k m) :=
  let buyers := step 0 t.priors.toArray.size
  let sites := step 0 t.gains.toArray.size
  let init := atShape finish (K := buyers.value) (M := sites.value) t.priors.size_toArray t.gains.size_toArray t pos
  ⟨init.value,buyers.work.seq (sites.work.seq init.work)⟩

def run (a : Input) (hm : 0 < a.targets) : Run (State a.types a.targets) := NormalizedWork.run a >>= (stored · hm)

theorem run_tables (a : Input) (hm : 0 < a.targets) :
    (run a hm).value.tables = (NormalizedWork.run a).value := by simp [run,stored,atShape_eq,finish]

structure Correct (a : Input) (hm : 0 < a.targets) (s : State a.types a.targets) : Prop where
  game : s.tables.game = a.game
  fields : FieldBound s.tables.fields 2 (2*lengthInput a+1)
  tolerance : s.tolerance = contactTolerance a.game
  denominator : s.denominator = ExactRecovery.denominator a.game
  coefficient : s.coefficient = coefficientHeight a.game
  grid : s.prepared.scales.grid = MarketTrial.grid a.game
  privateScale : s.prepared.scales.privateScale = MarketTrial.privateScale a.game
  witness : s.prepared.witness = witnessBound a.game
  counts : s.prepared.counts = eligible a.game hm
  targets : ∀ i : Fin a.types, s.prepared.directory.toSite[i.val] = redirect a.game hm i
  prices : ∀ i : Fin a.types, s.prepared.directory.price[i.val] = Holdings.outsideCost a.game (redirect a.game hm) i

theorem run_correct (a : Input) (v : a.Valid) : Correct a v.1 (run a v.1).value := by
  let t := (NormalizedWork.run a).value
  have eq : t.game = a.game := NormalizedWork.run_value a
  obtain ⟨gr,sc,wi,co,re⟩ := PrepareWork.fromTables_value a v.1 t eq
  have ft := fields_bound a v t eq
  have pr (i : Fin a.types) := OutsideWork.prices t.fields v.1 i
  simp only [Tables.fields_game,eq] at pr
  change Correct a v.1 (stored t v.1).value
  simp only [stored,atShape_eq,finish,Run.bind_value,step_value,ToleranceWork.parameters_value,eq]
  exact ⟨eq,ft,rfl,rfl,rfl,gr,sc,wi,co,re,pr⟩

def slots (S : ℕ) := NormalizedWork.tableSlots S+2+ToleranceWork.setupSlots S+PrepareWork.setupSlots S+1
def width (S : ℕ) := scalarWidth S+ToleranceWork.setupWidth S+PrepareWork.setupWidth S

theorem run_work (a : Input) (v : a.Valid) :
    (run a v.1).Bound (slots (lengthInput a)) (width (lengthInput a)) := by
  let t := (NormalizedWork.run a).value
  have eq : t.game = a.game := NormalizedWork.run_value a
  have n := NormalizedWork.run_work a v
  have tol := ToleranceWork.parameters_work a v t eq
  have p := PrepareWork.fromTables_work a v t eq
  have tv : (ToleranceWork.parameters t).value.tolerance = contactTolerance a.game := by
    rw [ToleranceWork.parameters_value,eq]
  simp only [run,stored,atShape_eq,finish,Run.Bound,Run.bind_slots,Run.bind_width,
    Work.seq,Work.one,step,slots,width] at *
  dsimp only [t] at *
  rw [tv]
  omega

theorem run_binary_work (a : Input) (v : a.Valid) :
    LinearProgramming.RecoveryRun.binaryWork (lengthInput a) (run a v.1).work ≤
      CodecWork.binaryLimit (lengthInput a) (slots (lengthInput a)) (width (lengthInput a)) :=
  CodecWork.addressed_bound _ (run_work a v)

end Kintali.InputOutput.InitializationWork
