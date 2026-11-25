module

public import Kintali.InputOutput.InventorySearch
public import Kintali.InputOutput.InitializationPolynomial
public import Kintali.TrialWork.TrialPolynomial

/-! # The binary word-cost bound for the surrounding search

A supplied contact evaluator is called on the materialized inventory.
The same initialization and search implementation occurs in the value
and work theorems.
-/

@[expose] public section

namespace Kintali.InputOutput.CheckedSearch

open StochasticGames.CompilerRun StochasticGames.BinarySize
open MarketTrial QuoteSearch

abbrev Provider (a : Input) (hm : 0 < a.targets) :=
  (state : InitializationWork.State a.types a.targets) →
    InitializationWork.Correct a hm state → InventorySearch.Contact a state

def Provider.Agrees (a : Input) (hm : 0 < a.targets) (contact : Provider a hm) : Prop :=
  ∀ state good, InventorySearch.Contact.Value a state (contact state good)

def Provider.Bound (a : Input) (hm : 0 < a.targets) (contact : Provider a hm) (C W : ℕ) : Prop :=
  ∀ state good s, ValidSelection (4*witnessBound a.game) (eligible a.game hm) s →
    ∀ list, (contact state good s list).Bound C W

def interior (a : Input) (valid : a.Valid) (contact : Provider a valid.1) : Run Output :=
  let init := InitializationWork.run a valid.1
  let correct := InitializationWork.run_correct a valid
  let search := CoreWork.interior a (PlanWork.clock a init.value.prepared)
    (fun _ => InventorySearch.trial a valid.1 init.value correct (contact init.value correct))
    InventorySearch.emit
  ⟨search.value, init.work.seq search.work⟩

set_option maxHeartbeats 1000000 in
theorem interior_value (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (contact : Provider a valid.1) (agree : Provider.Agrees a valid.1 contact) :
    (interior a valid contact).value = solve a := by
  let state := (InitializationWork.run a valid.1).value
  let good := InitializationWork.run_correct a valid
  exact CoreWork.interior_value a valid.1 normal (PlanWork.clock a state.prepared)
    (fun _ => InventorySearch.trial a valid.1 state good (contact state good)) InventorySearch.emit
    (PlanWork.clock_value a valid.1 state.prepared good.grid good.witness good.counts)
    (InventorySearch.trial_value a valid.1 state good (contact state good) (agree state good))
    InventorySearch.emit_value

def leadWidth (L W : ℕ) :=
  PlanWork.clockWidth (Binary.gridBitBound L) (Binary.witnesses L) +
    InventorySearch.trialWidth L W + 2*L

def slots (L C : ℕ) :=
  InitializationWork.slots L + CoreWork.interiorSlots L (PlanWork.clockSlots (Binary.gridBitBound L))
    (InventorySearch.trialSlots L C) (InventorySearch.emitSlots L)

def width (L W : ℕ) :=
  InitializationWork.width L + searchWidth L + leadWidth L W

theorem interior_work (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (contact : Provider a valid.1) (agree : Provider.Agrees a valid.1 contact) {C W : ℕ}
    (charge : Provider.Bound a valid.1 contact C W) :
    (interior a valid contact).Bound (slots (Binary.lengthInput a) C) (width (Binary.lengthInput a) W) := by
  let L := Binary.lengthInput a
  let state := (InitializationWork.run a valid.1).value
  let good := InitializationWork.run_correct a valid
  let B := Binary.gridBitBound L
  let H := Binary.witnesses L
  have gridFit : state.prepared.scales.grid.size ≤ B := good.grid ▸ Binary.grid_size a valid
  have witnessFit : state.prepared.witness.size ≤ H := good.witness ▸
    (size_le_self (witnessBound a.game)).trans (Binary.witness_bound a)
  have clock := (PlanWork.clock_work a state.prepared gridFit witnessFit).weaken le_rfl
    (show PlanWork.clockWidth B H ≤ leadWidth L W by unfold leadWidth B H; omega)
  have trial (s) (hs : ValidSelection (CoreWork.prepared a valid.1).quantiles
      (CoreWork.prepared a valid.1).quotes s) :=
    (InventorySearch.trial_work a valid normal state good (contact state good)
      (agree state good) s hs (charge state good s hs)).weaken le_rfl
      (show InventorySearch.trialWidth L W ≤ leadWidth L W by unfold leadWidth; omega)
  have emit (s : Strategy a.types a.targets) (_ : a.game.IsBayesNash s.coverage s.attacks) :=
    (InventorySearch.emit_work s (Binary.dimensions a).2.1 (Binary.dimensions a).1).weaken
      le_rfl (show 2*L ≤ leadWidth L W by unfold leadWidth; omega)
  have core := CoreWork.interior_work a valid normal (PlanWork.clock a state.prepared)
    (fun _ => InventorySearch.trial a valid.1 state good (contact state good)) InventorySearch.emit
    (PlanWork.clock_value a valid.1 state.prepared good.grid good.witness good.counts)
    (InventorySearch.trial_value a valid.1 state good (contact state good) (agree state good))
    clock trial emit
  have init := InitializationWork.run_work a valid
  have initFit : InitializationWork.width L ≤ width L W := by unfold width; omega
  have mainFit : searchWidth L+leadWidth L W ≤ width L W := by unfold width; omega
  exact ⟨Nat.add_le_add init.1 core.1,
    max_le (init.2.trans initFit) (core.2.trans mainFit)⟩

/-- The direct cases share the same charged dispatcher as the public solver. -/
def run (a : Input) (valid : a.Valid) (contact : Provider a valid.1) : Run Output :=
  DirectWork.dispatch (fun _ => interior a valid contact) a

theorem run_value (a : Input) (valid : a.Valid) (contact : Provider a valid.1)
    (agree : Provider.Agrees a valid.1 contact) : (run a valid contact).value = solve a := by
  by_cases direct : a.game.DirectCase
  · exact DirectWork.dispatch_direct _ a valid direct
  · exact (DirectWork.dispatch_interior _ a direct).trans (interior_value a valid direct contact agree)

def runSlots (L C : ℕ) := DirectWork.directSlots L + (DirectWork.planSlots L+1+slots L C)
def runWidth (L W : ℕ) := DirectWork.width L + width L W

theorem run_work (a : Input) (valid : a.Valid) (contact : Provider a valid.1)
    (agree : Provider.Agrees a valid.1 contact) {C W : ℕ}
    (charge : Provider.Bound a valid.1 contact C W) :
    (run a valid contact).Bound (runSlots (Binary.lengthInput a) C) (runWidth (Binary.lengthInput a) W) := by
  by_cases direct : a.game.DirectCase
  · exact (DirectWork.dispatch_direct_work (fun _ => interior a valid contact) a valid direct).weaken
      (Nat.le_add_right ..) (Nat.le_add_right ..)
  · exact (DirectWork.dispatch_interior_work (fun _ => interior a valid contact) a valid direct
      (interior_work a valid direct contact agree charge)).weaken
      (Nat.le_add_left ..) (max_le (Nat.le_add_right ..) (Nat.le_add_left ..))

end Kintali.InputOutput.CheckedSearch
