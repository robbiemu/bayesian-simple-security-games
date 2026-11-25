module

public import Kintali.InputOutput.CheckedSearch
public import Kintali.InputOutput.PublicWork
import all Kintali.ContactSize.Polynomial

/-! # Public composition with a charged sparse contact -/

@[expose] public section

namespace Kintali.InputOutput.CheckedSearch

open ContactSize Polynomial
open QuoteSearch TrialWork

local macro "build_polynomial" : tactic =>
  `(tactic| with_reducible (repeat' first | assumption | exact variable_eval | apply constant_eval | apply add_eval | apply mul_eval | apply pow_eval))

private theorem inventory_input_width : Evaluation Inventory.inputWidth := by
  have g := grid_poly
  unfold Inventory.inputWidth OutsideWork.priceWidth
  build_polynomial

private theorem inventory_slots : Evaluation Inventory.slots := by
  have w := inventory_input_width
  unfold Inventory.slots Inventory.realSlots Inventory.maxChoices Inventory.allPairSlots
    Inventory.pairSlots Inventory.testSlots costSlots scalarSlots Binary.witnesses
  build_polynomial

private theorem inventory_width : Evaluation Inventory.width := by
  have w := inventory_input_width
  unfold Inventory.width Inventory.testWidth scalarWidth
  build_polynomial

theorem run_slots_polynomial (C : Polynomial ℕ) :
    ∃ P : Polynomial ℕ, ∀ L, P.eval L = runSlots L (C.eval L) := by
  change Evaluation (fun L => runSlots L (C.eval L))
  have c : Evaluation C.eval := ⟨C,fun _ => rfl⟩
  have t : Evaluation Selected.afterSlots := Selected.after_slots_polynomial
  have i := inventory_slots
  have g := grid_poly
  have s : Evaluation InitializationWork.slots := InitializationWork.slots_polynomial
  unfold runSlots slots CoreWork.interiorSlots searchSlots PlanWork.clockSlots InventorySearch.trialSlots
    InventorySearch.emitSlots StrategyWork.slots DirectWork.directSlots DirectWork.strategySlots
    DirectWork.rowSlots DirectWork.planSlots Binary.trialLimit Binary.witnesses DriverWork.selectLimit
    DriverWork.updateLimit Runs.selectionSlots
  build_polynomial

theorem run_width_polynomial (W : Polynomial ℕ) :
    ∃ P : Polynomial ℕ, ∀ L, P.eval L = runWidth L (W.eval L) := by
  change Evaluation (fun L => runWidth L (W.eval L))
  have w : Evaluation W.eval := ⟨W,fun _ => rfl⟩
  have t : Evaluation Selected.afterWidth := Selected.after_width_polynomial
  have i := inventory_width
  have g := grid_poly
  have s : Evaluation InitializationWork.width := InitializationWork.width_polynomial
  unfold runWidth width leadWidth searchWidth PlanWork.clockWidth InventorySearch.trialWidth
    DirectWork.width Binary.trialLimit Binary.witnesses
  build_polynomial

abbrev ContactFamily := (a : Input) → (v : a.Valid) → Provider a v.1

def bits (c : ContactFamily) (xs : CodecWork.Stream) :
    StochasticGames.CompilerRun.Run CodecWork.Stream :=
  PublicWork.run (fun a v => run a v (c a v)) xs

theorem bits_exact (c : ContactFamily) (agree : ∀ a v, Provider.Agrees a v.1 (c a v))
    (xs : CodecWork.Stream) (a : Input) (read : Binary.inputCodec.decode xs = some a) (v : a.Valid) :
    (bits c xs).value = solveBits xs ∧
    Binary.outputCodec.decode (bits c xs).value = some (solve a) ∧
    a.IsBayesNash (solve a) :=
  PublicWork.decoded_output _ (fun b bValid => run_value b bValid (c b bValid) (agree b bValid)) xs a read v

/-- The one remaining word-cost interface is the contact evaluator on a
stored inventory. The clock, enclosing search, and code at both binary
boundaries contribute to the bound. -/
theorem bits_polynomial (c : ContactFamily) (agree : ∀ a v, Provider.Agrees a v.1 (c a v))
    (C W : Polynomial ℕ) (cost : ∀ a v, Provider.Bound a v.1 (c a v)
      (C.eval (Binary.lengthInput a)) (W.eval (Binary.lengthInput a))) :
    ∃ P : Polynomial ℕ, ∀ xs : CodecWork.Stream,
      LinearProgramming.RecoveryRun.binaryWork xs.length (bits c xs).work ≤ P.eval xs.length := by
  obtain ⟨K,k⟩ := run_slots_polynomial C
  obtain ⟨V,v⟩ := run_width_polynomial W
  apply PublicWork.stream_polynomial _ (fun a h => run_value a h (c a h) (agree a h)) K V
  intro a h
  rw [k,v]
  exact run_work a h (c a h) (agree a h) (cost a h)

end Kintali.InputOutput.CheckedSearch
