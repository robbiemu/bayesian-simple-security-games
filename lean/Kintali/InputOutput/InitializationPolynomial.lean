module

public import Kintali.InputOutput.InitializationWork
public import Kintali.InputOutput.DirectWork
public import Kintali.ContactSize.Polynomial
import all Kintali.ContactSize.Polynomial

/-! # Fixed natural polynomials for public initialization and the direct program -/

@[expose] public section
namespace Kintali.InputOutput

open ContactSize Polynomial

local macro "build_polynomial" : tactic =>
  `(tactic| with_reducible (repeat' first | assumption | exact variable_eval | apply constant_eval | apply add_eval | apply mul_eval | apply pow_eval))

private theorem normalized_poly : Evaluation NormalizedWork.tableSlots := by
  unfold NormalizedWork.tableSlots NormalizedWork.tabSlots NormalizedWork.fieldSlots TrialWork.scalarSlots
  build_polynomial

private theorem distinct_slots : Evaluation DatumWork.scaleSlots := by
  unfold DatumWork.scaleSlots DatumWork.enumSlots DatumWork.rowSlots DatumWork.listBound
  build_polynomial

private theorem distinct_width : Evaluation DatumWork.scaleWidth := by
  unfold DatumWork.scaleWidth TrialWork.scalarWidth DatumWork.listBound
  build_polynomial

private theorem tolerance_slots : Evaluation ToleranceWork.setupSlots := by
  have ds := distinct_slots
  have t := tolerance_poly
  have u := dimensions_poly
  unfold ToleranceWork.setupSlots ToleranceWork.scalarSlots ToleranceWork.operandWidth
  build_polynomial

private theorem tolerance_width : Evaluation ToleranceWork.setupWidth := by
  have dw := distinct_width
  have t := tolerance_poly
  have u := dimensions_poly
  unfold ToleranceWork.setupWidth ToleranceWork.operandWidth
  build_polynomial

private theorem eligibility_width : Evaluation PrepareWork.eligibilityWidth := by
  have g := grid_poly
  unfold PrepareWork.eligibilityWidth PrepareWork.fieldWidth OutsideWork.priceWidth
  build_polynomial

private theorem prepare_slots : Evaluation PrepareWork.setupSlots := by
  have t := tolerance_poly
  have e := eligibility_width
  unfold PrepareWork.setupSlots PrepareWork.scaleWidth PrepareWork.fieldWidth PrepareWork.witnessSlots
    ScalesWork.workSlots MaximaWork.overSlots OutsideWork.directorySlots OutsideWork.bestSlots
    OutsideWork.endpointSlots TrialWork.costSlots EligibilityWork.countSlots TrialWork.scalarSlots
  build_polynomial

private theorem prepare_width : Evaluation PrepareWork.setupWidth := by
  have t := tolerance_poly
  have e := eligibility_width
  unfold PrepareWork.setupWidth PrepareWork.scaleWidth PrepareWork.fieldWidth
    ScalesWork.workWidth OutsideWork.comparisonWidth OutsideWork.priceWidth PrepareWork.witnessWidth
    EligibilityWork.countWidth TrialWork.scalarWidth
  build_polynomial

theorem InitializationWork.slots_polynomial : ∃ p : Polynomial ℕ, ∀ S, p.eval S = InitializationWork.slots S := by
  change Evaluation InitializationWork.slots
  have n := normalized_poly
  have d := tolerance_slots
  have p := prepare_slots
  unfold InitializationWork.slots
  build_polynomial

theorem InitializationWork.width_polynomial : ∃ p : Polynomial ℕ, ∀ S, p.eval S = InitializationWork.width S := by
  change Evaluation InitializationWork.width
  have t := tolerance_width
  have p := prepare_width
  unfold InitializationWork.width TrialWork.scalarWidth
  build_polynomial

theorem InitializationWork.polynomial : ∃ p : Polynomial ℕ, ∀ (a : Input) (v : a.Valid),
    LinearProgramming.RecoveryRun.binaryWork (Binary.lengthInput a) (InitializationWork.run a v.1).work ≤
      p.eval (Binary.lengthInput a) := by
  have s : Evaluation InitializationWork.slots := InitializationWork.slots_polynomial
  have w : Evaluation InitializationWork.width := InitializationWork.width_polynomial
  have e : Evaluation (fun S => CodecWork.binaryLimit S (InitializationWork.slots S) (InitializationWork.width S)) := by
    unfold CodecWork.binaryLimit
    build_polynomial
  obtain ⟨p,h⟩ := e
  exact ⟨p,fun a v => (InitializationWork.run_binary_work a v).trans_eq (h _).symm⟩

theorem DirectWork.polynomial : ∃ p : Polynomial ℕ, ∀ (a : Input) (_ : a.Valid) (_ : a.game.DirectCase)
    (interior : Input → StochasticGames.CompilerRun.Run Output),
    LinearProgramming.RecoveryRun.binaryWork (Binary.lengthInput a)
      (CodecWork.solveRun (DirectWork.dispatch interior) (Binary.input a)).work ≤ p.eval (Binary.lengthInput a) := by
  have input : Evaluation CodecWork.inputLimit := by
    change ∃ p : Polynomial ℕ, _
    simp_rw [CodecWork.inputLimit_eq]
    change Evaluation (fun S => 22*S^3+110*S^2+125*S+16)
    build_polynomial
  have e : Evaluation (fun S => CodecWork.binaryLimit S
      (CodecWork.solveSlots S (DirectWork.directSlots S) (DirectWork.directLength S))
      (CodecWork.solveWidth S (DirectWork.width S) (DirectWork.directLength S))) := by
    unfold CodecWork.binaryLimit CodecWork.solveSlots CodecWork.solveWidth DirectWork.directSlots
      DirectWork.directLength DirectWork.strategySlots DirectWork.rowSlots DirectWork.planSlots DirectWork.width
    build_polynomial
  obtain ⟨p,h⟩ := e
  exact ⟨p,fun a v d interior => (DirectWork.bits_correct interior a v d).2.2.2.trans_eq (h _).symm⟩

end Kintali.InputOutput
