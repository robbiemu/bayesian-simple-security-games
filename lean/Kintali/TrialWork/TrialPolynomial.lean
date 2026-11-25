module

public import Kintali.TrialWork.SelectedExecute
public import Kintali.TrialWork.SelectedPolynomial
import all Kintali.ContactSize.Polynomial

/-! Polynomial addressed work of a fully executed trial supplied with
its sorted retained inventory. The contact uses its measured scalar
tariff and the trial runs the selected recovery or blocker branch. -/

@[expose] public section
namespace Kintali.TrialWork.Selected

open Polynomial ContactSize InputOutput ExactRecovery LinearProgramming QuotaSweep

local macro "build_poly" : tactic =>
  `(tactic| with_reducible (repeat' first | assumption | exact variable_eval | apply constant_eval | apply add_eval | apply mul_eval | apply pow_eval))

private theorem operand_poly : Evaluation ContactCharge.operandWidth := by
  have r := records_poly
  have g := grid_poly
  have f := parameters_poly
  have a : Evaluation allocationWidth := allocation_polynomial
  have u : Evaluation OperandBounds.inputWidth := by unfold OperandBounds.inputWidth; build_poly
  have b : Evaluation (fun n => OperandBounds.advanceWidth (recordLimit n) (OperandBounds.inputWidth n)) := by
    unfold OperandBounds.advanceWidth OperandBounds.eventWidth OperandBounds.budgetWidth OperandBounds.changeWidth
      OperandBounds.rateWidth OperandBounds.sumWidth
    build_poly
  unfold ContactCharge.operandWidth OperandBounds.inputStageWidth OperandBounds.stageWidth OperandBounds.sumWidth
  build_poly

theorem contact_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = ContactCharge.slots L := by
  change Evaluation ContactCharge.slots
  have u := operand_poly
  have r := records_poly
  unfold ContactCharge.slots OperandBounds.inputSlots ContactCharge.unitSlots scalarSlots
  build_poly

theorem contact_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = ContactCharge.width L := by
  change Evaluation ContactCharge.width
  have u := operand_poly
  unfold ContactCharge.width scalarWidth
  build_poly

private theorem repair_width_poly : Evaluation repairWidth := by
  have w : Evaluation inputWidth := input_width_polynomial
  have r : Evaluation repairLength := repair_length_polynomial
  have u := dimensions_poly
  unfold repairWidth indexWidth exactRows exactVars RationalInput.widthLimit RecoveryRun.operandLimit
    PivotRun.width RecoveryRun.scale PointEncoding.wordLimit
  build_poly

private theorem repair_slots_poly : Evaluation repairSlots := by
  have w := repair_width_poly
  have r : Evaluation repairLength := repair_length_polynomial
  unfold repairSlots RepairWork.solveSlots RowWork.denseSlots RowWork.rowSlots OutputWork.strategySlots
    OutputWork.attackRowSlots OutputWork.attackSlots OutputWork.fractionSlots scalarSlots exactRows exactVars
    RationalInput.slotLimit RecoveryRun.transitionLimit RecoveryRun.scale PointEncoding.wordLimit
  build_poly

theorem trial_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = trialSlots L := by
  change Evaluation trialSlots
  have c : Evaluation ContactCharge.slots := contact_slots_polynomial
  have v : Evaluation projectSlots := project_slots_polynomial
  have p : Evaluation (fun L => patternSlots L L 2 (inputWidth L)) := pattern_slots_polynomial
  have f : Evaluation (fun L => relaxSlots L L L 2 2 (inputWidth L)) := relaxed_slots_polynomial
  have r := repair_slots_poly
  have b : Evaluation blockedSlots := blocked_slots_polynomial
  unfold trialSlots executeSlots
  build_poly

theorem trial_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = trialWidth L := by
  change Evaluation trialWidth
  have c : Evaluation ContactCharge.width := contact_width_polynomial
  have v : Evaluation projectWidth := project_width_polynomial
  have p : Evaluation (fun L => patternWidth (inputWidth L)) := pattern_width_polynomial
  have f : Evaluation (fun L => relaxWidth L L L (inputWidth L)) := relaxed_width_polynomial
  have r := repair_width_poly
  have b : Evaluation blockedWidth := blocked_width_polynomial
  unfold trialWidth executeWidth scalarWidth
  build_poly

theorem after_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = afterSlots L := by
  change Evaluation afterSlots
  have v : Evaluation projectSlots := project_slots_polynomial
  have p : Evaluation (fun L => patternSlots L L 2 (inputWidth L)) := pattern_slots_polynomial
  have f : Evaluation (fun L => relaxSlots L L L 2 2 (inputWidth L)) := relaxed_slots_polynomial
  have r := repair_slots_poly
  have b : Evaluation blockedSlots := blocked_slots_polynomial
  unfold afterSlots executeSlots
  build_poly

theorem after_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = afterWidth L := by
  change Evaluation afterWidth
  have v : Evaluation projectWidth := project_width_polynomial
  have p : Evaluation (fun L => patternWidth (inputWidth L)) := pattern_width_polynomial
  have f : Evaluation (fun L => relaxWidth L L L (inputWidth L)) := relaxed_width_polynomial
  have r := repair_width_poly
  have b : Evaluation blockedWidth := blocked_width_polynomial
  unfold afterWidth executeWidth scalarWidth
  build_poly

theorem trial_binary_polynomial : ∃ p : Polynomial ℕ, ∀ (a : Input) (valid : a.Valid)
    (_ : ¬a.game.DirectCase) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a valid.1 st) (s : QuoteSearch.Selection (a.types*a.targets))
    (_ : SelectionBound a s) (l : Lists a (route st) s),
    RecoveryRun.binaryWork (Binary.lengthInput a) (trial a valid.1 st correct s l).work ≤ p.eval (Binary.lengthInput a) := by
  have s : Evaluation trialSlots := trial_slots_polynomial
  have w : Evaluation trialWidth := trial_width_polynomial
  have bounds : Evaluation (fun n => CodecWork.binaryLimit n (trialSlots n) (trialWidth n)) := by
    unfold CodecWork.binaryLimit
    build_poly
  obtain ⟨p,h⟩ := bounds
  exact ⟨p,fun a valid normal st correct q sel l =>
    (CodecWork.addressed_bound _ (trial_work a valid normal st correct q sel l)).trans_eq (h _).symm⟩

end Kintali.TrialWork.Selected
