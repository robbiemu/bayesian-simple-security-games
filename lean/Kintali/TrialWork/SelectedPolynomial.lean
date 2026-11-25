module

public import Kintali.TrialWork.SelectedChecks
public import Kintali.ContactSize.Polynomial
import all Kintali.ContactSize.Polynomial

/-! Fixed natural-coefficient polynomials for the sparse contact projection,
both endpoint searches, and the prepared pattern and relaxed feasibility scan. -/

@[expose] public section
namespace Kintali.TrialWork.Selected

open ContactSize Polynomial QuotaSweep InputOutput ExactRecovery

local macro "build_poly" : tactic =>
  `(tactic| with_reducible (repeat' first | assumption | exact variable_eval | apply constant_eval | apply add_eval | apply mul_eval | apply pow_eval))

theorem input_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = inputWidth L := by
  change Evaluation inputWidth
  have a : Evaluation allocationWidth := allocation_polynomial
  have v : Evaluation viewWidth := view_polynomial
  have r := records_poly
  have s := scale_poly
  have t := tolerance_poly
  have g := grid_poly
  unfold inputWidth sizeLimit StoredLookup.width fieldsWidth scalarWidth
  build_poly

private theorem labels_slots_poly : Evaluation Lists.labelsSlots := by
  have r := records_poly
  unfold Lists.labelsSlots
  build_poly

private theorem labels_width_poly : Evaluation Lists.labelsWidth := by
  have r := records_poly
  unfold Lists.labelsWidth
  build_poly

private theorem size_limit_poly : Evaluation sizeLimit := by
  have r := records_poly
  unfold sizeLimit
  build_poly

private theorem access_slots_poly : Evaluation accessSlots := by
  have r := records_poly
  unfold accessSlots StoredLookup.slots
  build_poly

theorem project_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = projectSlots L := by
  change Evaluation projectSlots
  have n := size_limit_poly
  have w : Evaluation inputWidth := input_width_polynomial
  have c := access_slots_poly
  have h := labels_slots_poly
  unfold projectSlots Access.projectionSlots Access.rowSlots Access.cellSlots Access.entrySlots
    sumSlots scalarSlots addWidth sumBits
  build_poly

theorem project_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = projectWidth L := by
  change Evaluation projectWidth
  have n := size_limit_poly
  have w : Evaluation inputWidth := input_width_polynomial
  have h := labels_width_poly
  unfold projectWidth Access.projectionWidth scalarWidth addWidth sumBits
  build_poly

theorem predicate_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = predicateSlots L := by
  change Evaluation predicateSlots
  have n := size_limit_poly
  have w : Evaluation inputWidth := input_width_polynomial
  have c := access_slots_poly
  unfold predicateSlots Access.blockSlots Access.blockRowSlots betterSlots quoteSlots costSlots scalarSlots
  build_poly

theorem blocked_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = blockedWidth L := by
  change Evaluation blockedWidth
  have w : Evaluation inputWidth := input_width_polynomial
  have g := grid_poly
  unfold blockedWidth blockWidth scalarWidth
  build_poly

theorem blocked_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = blockedSlots L := by
  change Evaluation blockedSlots
  have w : Evaluation blockedWidth := blocked_width_polynomial
  have c : Evaluation predicateSlots := predicate_slots_polynomial
  unfold blockedSlots intervalsSlots intervalSlots
  build_poly

theorem pattern_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = patternSlots L L 2 (inputWidth L) := by
  change Evaluation (fun L => patternSlots L L 2 (inputWidth L))
  have w : Evaluation inputWidth := input_width_polynomial
  unfold patternSlots tableSlots referenceSlots markSlots costSlots scalarSlots
  build_poly

theorem pattern_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = patternWidth (inputWidth L) := by
  change Evaluation (fun L => patternWidth (inputWidth L))
  have w : Evaluation inputWidth := input_width_polynomial
  unfold patternWidth scalarWidth
  build_poly

theorem relaxed_slots_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = relaxSlots L L L 2 2 (inputWidth L) := by
  change Evaluation (fun L => relaxSlots L L L 2 2 (inputWidth L))
  have w : Evaluation inputWidth := input_width_polynomial
  unfold relaxSlots rowSlots termSlots atomSlots atomBits costSlots sumSlots scalarSlots addWidth sumBits exactRows
  build_poly

theorem relaxed_width_polynomial : ∃ p : Polynomial ℕ, ∀ L, p.eval L = relaxWidth L L L (inputWidth L) := by
  change Evaluation (fun L => relaxWidth L L L (inputWidth L))
  have w : Evaluation inputWidth := input_width_polynomial
  unfold relaxWidth indexWidth exactRows checkWidth termBits atomBits sumBits scalarWidth
  build_poly

end Kintali.TrialWork.Selected
