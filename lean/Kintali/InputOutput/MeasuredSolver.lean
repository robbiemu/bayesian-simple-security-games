module

public import Kintali.InputOutput.CheckedPolynomial
public import Kintali.QuotaSweep.SelectedBuilder
import all Kintali.ContactSize.Polynomial

/-! # Executable public solver with a concrete measured sparse contact -/

@[expose] public section

namespace Kintali.InputOutput.MeasuredSolver

open StochasticGames.CompilerRun
open ContactSize Polynomial QuotaSweep QuoteSearch MarketTrial
open CheckedSearch

def contact : ContactFamily :=
  fun _ _ st correct _ lists => SelectedBuilder.fromLists lists st correct

theorem agrees (a : Input) (valid : a.Valid) : Provider.Agrees a valid.1 (contact a valid) :=
  fun st good _ lists => SelectedBuilder.fromLists_value lists st good

def run (xs : CodecWork.Stream) : Run CodecWork.Stream := bits contact xs

theorem exact_output (xs : CodecWork.Stream) (a : Input)
    (read : Binary.inputCodec.decode xs = some a) (valid : a.Valid) :
    (run xs).value = solveBits xs ∧
    Binary.outputCodec.decode (run xs).value = some (solve a) ∧ a.IsBayesNash (solve a) :=
  bits_exact contact agrees xs a read valid

theorem contact_work (a : Input) (valid : a.Valid) :
    let L := Binary.lengthInput a
    Provider.Bound a valid.1 (contact a valid) (SelectedBuilder.slots L) (SelectedBuilder.width L) := by
  dsimp only
  intro st good s hs lists
  have short : SelectionBound a s := by
    intro i
    have count := (hs.count i).trans (Nat.sub_le _ _)
    have limit := Nat.mul_le_mul_left 4 (Binary.witness_bound a)
    unfold sampleLimit Binary.witnesses at *
    omega
  exact SelectedBuilder.fromLists_work lists valid short st good

def contactWidth (L : ℕ) := SelectedBuilder.builderWidth L + ContactCharge.width L

local macro "build_polynomial" : tactic =>
  `(tactic| with_reducible (repeat' first | assumption | exact variable_eval | apply constant_eval | apply add_eval | apply mul_eval | apply pow_eval))

private theorem builder_slot_polynomial : Evaluation SelectedBuilder.slots := by
  have r := records_poly
  have g := grid_poly
  have q := scale_poly
  have c : Evaluation ContactCharge.slots := TrialWork.Selected.contact_slots_polynomial
  unfold SelectedBuilder.slots SelectedBuilder.builderSlots SelectedBuilder.columnSlots
    SelectedBuilder.orderSlots SelectedBuilder.inventorySize TrialWork.Selected.Lists.labelsSlots
    SelectedBuilder.quotaSlots SelectedBuilder.massSlots SelectedBuilder.quotaBits SelectedBuilder.indexWidth
    RankRun.contactSlots RankRun.inputSlots RankRun.slots RankRun.rowSlots
    RankRun.keySlots RankRun.quoteSlots TrialWork.costSlots TrialWork.scalarSlots
  build_polynomial

private theorem contact_width_polynomial : Evaluation contactWidth := by
  have r := records_poly
  have g := grid_poly
  have q := scale_poly
  have c : Evaluation ContactCharge.width := TrialWork.Selected.contact_width_polynomial
  unfold contactWidth SelectedBuilder.builderWidth SelectedBuilder.quotaBits SelectedBuilder.orderWidth
    SelectedBuilder.indexWidth TrialWork.Selected.Lists.labelsWidth StoredLookup.width TrialWork.scalarWidth
  build_polynomial

/-- The concrete program's addressed slot-and-width accounting is bounded by
one polynomial on every input stream. The cost model and the target machine
semantics are separate interfaces. -/
theorem binary_work_polynomial : ∃ P : Polynomial ℕ, ∀ xs : CodecWork.Stream,
    LinearProgramming.RecoveryRun.binaryWork xs.length (run xs).work ≤ P.eval xs.length := by
  obtain ⟨C, c⟩ := builder_slot_polynomial
  obtain ⟨W, w⟩ := contact_width_polynomial
  apply bits_polynomial contact agrees C W
  intro a valid st good s hs lists
  rw [c,w]
  exact (contact_work a valid st good s hs lists).weaken le_rfl
    (max_le (Nat.le_add_right ..) (Nat.le_add_left ..))

end Kintali.InputOutput.MeasuredSolver
