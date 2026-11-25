module

public import Kintali.QuotaSweep.SelectedWork
public import Kintali.QuotaSweep.PreparationWork
public import Kintali.TrialWork.Arithmetic
public import Kintali.InputOutput.CodecWork

/-!
# Composing the measured sparse contact with an addressed-word caller

`prepared` accepts the stored book, quotas and finite indices as inputs.
It translates the exact scan/scalar counter of the selected execution into
a `CompilerRun.Run` with a uniform number of addressed slots reserved per
charged unit. `selected` exposes the same boundary for a public trial.
Ordinary arithmetic operations of the indicated width have executable
addressed implementations in `TrialWork.Arithmetic` satisfying the tariff.

The counter includes allocation and graph table scans, bounded successor
walks, proposals, rates, endpoint calculations and the budget branch. A
caller supplying the sparse inventory separately charges the formation of
retained Finsets, finite index enumerations and their sorts, column tables,
and preparation of the game's numeric parameters. `Sparse.key_preparation`
counts the ordinal key evaluations and comparisons after enumeration.
The uniform charge is a cost adapter for the measured computation. A
primitive instruction trace or certification of emitted Lean code requires
an execution-semantics refinement independently of this adapter.
-/

@[expose] public section
namespace Kintali.QuotaSweep.ContactCharge

open StochasticGames.CompilerRun
open Kintali.ExactRecovery Kintali.ContactSize Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch

/-- The division tariff includes reciprocation, multiplication and reduction. -/
def unitSlots (w : ℕ) := 4 + TrialWork.scalarSlots w

def operandWidth (L : ℕ) :=
  OperandBounds.inputStageWidth L + 4*(Binary.gridBitBound L + L + recordLimit L)+16

def slots (L : ℕ) := OperandBounds.inputSlots L * unitSlots (operandWidth L)

def width (L : ℕ) := TrialWork.scalarWidth (operandWidth L)

/-- Charge exactly the supplied index/scalar count. This operation attaches
the same tariff to every charged unit, regardless of whether its implementation
uses arithmetic, a list traversal or an index comparison. -/
def price {T : Type*} (w : ℕ) (a : T × ℕ) : Run T :=
  ⟨a.1,⟨a.2*unitSlots w,TrialWork.scalarWidth w⟩⟩

@[simp] theorem price_value {T : Type*} (w : ℕ) (a : T × ℕ) : (price w a).value = a.1 := rfl

theorem price_work {T : Type*} (w : ℕ) (a : T × ℕ) {n : ℕ} (h : a.2 ≤ n) :
    (price w a).Bound (n*unitSlots w) (TrialWork.scalarWidth w) :=
  ⟨Nat.mul_le_mul_right _ h,le_rfl⟩

/-- Actual arithmetic programs for the largest scalar operations charged
by a graph unit, including normalized rational division. -/
theorem arithmetic_tariff {q r : ℚ} {w : ℕ} (hq : Fits w q) (hr : Fits w r) :
    (TrialWork.plus q r).Bound (unitSlots w) (TrialWork.scalarWidth w) ∧
    (TrialWork.times q r).Bound (unitSlots w) (TrialWork.scalarWidth w) ∧
    (TrialWork.divide q r).Bound (unitSlots w) (TrialWork.scalarWidth w) ∧
    (TrialWork.le q r).Bound (unitSlots w) (TrialWork.scalarWidth w) ∧
    (TrialWork.lt q r).Bound (unitSlots w) (TrialWork.scalarWidth w) := by
  exact ⟨(TrialWork.plus_work hq hr).weaken (Nat.le_add_left ..) le_rfl,
    (TrialWork.times_work hq hr).weaken (Nat.le_add_left ..) le_rfl,TrialWork.divide_work hq hr,
    (TrialWork.le_work hq hr).weaken (by unfold unitSlots TrialWork.scalarSlots; omega) le_rfl,
    (TrialWork.lt_work hq hr).weaken (by unfold unitSlots; omega) le_rfl⟩

section Prepared

variable {B S E : Type} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] [Encodable B] [Encodable S] [Encodable E]

/-- The book has already received its finite record, retained and rank tables.
The lookup, rate, mass and outside-set callbacks use the supplied inventory. -/
def prepared (K : Book B S E) (P : Parameters B S) (w : ℕ) : Run (Book.Stored B S E) :=
  price w (K.indexedContact Book.encodedEq Book.encodedEq Book.encodedEq P (8*(K.records.length+1)))

theorem prepared_value (K : Book B S E) (P : Parameters B S) (w : ℕ) :
    (prepared K P w).value = (K.contactWork P (8*(K.records.length+1))).1 := by
  simp [prepared,Book.indexedContact_eq]

theorem prepared_work (K : Book B S E) (P : Parameters B S) (w : ℕ) :
    (prepared K P w).Bound (300*(K.records.length+2)^5*unitSlots w) (TrialWork.scalarWidth w) := by
  unfold prepared
  apply price_work
  rw [Book.indexedContact_eq]
  exact K.contactWork_polynomial P

/-- Bind any charged preparation of this book and quota vector to the
contact. The preparation's actual slots and width remain visible to the caller. -/
theorem bind_inventory (inventory : Run (Book B S E × Parameters B S)) {k w w₀ r : ℕ}
    (hp : inventory.Bound k w₀) (hr : inventory.value.1.records.length ≤ r) :
    (inventory >>= fun x => prepared x.1 x.2 w).Bound (k+300*(r+2)^5*unitSlots w)
      (max w₀ (TrialWork.scalarWidth w)) := by
  have hc := prepared_work inventory.value.1 inventory.value.2 w
  change inventory.work.slots+(prepared _ _ w).work.slots ≤ _ ∧
    max inventory.work.width (prepared _ _ w).work.width ≤ _
  exact ⟨Nat.add_le_add hp.1 (hc.1.trans (by gcongr)),max_le_max hp.2 hc.2⟩

end Prepared

/-- Composable scalar-charge boundary for the contact selected by the normal
public search. The result retains its stored allocation table for projection. -/
def selected (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) :=
  price (operandWidth (Binary.lengthInput a))
    (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game))

theorem selected_value (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) :
    (selected a toSite s).value =
      (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).1 := rfl

theorem selected_charge (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) :
    (selected a toSite s).work.slots = (Sparse.selectedRun (G := grid a.game) a.game toSite s
      (privateScale a.game)).2*unitSlots (operandWidth (Binary.lengthInput a)) := rfl

theorem selected_work (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) :
    (selected a toSite s).Bound (slots (Binary.lengthInput a)) (width (Binary.lengthInput a)) :=
  price_work _ _ (OperandBounds.selected_slots a toSite s hs)

theorem selected_binary (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) :
    let L := Binary.lengthInput a
    LinearProgramming.RecoveryRun.binaryWork L (selected a toSite s).work ≤
      CodecWork.binaryLimit L (slots L) (width L) :=
  CodecWork.addressed_bound _ (selected_work a toSite s hs)

end Kintali.QuotaSweep.ContactCharge
