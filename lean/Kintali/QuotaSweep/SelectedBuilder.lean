module

public import Kintali.QuotaSweep.BuilderEntry
public import Kintali.QuotaSweep.BuilderQuotaWork

/-! # Selected quota-sweep entry point from the search trial's prepared lists -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)} {hm : 0 < a.targets}

def builderSlots (L : ℕ) := columnSlots L+orderSlots L+(2+recordLimit L*7+1)+quotaSlots L+1

theorem assemble_work (l : Lists a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (st : InitializationWork.State a.types a.targets) (correct : InitializationWork.Correct a valid.1 st) :
    let L := Binary.lengthInput a
    (assemble l st correct).Bound (builderSlots L) (builderWidth L) := by
  let L := Binary.lengthInput a
  let c := columns l st
  let os := makeOrders l st
  let ho := orders_valid l st
  let book := createBook l st.tables.fields st.prepared.scales.grid correct.grid c.value (columns_correct l st) os.value ho
  let quotas := quotaData l st os.value ho
  have shape := indexes_fit L
  have cols := (columns_work l valid hs st).weaken le_rfl shape.1
  have order := (orders_work l hs st).weaken le_rfl shape.2.1
  have width : TrialWork.scalarWidth (2*Binary.lengthInput a+1) ≤ builderWidth L := by
    apply Nat.le_trans _ shape.2.2
    unfold TrialWork.scalarWidth quotaBits
    dsimp only [L]; omega
  have mask := admitted_work st.tables.fields os.value ho correct.fields width
  have few := (order_counts os.value ho hs).2.2
  have bc : book.Bound (2+recordLimit L*7+1) (builderWidth L) :=
    ⟨Nat.add_le_add_right (mask.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ few) _)) 1,
      max_le mask.2 (Nat.zero_le _)⟩
  have q := quotaData_work l valid hs st correct os.value ho
  change c.work.slots+(os.work.slots+(book.work.slots+(quotas.work.slots+1))) ≤ builderSlots L ∧
    max c.work.width (max os.work.width (max book.work.width (max quotas.work.width 0))) ≤ builderWidth L
  exact ⟨(Nat.add_le_add cols.1 (Nat.add_le_add order.1 (Nat.add_le_add bc.1 (Nat.add_le_add_right q.1 1)))).trans
    (by unfold builderSlots; dsimp only [L]; omega),max_le cols.2 (max_le order.2 (max_le bc.2 (max_le q.2 (Nat.zero_le _))))⟩

def slots (L : ℕ) := builderSlots L+RankRun.contactSlots L (RankRun.keySlots L)
def width (L : ℕ) := max (builderWidth L) (ContactCharge.width L)

theorem fromLists_work (l : Lists a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (st : InitializationWork.State a.types a.targets) (correct : InitializationWork.Correct a valid.1 st) :
    let L := Binary.lengthInput a
    (fromLists l st correct).Bound (slots L) (width L) :=
  RankRun.fromBuilder_work valid hs _ (assemble_work l valid hs st correct)

end Kintali.QuotaSweep.SelectedBuilder
