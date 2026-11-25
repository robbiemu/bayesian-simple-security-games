module

public import Kintali.QuotaSweep.BuilderParameters

/-! # Selected quota-sweep entry point from the search trial's prepared lists -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)} {hm : 0 < a.targets}

def assemble (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) : Run (RankRun.Inventory a toSite s) :=
  let c := columns l st
  let os := makeOrders l st
  let valid := orders_valid l st
  let book := createBook l st.tables.fields st.prepared.scales.grid correct.grid c.value (columns_correct l st) os.value valid
  let computed := createBook_value l st.tables.fields correct.game st.prepared.scales.grid correct.grid c.value (columns_correct l st) os.value valid
  let quotas := quotaData l st os.value valid
  let data : RankRun.Inventory a toSite s :=
    { columns := c.value,columns_correct := columns_correct l st
      payoffs := st.tables,payoffs_correct := correct.game
      gridValue := st.prepared.scales.grid,grid_correct := correct.grid
      book := book.value,book_correct := computed,vertices := os.value.vertices
      vertices_correct := (orders_vertices l st).trans (congrArg Book.rankVertices computed.symm)
      parameters := quotas.value,parameters_correct := quotaData_value l st correct os.value valid (orders_sites l st)
      finiteBuyers := enumeration os.value.buyers valid.buyers_unique valid.buyers_complete
      finiteSites := enumeration os.value.sites valid.sites_unique valid.sites_complete
      finiteBids := enumeration os.value.bids valid.bids_unique valid.bids_complete }
  ⟨data,c.work.seq (os.work.seq (book.work.seq (quotas.work.seq (StochasticGames.CompilerRun.Work.one 0))))⟩

/-- Compute the ordinal book, quota tables, rank rows and selected first
contact from the sorted real-bid and cut lists provided by the search driver. -/
def fromLists (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) : Run (StoredLookup.SelectedStored a toSite s) :=
  RankRun.fromBuilder (assemble l st correct)

theorem fromLists_value (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) :
    (fromLists l st correct).value = (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).1 :=
  RankRun.fromBuilder_value _

end Kintali.QuotaSweep.SelectedBuilder
