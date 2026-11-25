module

public import Kintali.QuotaSweep.BuilderOrders

/-! # The finite enumerations of the selected sparse record order -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

structure Orders.Valid (o : Orders a toSite s) : Prop where
  sites_unique : o.sites.Nodup
  sites_complete : ∀ j, j ∈ o.sites
  buyers_unique : o.buyers.Nodup
  buyers_complete : ∀ j, j ∈ o.buyers
  bids_unique : o.bids.Nodup
  bids_complete : ∀ e, e ∈ o.bids
  records : o.records = (Sparse.book a.game Fin.val Fin.val
    ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored)).records
  vertices : o.vertices = o.records.filterMap Sum.getRight?

theorem orders_valid (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    (makeOrders l st).value.Valid := by
  have rs : l.reals.value.Nodup := by rw [l.reals_value]; exact List.nodup_finRange _
  refine ⟨by rw [orders_sites]; exact List.nodup_finRange _,
    fun t => by rw [orders_sites]; exact List.mem_finRange _,
    by rw [orders_buyers]; exact sumList_unique _ _ (List.nodup_finRange _) l.groups_unique,
    fun _ => by rw [orders_buyers]; exact sumList_complete _ _ (List.mem_finRange ·) l.groups_complete _,
    by rw [orders_bids]; exact sumList_unique _ _ rs l.groups_unique,
    fun _ => by rw [orders_bids]; exact sumList_complete _ _ (fun t => by simp) l.groups_complete _,
    orders_records l st,?_⟩
  simp only [makeOrders,Run.bind_value,step_value,rights_value]

/-- Use the proved nodup data directly for the runtime finite universe. -/
@[instance_reducible] def enumeration {T : Type} (xs : List T) (unique : xs.Nodup) (total : ∀ t, t ∈ xs) : Fintype T :=
  ⟨⟨xs,unique⟩,total⟩

end Kintali.QuotaSweep.SelectedBuilder
