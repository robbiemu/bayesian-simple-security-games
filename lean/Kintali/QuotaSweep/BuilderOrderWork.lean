module

public import Kintali.QuotaSweep.BuilderOrderSpec

/-! # Verified finite enumerations and their addressed construction cost -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def orderWidth (L : ℕ) := Lists.labelsWidth L+StoredLookup.width L+indexWidth L
def inventorySize (L : ℕ) := recordLimit L+L+1
def orderSlots (L : ℕ) :=
  let n := inventorySize L
  Lists.labelsSlots L+2*(2*L+2)+4*(4*(10*n+1))+(1+(5*n)*(5*n+1)*30)+(5*n+1)+1

set_option maxHeartbeats 2600000 in
theorem orders_work (l : Lists a toSite s) (hs : SelectionBound a s) (st : InitializationWork.State a.types a.targets) :
    let L := Binary.lengthInput a
    (makeOrders l st).Bound (orderSlots L) (orderWidth L) := by
  let L := Binary.lengthInput a
  let n := inventorySize L
  let W := orderWidth L
  let is := number (step 0 st.tables.priors.toArray.size) st.tables.priors.size_toArray
  let js := number (step 0 st.tables.gains.toArray.size) st.tables.gains.size_toArray
  let bs := sumList is.value l.groups.value
  let es := sumList l.reals.value l.groups.value
  let vs := sumList bs.value js.value
  let all := sumList es.value vs.value
  let sorted := TrialWork.ListBuild.sortedSet (compareRecord a toSite s) all.value
  have d := Binary.dimensions a
  have k : a.types ≤ L := d.2.1
  have m : a.targets ≤ L := d.1
  have sizes : L ≤ n ∧ recordLimit L ≤ n := by unfold n inventorySize; omega
  have fit : L ≤ W := by unfold W orderWidth indexWidth; omega
  have wl : Lists.labelsWidth L ≤ W := by unfold W orderWidth; omega
  have wc : StoredLookup.width L ≤ W := by unfold W orderWidth; omega
  have label := l.labels_work hs
  change l.reals.work.slots+l.groups.work.slots ≤ Lists.labelsSlots L ∧
    max l.reals.work.width l.groups.work.width ≤ Lists.labelsWidth L at label
  have a₁ : is.Bound (2*L+2) W := (number_work _ st.tables.priors.size_toArray
    ((bound_step 0 _).weaken le_rfl (Nat.zero_le W))
    ((size_le_self _).trans (k.trans fit))).weaken (by omega) le_rfl
  have a₂ : js.Bound (2*L+2) W := (number_work _ st.tables.gains.size_toArray
    ((bound_step 0 _).weaken le_rfl (Nat.zero_le W))
    ((size_le_self _).trans (m.trans fit))).weaken (by omega) le_rfl
  have ri : l.reals.value.length ≤ n := by
    rw [l.reals_value,List.length_finRange,← l.bidOrder]
    exact (l.bid_count hs).trans sizes.2
  have rg : l.groups.value.length ≤ n := (l.groups_length hs).trans sizes.2
  have il : is.value.length ≤ n := by simp only [is,numbersK st,List.length_finRange]; exact k.trans sizes.1
  have jl : js.value.length ≤ n := by simp only [js,numbersM st,List.length_finRange]; exact m.trans sizes.1
  have bl : bs.value.length ≤ 2*n := by simpa only [bs,sumList_value,List.length_append,List.length_map] using
    (show is.value.length+l.groups.value.length ≤ 2*n by omega)
  have el : es.value.length ≤ 2*n := by simpa only [es,sumList_value,List.length_append,List.length_map] using
    (show l.reals.value.length+l.groups.value.length ≤ 2*n by omega)
  have vl : vs.value.length ≤ 3*n := by simpa only [vs,sumList_value,List.length_append,List.length_map] using
    (show bs.value.length+js.value.length ≤ 3*n by omega)
  have al : all.value.length ≤ 5*n := by simpa only [all,sumList_value,List.length_append,List.length_map] using
    (show es.value.length+vs.value.length ≤ 5*n by omega)
  let makeCost := 4*(10*n+1)
  have b : bs.Bound makeCost W := (sumList_work is.value l.groups.value W).weaken (by unfold makeCost; omega) le_rfl
  have e : es.Bound makeCost W := (sumList_work l.reals.value l.groups.value W).weaken (by unfold makeCost; omega) le_rfl
  have v : vs.Bound makeCost W := (sumList_work bs.value js.value W).weaken (by unfold makeCost; omega) le_rfl
  have z : all.Bound makeCost W := (sumList_work es.value vs.value W).weaken (by unfold makeCost; omega) le_rfl
  have sortCost : sorted.Bound (1+(5*n)*(5*n+1)*30) W :=
    (TrialWork.ListBuild.sortedSet_work _ all.value (fun x y => (compareRecord_work hs x y).weaken le_rfl wc)).weaken
      (by gcongr) le_rfl
  have rv : (rights sorted.value).Bound (5*n+1) W := (rights_work _ W).weaken
    (Nat.succ_le_succ ((TrialWork.ListBuild.sortedSet_length (compareRecord a toSite s) all.value).trans al)) le_rfl
  change l.reals.work.slots+(l.groups.work.slots+(is.work.slots+(js.work.slots+(bs.work.slots+
    (es.work.slots+(vs.work.slots+(all.work.slots+(sorted.work.slots+((rights sorted.value).work.slots+1))))))))) ≤ _ ∧
    max l.reals.work.width (max l.groups.work.width (max is.work.width (max js.work.width (max bs.work.width
      (max es.work.width (max vs.work.width (max all.work.width (max sorted.work.width
        (max (rights sorted.value).work.width 0))))))))) ≤ _
  obtain ⟨lwork,lwidth⟩ := label
  obtain ⟨bs₁,bw₁⟩ := a₁
  obtain ⟨bs₂,bw₂⟩ := a₂
  obtain ⟨bc,bw⟩ := b
  obtain ⟨ec,ew⟩ := e
  obtain ⟨vc,vw⟩ := v
  obtain ⟨ac,aw⟩ := z
  obtain ⟨sc,sw⟩ := sortCost
  obtain ⟨rc,rw⟩ := rv
  constructor
  · change _ ≤ orderSlots L
    unfold orderSlots
    change _ ≤ Lists.labelsSlots L+2*(2*L+2)+4*(4*(10*n+1))+(1+(5*n)*(5*n+1)*30)+(5*n+1)+1
    dsimp only [makeCost] at bc ec vc ac
    omega
  · change _ ≤ W
    omega

end Kintali.QuotaSweep.SelectedBuilder
