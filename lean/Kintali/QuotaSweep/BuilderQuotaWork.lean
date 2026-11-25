module

public import Kintali.QuotaSweep.BuilderParameters
public import Kintali.QuotaSweep.BuilderOrderWork

/-! # Addressed costs of the selected quota vector and active sets -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def quotaBits (L : ℕ) := 2*L+scaleWidth L+indexWidth L+4
def builderWidth (L : ℕ) := TrialWork.scalarWidth (quotaBits L)+orderWidth L+indexWidth L+1
def massSlots (L : ℕ) := 6+(2*(recordLimit L+2)+1)+(1+TrialWork.scalarSlots (quotaBits L))+1

theorem indexes_fit (L : ℕ) : indexWidth L ≤ builderWidth L ∧ orderWidth L ≤ builderWidth L ∧
    TrialWork.scalarWidth (quotaBits L) ≤ builderWidth L := by unfold builderWidth; omega

theorem groupSize_le (l : Lists a toSite s) (h : StoredLookup.SelectedGroups a toSite s) :
    (groupSize l h).value ≤ grid a.game := by
  rw [groupSize_value]
  exact (Nat.sub_le _ _).trans ((Sparse.partition (G := grid a.game) a.game toSite s h.1).hi_le_end h.2)

theorem unit_fits (a : Input) (valid : a.Valid) :
    Fits (quotaBits (Binary.lengthInput a)) (privateScale a.game/(grid a.game)) :=
  ((scale_fits a valid).div (Fits.natCast _)).mono (by
    have := Binary.grid_size a valid
    unfold quotaBits indexWidth; omega)

theorem siteRate_work (d : TrialWork.Fields a.types a.targets) {c u w : ℕ} (data : TrialWork.FieldBound d c u)
    (priced : TrialWork.scalarWidth u ≤ w) (j : Fin a.targets) :
    (siteRate d j).Bound (c+4+4) w := by
  have h := data.gain j
  have f := (TrialWork.lt_work (Fits.zero.mono data.positive) h.2).weaken le_rfl priced
  have r := (TrialWork.inverse_work h.2).weaken le_rfl priced
  have cmp : (if (TrialWork.lt 0 (d.gain j).value).value then TrialWork.inverse (d.gain j).value
      else step 0 0).Bound 4 w := by split; exact r; exact (bound_step _ _).weaken (by decide) (Nat.zero_le _)
  exact (bound_bind (h.1.weaken le_rfl ((show u ≤ TrialWork.scalarWidth u by unfold TrialWork.scalarWidth; omega).trans priced))
    (bound_bind f cmp)).weaken (by omega) le_rfl

theorem buyerMass_work (l : Lists a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (d : TrialWork.Fields a.types a.targets) (data : TrialWork.FieldBound d 2 (2*Binary.lengthInput a+1))
    (b : Buyers a toSite s) :
    let L := Binary.lengthInput a
    (buyerMass l d (privateScale a.game/grid a.game) b).Bound (massSlots L) (builderWidth L) := by
  let L := Binary.lengthInput a
  let u := quotaBits L
  let w := builderWidth L
  have db : 2*L+1 ≤ u := by unfold u quotaBits; omega
  have rates := data.mono db
  have fw := (indexes_fit L).2.2
  have base : u ≤ w := (show u ≤ TrialWork.scalarWidth u by unfold TrialWork.scalarWidth; omega).trans fw
  rcases b with i|h
  · exact (rates.prior i).1.weaken (by unfold massSlots; omega) base
  · have number := groupSize l h
    have count := (groupSize_work l valid hs h).weaken le_rfl (indexes_fit L).1
    have gs := (Nat.size_le_size (groupSize_le l h)).trans (Binary.grid_size a valid)
    have cast : Fits u ((groupSize l h).value : ℚ) :=
      (Fits.natCast _).mono (by unfold u quotaBits indexWidth; dsimp only [L] at *; omega)
    have read : (RankRun.scaleIndex (groupSize l h).value).Bound 1 w :=
      (bound_step _ _).weaken le_rfl ((gs.trans (by unfold u quotaBits indexWidth; dsimp only [L] at *; omega) : _ ≤ u).trans base)
    have scaled := (TrialWork.times_work cast (unit_fits a valid)).weaken le_rfl fw
    let cost := (2*(recordLimit L+2)+1)+(1+TrialWork.scalarSlots u)
    have branch : (if (active d h.1).value then (do
      let n ← groupSize l h
      let q ← RankRun.scaleIndex n
      TrialWork.times q (privateScale a.game/grid a.game)) else step 0 0).Bound (cost+1) w := by
      split
      · exact (bound_bind count (bound_bind read scaled)).weaken (Nat.le_succ _) le_rfl
      · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
    exact (bound_bind (active_work d rates fw h.1) branch).weaken (by unfold massSlots; dsimp only [cost,u,L]; omega) le_rfl

theorem order_counts (o : Orders a toSite s) (ok : o.Valid) (hs : SelectionBound a s) :
    let r := recordLimit (Binary.lengthInput a)
    o.sites.length ≤ r ∧ o.buyers.length ≤ r ∧ o.bids.length ≤ r := by
  have card (T : Type) [DecidableEq T] [Fintype T] (xs : List T) (unique : xs.Nodup) :
      xs.length ≤ Fintype.card T := by
    rw [← List.toFinset_card_of_nodup unique]; exact Finset.card_le_univ _
  have inv := (selected_inventory a toSite s hs).2.2.1
  have combined : Fintype.card (Bids a toSite s)+
      (Fintype.card (Buyers a toSite s)+a.targets) ≤ recordLimit (Binary.lengthInput a) := by
    simpa only [Sparse.R,Record,Vertex,Fintype.card_sum,Fintype.card_fin,Bids,Buyers,Sparse.B,Sparse.E] using inv
  exact ⟨(card _ _ ok.sites_unique).trans (by rw [Fintype.card_fin]; omega),
    (card _ _ ok.buyers_unique).trans (by omega),(card _ _ ok.bids_unique).trans (by omega)⟩

def quotaSlots (L : ℕ) :=
  let r := recordLimit L
  let u := quotaBits L
  3+(4+TrialWork.scalarSlots u)+(r*(10+3)+1)+(r*(massSlots L+3)+1)+(2+r*7)+
    (1+r*(2+4))+TrialWork.scalarSlots u+1+TrialWork.scalarSlots u+1

set_option maxHeartbeats 1600000 in
theorem quotaData_work (l : Lists a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (st : InitializationWork.State a.types a.targets) (correct : InitializationWork.Correct a valid.1 st)
    (o : Orders a toSite s) (ok : o.Valid) :
    let L := Binary.lengthInput a
    (quotaData l st o ok).Bound (quotaSlots L) (builderWidth L) := by
  let L := Binary.lengthInput a
  let u := quotaBits L
  let w := builderWidth L
  let r := recordLimit L
  let d := st.tables.fields
  let unit := TrialWork.divide st.prepared.scales.privateScale (st.prepared.scales.grid : ℚ)
  let rates := rowsOf o.sites (siteRate d)
  let masses := rowsOf o.buyers (buyerMass l d unit.value)
  let mask := privateBuyers d o ok
  let maxv := MaximaWork.scan d.gain o.sites
  let up := TrialWork.plus 1 maxv.value
  let target := TrialWork.times st.prepared.scales.privateScale (st.tables.resources : ℚ)
  have narrow : 2*L+1 ≤ u := by unfold u quotaBits; omega
  have data := correct.fields.mono narrow
  have width := (indexes_fit L).2.2
  have base : u ≤ w := (show u ≤ TrialWork.scalarWidth u by unfold TrialWork.scalarWidth; omega).trans width
  obtain ⟨cs,cb,_⟩ := order_counts o ok hs
  have scale : Fits u st.prepared.scales.privateScale := correct.privateScale ▸ (scale_fits a valid).mono
    (by unfold u quotaBits; dsimp only [L]; omega)
  have gridSize : st.prepared.scales.grid.size+1 ≤ u := by
    rw [correct.grid]; have := Binary.grid_size a valid; unfold u quotaBits indexWidth; dsimp only [L]; omega
  have uf : unit.Bound (4+TrialWork.scalarSlots u) w :=
    (TrialWork.divide_work scale ((Fits.natCast _).mono gridSize)).weaken le_rfl width
  have ue : unit.value = privateScale a.game/(grid a.game) := by simp [unit,correct.grid,correct.privateScale]
  have rb : rates.Bound (r*13+1) w := (rowsOf_work _ _ (siteRate_work d data width)).weaken
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ cs) 1) le_rfl
  have mb : masses.Bound (r*(massSlots L+3)+1) w := by
    unfold masses; rw [ue]
    exact (rowsOf_work _ _ (buyerMass_work l valid hs d correct.fields)).weaken
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ cb) 1) le_rfl
  have pb : mask.Bound (2+r*7) w := (privateBuyers_work d o ok data width).weaken
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ cb) _) le_rfl
  have gb : maxv.Bound (1+r*6) w := (MaximaWork.scan_work d.gain o.sites data.positive width
    (fun j => (data.gain j).1.weaken le_rfl base) (fun j => (data.gain j).2)).weaken
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ cs) _) le_rfl
  have ub : up.Bound (TrialWork.scalarSlots u) w :=
    (TrialWork.plus_work (Fits.one.mono data.positive)
      (MaximaWork.scan_fits d.gain o.sites data.positive (fun j => (data.gain j).2))).weaken le_rfl width
  have res : Fits u (st.tables.resources : ℚ) := data.budget
  have tb : target.Bound (TrialWork.scalarSlots u) w := (TrialWork.times_work scale res).weaken le_rfl width
  have limits : st.prepared.scales.grid.size ≤ w ∧ st.tables.resources.size ≤ w := by
    refine ⟨(by omega : st.prepared.scales.grid.size ≤ u).trans base,?_⟩
    have h := res.1
    simp only [Rat.num_natCast,Int.natAbs_natCast] at h
    exact h.trans base
  change 1+(1+(1+(unit.work.slots+(rates.work.slots+(masses.work.slots+(mask.work.slots+
    (maxv.work.slots+(up.work.slots+(1+(target.work.slots+1)))))))))) ≤ _ ∧
    max 0 (max 0 (max st.prepared.scales.grid.size (max unit.work.width (max rates.work.width
      (max masses.work.width (max mask.work.width (max maxv.work.width (max up.work.width
        (max st.tables.resources.size (max target.work.width 0)))))))))) ≤ _
  obtain ⟨us,uw⟩ := uf
  obtain ⟨rs,rw⟩ := rb
  obtain ⟨ms,mw⟩ := mb
  obtain ⟨ps,pw⟩ := pb
  obtain ⟨gs,gw⟩ := gb
  obtain ⟨hs',hw⟩ := ub
  obtain ⟨ts,tw⟩ := tb
  constructor
  · change _ ≤ quotaSlots L
    unfold quotaSlots; dsimp only [r,u] at *; omega
  · change _ ≤ w; omega

end Kintali.QuotaSweep.SelectedBuilder
