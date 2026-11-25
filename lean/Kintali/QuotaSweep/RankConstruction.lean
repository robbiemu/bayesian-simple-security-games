module

public import Kintali.QuotaSweep.RankComparison

/-! # Constructing a selected rank table from stored record and key access -/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open Kintali.ExactRecovery Kintali.ContactSize Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch
open StochasticGames.CompilerRun StochasticGames.BinarySize

abbrev SelectedVertex (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :=
  Sparse.V (Fin a.types) (Fin a.targets) (StoredLookup.SelectedGroups a toSite s)

def selectedTable (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (make : SelectedVertex a toSite s → StoredLookup.SelectedRecord a toSite s → Run Expanded.Key) :=
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  let K := Sparse.book a.game Fin.val Fin.val l
  table K.rankVertices K.records make keyLess

def KeysCorrect (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (make : SelectedVertex a toSite s → StoredLookup.SelectedRecord a toSite s → Run Expanded.Key) :=
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  ∀ v e, (make v e).value = Expanded.key a.game Fin.val Fin.val (l.embedVertex v) (l.embedRecord e)

theorem selectedTable_value (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (make) (correct : KeysCorrect a toSite s make) :
    (selectedTable a toSite s make).value =
      Sparse.keyedTable a.game Fin.val Fin.val ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored) := by
  dsimp only [KeysCorrect] at correct
  simp only [selectedTable,table_value _ _ _ _ keyLess_value,correct,Sparse.keyedTable]

def inputSlots (L k : ℕ) := slots (recordLimit L) (recordLimit L) k 17

theorem selectedTable_work (a : Input) (valid : a.Valid) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) (make)
    (correct : KeysCorrect a toSite s make) {k : ℕ}
    (charged : ∀ v e, (make v e).Bound k (ContactCharge.width (Binary.lengthInput a))) :
    (selectedTable a toSite s make).Bound (inputSlots (Binary.lengthInput a) k)
      (ContactCharge.width (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  let K := Sparse.book a.game Fin.val Fin.val l
  let r := recordLimit L
  have hr : K.records.length ≤ r := by
    simp only [K,l,Sparse.Layout.stored_eq]
    exact (selected_inventory a toSite s hs).2.2.2
  have hv : K.rankVertices.length ≤ r := (List.length_filterMap_le ..).trans hr
  have cmp (v : SelectedVertex a toSite s) (e f : StoredLookup.SelectedRecord a toSite s) :
      (keyLess (make v e).value (make v f).value).Bound 17 (ContactCharge.width L) := by
    rw [correct,correct]
    exact keyLess_work _ _ (inputKey_fits a valid ..) (inputKey_fits a valid ..)
  have wr : K.records.length.size+1 ≤ ContactCharge.width L := by
    have := (size_le_self _).trans hr
    dsimp [K] at this ⊢
    unfold ContactCharge.width ContactCharge.operandWidth TrialWork.scalarWidth
    dsimp [r] at this
    omega
  have work := table_bound K.rankVertices K.records make keyLess (fun v _ e _ => charged v e)
    (fun v _ e _ f _ => cmp v e f) wr
  exact work.weaken (by unfold inputSlots slots rowSlots; dsimp [r] at *; gcongr) le_rfl

/-- The explicit lengths of the selected real and group columns and all
finite book/initial-quota sets used by the restricted constructor. -/
theorem selected_inventory_sizes (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) :
    let G := grid a.game
    let reals := Sparse.realOrder (G := G) a.game toSite s
    let groups := StoredLookup.SelectedGroups a toSite s
    let l := (Sparse.selectedLayout (G := G) a.game toSite s).stored
    let K := Sparse.book a.game Fin.val Fin.val l
    let P := Sparse.selectedParameters (G := G) a.game toSite s (privateScale a.game)
    let r := recordLimit (Binary.lengthInput a)
    reals.length ≤ r ∧ (Sparse.Layout.keys (Fin reals.length)).length ≤ r ∧
    (Sparse.Layout.keys groups).length ≤ r ∧ K.records.length ≤ r ∧
    K.rankVertices.length ≤ r ∧ K.buyerOrder.length ≤ r ∧ K.vertexOrder.length ≤ r ∧
    K.retained.card ≤ r ∧ P.privateBuyers.card ≤ r ∧
    ∀ j, (Sparse.siteCuts (G := G) a.game toSite s j).card ≤ r+2 := by
  let G := grid a.game
  let reals := Sparse.realOrder (G := G) a.game toSite s
  let H := StoredLookup.SelectedGroups a toSite s
  let l := (Sparse.selectedLayout (G := G) a.game toSite s).stored
  let K := Sparse.book a.game Fin.val Fin.val l
  let r := recordLimit (Binary.lengthInput a)
  obtain ⟨ar,gr,rec,hr⟩ := selected_inventory a toSite s hs
  have real : reals.length ≤ r := by simpa only [Fintype.card_fin] using ar
  have size : K.records.length ≤ r := by simpa only [K,l,Sparse.Layout.stored_eq] using hr
  have first (T : Type) [Fintype T] [DecidableEq T] [Encodable T] :
      (Sparse.Layout.keys T).length = Fintype.card T := by simp [Sparse.Layout.keys]
  have count : Fintype.card (Sparse.E (Fin reals.length) H) +
      Fintype.card (Sparse.B (Fin a.types) H) + a.targets ≤ r := by
    simpa only [Sparse.R,Record,Vertex,Fintype.card_sum,Fintype.card_fin,Nat.add_assoc,
      Sparse.E,Sparse.B] using rec
  have ecount : Fintype.card (Sparse.E (Fin reals.length) H) ≤ r := by omega
  have bcount : Fintype.card (Sparse.B (Fin a.types) H) ≤ r := by omega
  refine ⟨real,(first _).le.trans ar,(first _).le.trans gr,size,
    (List.length_filterMap_le ..).trans size,K.buyerOrder_length.trans size,K.vertexOrder_length.trans size,
    (Finset.card_le_univ _).trans ecount,(Finset.card_le_univ _).trans bcount,?_⟩
  intro j
  let bids : Finset (Sparse.ListedBid a.types a.targets G) := Sparse.realBids a.game toSite s
  have bsize : bids.card ≤ r := (Sparse.realOrder_length a.game toSite s).symm.le.trans real
  let selected := (bids.filter fun b => b.2.1 = j).image fun b => b.2.2.val
  have small : selected.card ≤ bids.card := Finset.card_image_le.trans (Finset.card_filter_le ..)
  exact (Finset.card_insert_le 0 _).trans (Nat.add_le_add_right
    ((Finset.card_insert_le G selected).trans (Nat.add_le_add_right (small.trans bsize) 1)) 1)

end Kintali.QuotaSweep.RankRun
