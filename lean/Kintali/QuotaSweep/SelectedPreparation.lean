module

public import Kintali.QuotaSweep.ContactCharge
public import Kintali.QuotaSweep.StoredLookupRun

/-! # Public-input bounds for the stored sparse ordinal preprocessing -/

@[expose] public section
namespace Kintali.QuotaSweep.ContactCharge

open Kintali.ContactSize Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ExactRecovery
open StochasticGames.BinarySize

/-- Evaluations and comparisons in the actual eager ordinal table, after
the sparse record and vertex enumerations have been supplied. -/
theorem selected_key_counts (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) :
    let G := grid a.game
    let l := (Sparse.selectedLayout (G := G) a.game toSite s).stored
    let K := Sparse.book a.game Fin.val Fin.val l
    let keys := Sparse.countedKeyTable K.records
      (fun i e => Expanded.key a.game Fin.val Fin.val (l.embedVertex i) (l.embedRecord e)) K.rankVertices
    let r := recordLimit (Binary.lengthInput a)
    keys.1 = Sparse.keyedTable a.game Fin.val Fin.val l ∧ keys.2.1 ≤ r*r ∧ keys.2.2 ≤ r*(r*r) := by
  let G := grid a.game
  let l := (Sparse.selectedLayout (G := G) a.game toSite s).stored
  let K := Sparse.book a.game Fin.val Fin.val l
  let r := recordLimit (Binary.lengthInput a)
  have hr : K.records.length ≤ r := by
    simp only [K,l,Sparse.Layout.stored_eq]
    exact (selected_inventory a toSite s hs).2.2.2
  have v : K.rankVertices.length ≤ r := (List.length_filterMap_le ..).trans hr
  have eq := Sparse.key_preparation a.game Fin.val Fin.val l
  dsimp only at eq ⊢
  rw [eq]
  exact ⟨rfl,Nat.mul_le_mul v hr,Nat.mul_le_mul v (Nat.mul_le_mul hr hr)⟩

/-- The three finite fields and the last record identifier of any expanded
preference key fit the width used by the selected contact adapter. -/
theorem preference_words (a : Input) (valid : a.Valid)
    (v : Expanded.V (Fin a.types) (Fin a.targets) (grid a.game))
    (e : Expanded.R (Fin a.types) (Fin a.targets) (grid a.game)) :
    let w := operandWidth (Binary.lengthInput a)
    (∀ q : ℚ, Expanded.primary a.game v e = (q : WithTop ℚ) → Fits w q) ∧
    (Expanded.tie Fin.val Fin.val v e).1.size ≤ w ∧
    (Expanded.tie Fin.val Fin.val v e).2.size ≤ w ∧ (Encodable.encode e).size ≤ w := by
  let L := Binary.lengthInput a
  let c := L+Binary.gridBitBound L
  have g : (grid a.game).size ≤ c := (Binary.grid_size a valid).trans (Nat.le_add_left ..)
  have k : a.types.size ≤ c := (size_le_self a.types).trans ((Binary.dimensions a).2.1.trans (Nat.le_add_right ..))
  have m : a.targets.size ≤ c := (size_le_self a.targets).trans ((Binary.dimensions a).1.trans (Nat.le_add_right ..))
  have wl : L ≤ recordLimit L := by unfold recordLimit; omega
  have a1 (i j) := Binary.datum_parts a valid (intercept_mem a.game i j)
  have b1 (i j) := Binary.datum_parts a valid (slope_mem a.game i j)
  have tie := KeyWidth.tie_bits k m g v e
  have wc : c ≤ operandWidth L := by unfold operandWidth c; omega
  refine ⟨?_,tie.1.trans wc,tie.2.trans wc,(KeyWidth.record_code k m g e).trans (show 4*c+3 ≤ operandWidth L by unfold operandWidth c; omega)⟩
  intro q hq
  exact (KeyWidth.primary_fits a.game a1 b1 g v e hq).mono
    (show 2*(2*L+1)+2*c+8 ≤ operandWidth L by unfold operandWidth c; omega)

/-- The stored contact's index codes, prefix arithmetic and rank-key fields
share the same input polynomial. -/
theorem record_word (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (hs : SelectionBound a s) (e : StoredLookup.SelectedRecord a toSite s) :
    (Encodable.encode e).size ≤ operandWidth (Binary.lengthInput a) := by
  let h := StoredLookup.selected_key_bound a toSite s hs
  have fits := h.size e
  rw [StoredLookup.recordKey_value] at fits
  exact fits.trans (by unfold StoredLookup.width operandWidth; omega)

end Kintali.QuotaSweep.ContactCharge
