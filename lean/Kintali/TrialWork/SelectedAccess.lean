module

public import Kintali.TrialWork.SelectedLists

/-! The allocation lookup is the numeric lookup on the stored selected
contact. Sorted retained bids use charged list indexing and private groups
contain their site directly. -/

@[expose] public section
namespace Kintali.TrialWork.Selected

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery MarketTrial QuoteSearch
open QuotaSweep ContactSize InputOutput QuotaSweep.StoredLookup

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def fieldsWidth (L : ℕ) := 2*L+1

def sizeLimit (L : ℕ) := recordLimit L+L

def inputWidth (L : ℕ) := sizeLimit L+StoredLookup.width L+scalarWidth (fieldsWidth L)+
  allocationWidth L+viewWidth L+scaleWidth L+toleranceWidth L+2*(Binary.gridBitBound L+1)+2

def accessSlots (L : ℕ) := recordLimit L+StoredLookup.slots (recordLimit L)+6

def access (l : Lists a toSite s) (d : Fields a.types a.targets) (dir : Vector (Fin a.targets) a.types)
    (z : SelectedStored a toSite s) :
    Access a.types a.targets (grid a.game) (SelectedReals a toSite s) (SelectedGroups a toSite s) where
  real i := get l.bids (Fin.cast (congrArg List.length l.bidOrder).symm i)
  site h := step 0 h.1
  holding r := StoredLookup.selected a toSite s z r
  redirect i := step a.types.size dir[i.val]
  active j := d.gain j >>= lt 0

theorem access_reads (l : Lists a toSite s) (d : Fields a.types a.targets) (dg : d.game = a.game)
    (dir : Vector (Fin a.targets) a.types) (dt : ∀ i : Fin a.types, dir[i.val] = toSite i)
    (z : SelectedStored a toSite s) :
    Reads (access l d dir z) a.game (Sparse.selectedLayout (G := grid a.game) a.game toSite s)
      z.encodedView.allocation toSite := by
  constructor
  · intro i
    simp only [access,get_value]
    change l.bids.get _ = (Sparse.realOrder a.game toSite s).get i
    have lookup {T : Type} {u v : List T} (e : u = v) (r : Fin v.length) :
        u.get (Fin.cast (congrArg List.length e).symm r) = v.get r := by subst u; rfl
    exact lookup l.bidOrder i
  · intro h; rfl
  · exact StoredLookup.selected_value a toSite s z
  · exact dt
  · intro j
    simp only [access,Run.bind_value,lt_value]
    change decide (0 < d.game.gain j) = _
    rw [dg]

theorem access_bound (l : Lists a toSite s) (d : Fields a.types a.targets) (dir : Vector (Fin a.targets) a.types)
    (valid : a.Valid) (normal : ¬a.game.DirectCase) (hs : SelectionBound a s)
    (fd : FieldBound d 2 (fieldsWidth (Binary.lengthInput a))) :
    let L := Binary.lengthInput a
    let z := (ContactCharge.selected a toSite s).value
    AccessBound (access l d dir z) (accessSlots L) (inputWidth L) := by
  let L := Binary.lengthInput a
  let R := recordLimit L
  let W := inputWidth L
  let z := (ContactCharge.selected a toSite s).value
  have rwide : R ≤ W := by unfold W inputWidth sizeLimit R; omega
  have fw : fieldsWidth L ≤ W := by unfold W inputWidth scalarWidth; omega
  have fwide : scalarWidth (fieldsWidth L) ≤ W := by unfold W inputWidth; omega
  have lim : l.bids.length ≤ R := l.bid_count hs
  have narrow : StoredLookup.width L ≤ W := by unfold W inputWidth; omega
  have slot : 6 ≤ accessSlots L := by unfold accessSlots; omega
  have single : 1 ≤ accessSlots L := by omega
  have alloc := (selected_state a valid normal toSite s hs).2
  change AccessBound (access l d dir z) (accessSlots L) W
  constructor
  · intro i
    let ix := Fin.cast (congrArg List.length l.bidOrder).symm i
    have bound : ix.val+1 ≤ R := ix.isLt.trans_le lim
    exact (get_bound l.bids ix).weaken (bound.trans (by unfold accessSlots R; omega))
      ((size_le_self _).trans (by omega))
  · intro h; exact (bound_step 0 _).weaken single (Nat.zero_le _)
  · intro e
    exact (contact_read_work a toSite s hs e).weaken
      (show StoredLookup.slots (recordLimit L) ≤ accessSlots L by unfold accessSlots; omega) narrow
  · intro i; exact (bound_step _ _).weaken single (fd.kSize.trans fw)
  · intro j
    apply Run.Bound.weaken (k := 2+4) (w := W) ?_ slot le_rfl
    apply bound_bind ((fd.gain j).1.weaken le_rfl fw)
    exact (lt_work (Fits.zero.mono fd.positive) (fd.gain j).2).weaken le_rfl fwide
  · intro e
    rw [show ((access l d dir z).holding e).value = (z.encodedRead e).1 from StoredLookup.selected_value ..]
    exact (alloc e).mono (show allocationWidth L ≤ W by unfold W inputWidth; omega)
  · exact fd.kSize.trans fw
  · exact fd.mSize.trans fw
  · exact fd.positive.trans fw

end Kintali.TrialWork.Selected
