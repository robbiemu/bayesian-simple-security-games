module

public import Kintali.TrialWork.InventoryWork
public import Kintali.InputOutput.InitializationWork
public import Kintali.SearchBounds

/-! # Materialized bid and cut lists at each selected restriction -/

@[expose] public section

namespace Kintali.TrialWork.Inventory

open StochasticGames.CompilerRun ExactRecovery MarketTrial QuoteSearch ContactSize InputOutput
open LinearProgramming.ArithmeticRun Sparse ListBuild

variable {k m : ℕ}

def reserve (st : InitializationWork.State k m) (i : Fin k) : Run ℚ :=
  step k.size st.prepared.directory.price[i.val]

def toSite (st : InitializationWork.State k m) (i : Fin k) : Fin m :=
  st.prepared.directory.toSite[i.val]

/-- `G` is passed as a stored number so the trial can use it for every
index and price calculation. The equality transports only erased indices. -/
def buildAt (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (s : Selection (a.types*a.targets))
    (G : ℕ) (gridEq : G = grid a.game) : Run (Selected.Lists a (toSite st) s) :=
  let bids := listed (G := G) st.tables.fields (reserve st) s bidCompare
  let cuts := tabulate a.targets (cutLevels bids.value)
  have reserveEq (i : Fin a.types) :
      (reserve st i).value = Holdings.outsideCost st.tables.fields.game (toSite st) i := by
    have he : st.tables.fields.game = a.game := correct.game
    have red : toSite st = redirect a.game hm := funext correct.targets
    rw [he, red]
    exact correct.prices i
  have order : bids.value = realOrder (G := G) a.game (toSite st) s := by
    have he : st.tables.fields.game = a.game := correct.game
    simpa only [bids, he] using listed_value st.tables.fields (reserve st) (toSite st)
      reserveEq s bidCompare bidCompare_value
  let value : Selected.Lists a (toSite st) s :=
    { bids := gridEq ▸ bids.value
      cuts := cuts.value
      bidOrder := by subst G; exact order
      cutOrder j := by
        subst G
        have ho := cutLevels_value st.tables.fields (toSite st) s bids.value
          (by simpa only [show st.tables.fields.game = a.game from correct.game] using order) j
        simpa only [cuts,tabulate_value,Vector.getElem_ofFn,
          show st.tables.fields.game = a.game from correct.game] using ho }
  ⟨value,bids.work.seq (cuts.work.seq (Work.one 0))⟩

def build (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (s : Selection (a.types*a.targets)) :
    Run (Selected.Lists a (toSite st) s) :=
  buildAt a hm st correct s st.prepared.scales.grid correct.grid

def inputWidth (L : ℕ) :=
  2*L+1+OutsideWork.priceWidth (2*L+1)+Binary.gridBitBound L+L*L+L
def maxChoices (L : ℕ) := 4*Binary.witnesses L
def slots (L : ℕ) :=
  let J := maxChoices L
  let R := L*L*(J+1)
  realSlots L L J (inputWidth L) 2 + (3*(L+1)+L*(20*(R+3)^2)) + 1
def width (L : ℕ) := testWidth (inputWidth L)

theorem build_work (a : Input) (valid : a.Valid) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a valid.1 st) (s : Selection (a.types*a.targets))
    (selection : ValidSelection (4*witnessBound a.game) (eligible a.game valid.1) s) :
    (build a valid.1 st correct s).Bound (slots (Binary.lengthInput a)) (width (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  let W := inputWidth L
  let J := maxChoices L
  let G := st.prepared.scales.grid
  let f := st.tables.fields
  have dims := Binary.dimensions a
  have kL : a.types ≤ L := dims.2.1
  have mL : a.targets ≤ L := dims.1
  have fEq : f.game = a.game := correct.game
  have fBound : FieldBound f 2 W := correct.fields.mono (by unfold W inputWidth; omega)
  have idx : (a.types*a.targets).size ≤ W := by
    have q := Nat.mul_le_mul kL mL
    exact ((StochasticGames.BinarySize.size_le_self _).trans q).trans (by unfold W inputWidth; omega)
  have gridWidth : G.size ≤ W := by
    have h : G.size ≤ Binary.gridBitBound L := by rw [show G = grid a.game from correct.grid]; exact Binary.grid_size a valid
    unfold W inputWidth
    omega
  have allowed : ∀ p : Fin (a.types*a.targets), s[p].length ≤ J :=
    fun p => (selection.count p).trans ((Nat.sub_le _ _).trans
      (Nat.mul_le_mul_left 4 (Binary.witness_bound a)))
  have quoteBound (p : Fin (a.types*a.targets)) (z : ℕ) (hz : z ∈ s[p]) : z ≤ G := by
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective p
    have inside := selection.index _ z hz
    rw [eligible_at] at inside
    rw [show G = grid a.game from correct.grid]
    exact inside.le.trans (eligibleCount_le ..)
  have reserveBound (i : Fin a.types) : (reserve st i).Bound 2 W ∧ Fits W (reserve st i).value := by
    have scope : OutsideWork.priceWidth (2*L+1) ≤ W := by unfold W inputWidth; omega
    have fit := OutsideWork.endpoint_fits f correct.fields i (redirect a.game valid.1 i)
    have eq : (reserve st i).value = Holdings.outsideCost a.game (redirect a.game valid.1) i := correct.prices i
    rw [OutsideWork.endpoint_value, fEq] at fit
    have fit' : Fits (OutsideWork.priceWidth (2*L+1)) (reserve st i).value := by
      rw [eq]
      exact fit
    exact ⟨⟨by change 1 ≤ 2; decide, fBound.kSize⟩,fit'.mono scope⟩
  let bids := listed (G := G) f (reserve st) s bidCompare
  let cuts := tabulate a.targets (cutLevels bids.value)
  have bv := listed_work f (reserve st) s fBound gridWidth reserveBound idx allowed quoteBound
  have limit : bids.value.length ≤ L*L*(J+1) := by
    unfold bids listed
    rw [Run.bind_value]
    exact (sortedSet_length _ _).trans ((candidates_length f (reserve st) s J allowed).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul kL mL)))
  have cw : W ≤ testWidth W := by unfold testWidth scalarWidth; omega
  have cv := tabulate_bound (cutLevels bids.value) (fBound.mSize.trans cw) (fun j =>
    (cutLevels_work bids.value j gridWidth fBound.mSize).weaken
      (by gcongr) cw)
  have hb : realSlots a.types a.targets J W 2 ≤ realSlots L L J W 2 := by
    unfold realSlots allPairSlots
    dsimp only
    gcongr
  constructor
  · change bids.work.slots + (cuts.work.slots + 1) ≤ _
    have b : bids.work.slots ≤ realSlots L L J W 2 := bv.1.trans hb
    have c := cv.1
    have cGoal : cuts.work.slots ≤ 3*(L+1)+L*(20*(L*L*(J+1)+3)^2) := by
      refine c.trans ?_
      gcongr
    rw [← Nat.add_assoc]
    exact Nat.add_le_add_right (Nat.add_le_add b cGoal) 1
  · exact max_le bv.2 (max_le cv.2 (Nat.zero_le _))

end Kintali.TrialWork.Inventory
