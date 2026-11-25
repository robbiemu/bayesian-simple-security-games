module

public import Kintali.QuotaSweep.BuilderCuts

/-! # Materializing the two coordinate columns from the prepared lists -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def realColumn (l : Lists a toSite s) :=
  let eq := congrArg List.length l.bidOrder
  vectorBy (length l.bids) ((length_value l.bids).trans eq) (fun i => get l.bids (Fin.cast eq.symm i))

theorem realColumn_value (l : Lists a toSite s) (i : StoredLookup.SelectedReals a toSite s) :
    (realColumn l).value[i.val] = (Sparse.selectedLayout (G := grid a.game) a.game toSite s).real i := by
  rw [realColumn,vectorBy_value]
  simp only [Vector.getElem_ofFn,get_value]
  change l.bids.get _ = (Sparse.realOrder a.game toSite s).get i
  generalize_proofs h
  exact (show ∀ (u v : List (Sparse.ListedBid a.types a.targets (grid a.game))) (e : u=v) (j : Fin v.length),
      u.get (Fin.cast (congrArg List.length e).symm j)=v.get j by rintro u v rfl j; rfl) _ _ l.bidOrder i

def gapRow (l : Lists a toSite s) (j : Fin a.targets) :=
  vectorBy (l.count j) (l.count_value j) (fun h => rep l ⟨j,h⟩)

def rows (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :=
  vectorBy (step 0 st.tables.gains.toArray.size) st.tables.gains.size_toArray fun j => do
    let xs ← gapRow l j
    step 0 xs.toArray

theorem rows_length (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) (j : Fin a.targets) :
    (rows l st).value[j.val].size = (Sparse.partition (G := grid a.game) a.game toSite s j).groups := by
  simp [rows,vectorBy_value]

def columns (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :=
  let r := realColumn l
  let p := rows l st
  let c : RankRun.Columns a toSite s := ⟨r.value,p.value,rows_length l st⟩
  (⟨c,r.work.seq (p.work.seq (StochasticGames.CompilerRun.Work.one 0))⟩ : Run (RankRun.Columns a toSite s))

private theorem vectorBy_at {T : Type} {n : ℕ} (len : Run ℕ) (eq : len.value=n) (f : Fin n → Run T) (i : Fin n) :
    (vectorBy len eq f).value[i.val] = (f i).value :=
  (congrArg (fun v : Vector T n => v[i.val]) (vectorBy_value len eq f)).trans (by simp)

private theorem rows_at (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) (j : Fin a.targets) :
    (rows l st).value[j.val] = (gapRow l j).value.toArray := by
  exact vectorBy_at (step 0 st.tables.gains.toArray.size) st.tables.gains.size_toArray
    (fun j => do let xs ← gapRow l j; step 0 xs.toArray) j

theorem columns_correct (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    (columns l st).value.Correct := by
  constructor
  · intro i
    change (realColumn l).value[i.val] = _
    simpa only [Sparse.Layout.stored_eq] using realColumn_value l i
  · rintro ⟨j,h⟩
    rw [Sparse.Layout.stored_eq]
    apply congrArg (Prod.mk j)
    have opt : (rows l st).value[j.val][h.val]? = some ((rep l ⟨j,h⟩).value) := by
      rw [rows_at,getElem?_pos _ _ (by simp)]
      exact congrArg some (vectorBy_at (l.count j) (l.count_value j) (fun p => rep l ⟨j,p⟩) h)
    rw [getElem?_pos _ _ (by rw [rows_length]; exact h.isLt)] at opt
    exact (Option.some.inj opt).trans (rep_value l ⟨j,h⟩)

def columnSlots (L : ℕ) :=
  let r := recordLimit L
  let real := (r+1)+(3*(r+1)+r*(r+1))
  let counts := r+4
  let row := counts+3*(r+1)+r*(r+3)
  real+(1+3*(L+1)+L*(row+1))+1

theorem count_work (l : Lists a toSite s) (hs : SelectionBound a s) (j : Fin a.targets) :
    let L := Binary.lengthInput a
    (l.count j).Bound (recordLimit L+4) (indexWidth L) := by
  let L := Binary.lengthInput a
  let xs := l.cuts[j.val]
  let r := recordLimit L
  let W := indexWidth L
  have size : xs.length ≤ r+1 := (cutLength l j).symm.le.trans (Nat.succ_le_succ (Lists.group_count hs j))
  have dim := (Binary.dimensions a).1
  have w1 : a.targets.size ≤ W := (size_le_self _).trans (dim.trans (by unfold W indexWidth; omega))
  have w2 : xs.length.size ≤ W := (size_le_self _).trans (by unfold W indexWidth r at *; omega)
  have base : (l.count j).Bound (1+((xs.length+1)+1)) W :=
    bound_bind ((bound_step _ _).weaken le_rfl w1) (bound_bind ((length_bound xs).weaken le_rfl w2)
      (show (natSub (length xs).value 1).Bound 1 W by
        rw [length_value]; exact ⟨le_rfl,max_le w2 (by change 1 ≤ W; unfold W indexWidth; omega)⟩))
  exact base.weaken (show 1+(xs.length+1+1) ≤ r+4 by omega) le_rfl

theorem columns_work (l : Lists a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (st : InitializationWork.State a.types a.targets) :
    let L := Binary.lengthInput a
    (columns l st).Bound (columnSlots L) (indexWidth L) := by
  let L := Binary.lengthInput a
  let r := recordLimit L
  let W := indexWidth L
  have wide : r+L+1 ≤ W := by unfold W indexWidth r; omega
  have real : l.bids.length ≤ r := l.bid_count hs
  have nr := congrArg List.length l.bidOrder
  let n := (Sparse.realOrder (G := grid a.game) a.game toSite s).length
  change l.bids.length = n at nr
  have rs : n ≤ r := nr ▸ real
  have ln : (length l.bids).Bound (r+1) W := (length_bound _).weaken (by omega)
    ((size_le_self _).trans (by omega))
  have rb : (realColumn l).Bound ((r+1)+(3*(r+1)+r*(r+1))) W := by
    apply (vectorBy_work _ _ _ ln (show n.size ≤ W from (size_le_self _).trans (by omega))
      (fun i : Fin n => (get_bound l.bids (Fin.cast nr.symm i)).weaken
        (show _ ≤ r+1 by change i.val+1 ≤ r+1; have := i.isLt; omega)
        ((size_le_self _).trans (by change i.val ≤ W; have := i.isLt; omega)))).weaken _ le_rfl
    gcongr
  let rowLimit := r+4+3*(r+1)+r*(r+3)
  have rowsB (j : Fin a.targets) : (gapRow l j).Bound rowLimit W := by
    let groups := (Sparse.partition (G := grid a.game) a.game toSite s j).groups
    have gr : groups ≤ r := Lists.group_count hs j
    have h := vectorBy_work (l.count j) (l.count_value j) (fun h => rep l ⟨j,h⟩)
      (count_work l hs j) ((size_le_self _).trans (show groups ≤ W by omega)) (fun _ => rep_work l valid hs _)
    apply h.weaken _ le_rfl
    change r+4+(3*(groups+1)+groups*(r+3)) ≤ rowLimit
    unfold rowLimit
    rw [← Nat.add_assoc]
    exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 3 (Nat.succ_le_succ gr)) _) (Nat.mul_le_mul_right _ gr)
  have m : a.targets ≤ L := (Binary.dimensions a).1
  have dim : a.targets.size ≤ W := (size_le_self _).trans (by omega)
  have gridRows : (rows l st).Bound (1+(3*(L+1)+L*(rowLimit+1))) W := by
    apply (vectorBy_work _ _ _ ((bound_step 0 _).weaken le_rfl (Nat.zero_le W)) dim
      (fun j => bound_bind (rowsB j) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))).weaken _ le_rfl
    gcongr
  exact ⟨(Nat.add_le_add rb.1 (Nat.add_le_add_right gridRows.1 1)).trans (by
    unfold columnSlots; dsimp only [L,r,rowLimit]; omega),max_le rb.2 (max_le gridRows.2 (Nat.zero_le _))⟩

end Kintali.QuotaSweep.SelectedBuilder
