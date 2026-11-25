module

public import Kintali.QuotaSweep.BuilderCuts
public import Kintali.TrialWork.ListBuild

/-! # Finite buyer, bid, site, record and vertex orders from the selected labels -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def sumList {A B : Type} (xs : List A) (ys : List B) : Run (List (A ⊕ B)) := do
  let x ← StochasticGames.CompilerRun.mapM (fun a => step 0 (Sum.inl a)) xs
  let y ← StochasticGames.CompilerRun.mapM (fun b => step 0 (Sum.inr b)) ys
  append x y

@[simp] theorem sumList_value {A B : Type} (xs : List A) (ys : List B) :
    (sumList xs ys).value = xs.map Sum.inl ++ ys.map Sum.inr := by simp [sumList]

theorem sumList_complete {A B : Type} (xs : List A) (ys : List B)
    (x : ∀ a, a ∈ xs) (y : ∀ b, b ∈ ys) : ∀ i, i ∈ (sumList xs ys).value := by
  rintro (a|b) <;> simp [x,y]

theorem sumList_unique {A B : Type} (xs : List A) (ys : List B)
    (x : xs.Nodup) (y : ys.Nodup) : (sumList xs ys).value.Nodup := by
  rw [sumList_value,List.nodup_append]
  refine ⟨x.map Sum.inl_injective,y.map Sum.inr_injective,?_⟩
  intro i hi
  rcases List.mem_map.mp hi with ⟨a,_,rfl⟩
  simp

theorem sumList_work {A B : Type} (xs : List A) (ys : List B) (w : ℕ) :
    (sumList xs ys).Bound (4*(xs.length+ys.length+1)) w := by
  let x := StochasticGames.CompilerRun.mapM (fun a : A => step 0 (Sum.inl a : A⊕B)) xs
  let y := StochasticGames.CompilerRun.mapM (fun b : B => step 0 (Sum.inr b : A⊕B)) ys
  have hx := mapM_bound _ xs 1 w (fun a _ => (bound_step 0 (Sum.inl a : A⊕B)).weaken le_rfl (Nat.zero_le _))
  have hy := mapM_bound _ ys 1 w (fun b _ => (bound_step 0 (Sum.inr b : A⊕B)).weaken le_rfl (Nat.zero_le _))
  have rest := append_bound x.value y.value w
  have size : x.value.length = xs.length := by simp [x]
  exact (bound_bind hx (bound_bind hy rest)).weaken (by rw [size]; omega) le_rfl

def rights {A B : Type} : List (A ⊕ B) → Run (List B)
  | [] => step 0 []
  | e::rest => do
    let r ← rights rest
    step 0 (match e with | .inl _ => r | .inr b => b::r)

@[simp] theorem rights_value {A B : Type} (xs : List (A ⊕ B)) :
    (rights xs).value = xs.filterMap Sum.getRight? := by
  induction xs with
  | nil => rfl
  | cons e xs ih => cases e <;> simp [rights,ih,List.filterMap_cons,Sum.getRight?]

theorem rights_work {A B : Type} (xs : List (A ⊕ B)) (w : ℕ) :
    (rights xs).Bound (xs.length+1) w := by
  induction xs with
  | nil => exact ⟨le_rfl,Nat.zero_le _⟩
  | cons e xs ih => exact bound_bind ih ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))

abbrev Buyers (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :=
  Sparse.B (Fin a.types) (StoredLookup.SelectedGroups a toSite s)
abbrev Bids (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :=
  Sparse.E (StoredLookup.SelectedReals a toSite s) (StoredLookup.SelectedGroups a toSite s)

structure Orders (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) where
  sites : List (Fin a.targets)
  buyers : List (Buyers a toSite s)
  bids : List (Bids a toSite s)
  records : List (StoredLookup.SelectedRecord a toSite s)
  vertices : List (RankRun.SelectedVertex a toSite s)

def wordCompare (x y : ℕ) : Run Ordering := ⟨compare x y,⟨2,max x.size y.size⟩⟩

def compareRecord (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (x y : StoredLookup.SelectedRecord a toSite s) : Run Ordering := do
  let n ← StoredLookup.recordKey (Sparse.partition (G := grid a.game) a.game toSite s) x
  let m ← StoredLookup.recordKey (Sparse.partition (G := grid a.game) a.game toSite s) y
  wordCompare n m

theorem compareRecord_work (hs : SelectionBound a s) (x y : StoredLookup.SelectedRecord a toSite s) :
    (compareRecord a toSite s x y).Bound 26 (StoredLookup.width (Binary.lengthInput a)) := by
  have id := StoredLookup.selected_key_bound a toSite s hs
  unfold compareRecord
  apply bound_bind (l := 14) (id.work x)
  apply bound_bind (l := 2) (id.work y)
  exact ⟨le_rfl,max_le (id.size x) (id.size y)⟩

def makeOrders (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    Run (Orders a toSite s) := do
  let rs ← l.reals
  let gs ← l.groups
  let is ← number (step 0 st.tables.priors.toArray.size) st.tables.priors.size_toArray
  let js ← number (step 0 st.tables.gains.toArray.size) st.tables.gains.size_toArray
  let bs ← sumList is gs
  let es ← sumList rs gs
  let vs ← sumList bs js
  let all ← sumList es vs
  let sorted ← TrialWork.ListBuild.sortedSet (compareRecord a toSite s) all
  let verts ← rights sorted
  step 0 ⟨js,bs,es,sorted,verts⟩

theorem orders_sites (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    (makeOrders l st).value.sites = List.finRange a.targets := by simp [makeOrders]

theorem orders_buyers (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    (makeOrders l st).value.buyers = (sumList (List.finRange a.types) l.groups.value).value := by simp [makeOrders]

theorem orders_bids (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    (makeOrders l st).value.bids = (sumList l.reals.value l.groups.value).value := by simp [makeOrders]

theorem numbersK (st : InitializationWork.State a.types a.targets) :
    (number (step 0 st.tables.priors.toArray.size) st.tables.priors.size_toArray).value = List.finRange a.types :=
  number_value _ _

theorem numbersM (st : InitializationWork.State a.types a.targets) :
    (number (step 0 st.tables.gains.toArray.size) st.tables.gains.size_toArray).value = List.finRange a.targets :=
  number_value _ _

private theorem recordsOf {I J A H : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype H]
    [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
    [Encodable I] [Encodable J] [Encodable A] [Encodable H] {G : ℕ} (g : Game I J)
    (bi : I → ℕ) (sj : J → ℕ) (l : Sparse.Layout I J G A H) :
    let _ : LinearOrder (Sparse.R I J A H) := LinearOrder.lift' Encodable.encode Encodable.encode_injective
    (Sparse.book g bi sj l).records = (Finset.univ : Finset (Sparse.R I J A H)).sort := rfl

private theorem sortedAll {T : Type} [Fintype T] [Encodable T]
    (comparison : T → T → Run Ordering)
    (correct : ∀ x y, (comparison x y).value=compare (Encodable.encode x) (Encodable.encode y))
    (xs : List T) (complete : ∀ x, x ∈ xs) :
    let _ : LinearOrder T := LinearOrder.lift' Encodable.encode Encodable.encode_injective
    (TrialWork.ListBuild.sortedSet comparison xs).value = (Finset.univ : Finset T).sort := by
  let : LinearOrder T := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  have eq (x y : T) : (comparison x y).value = compare x y := correct x y
  change (TrialWork.ListBuild.sortedSet comparison xs).value = Finset.univ.sort (fun x y : T => x ≤ y)
  apply (TrialWork.ListBuild.sortedSet_value comparison eq xs).trans
  apply congrArg (fun set : Finset T => set.sort (fun x y : T => x ≤ y))
  exact Finset.eq_univ_of_forall (fun e => List.mem_toFinset.mpr (complete e))

theorem orders_records (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    (makeOrders l st).value.records = (Sparse.book a.game Fin.val Fin.val
      ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored)).records := by
  let buyers := (sumList (List.finRange a.types) l.groups.value).value
  let bids := (sumList l.reals.value l.groups.value).value
  let vertices := (sumList buyers (List.finRange a.targets)).value
  let all := (sumList bids vertices).value
  have hbuy := sumList_complete (List.finRange a.types) l.groups.value (List.mem_finRange ·) l.groups_complete
  have hbid := sumList_complete l.reals.value l.groups.value (fun i => by simp) l.groups_complete
  have hvertices := sumList_complete buyers (List.finRange a.targets) hbuy (List.mem_finRange ·)
  have cover := sumList_complete bids vertices hbid hvertices
  have cmp (x y : StoredLookup.SelectedRecord a toSite s) :
      (compareRecord a toSite s x y).value = compare (Encodable.encode x) (Encodable.encode y) := by
    simp only [compareRecord,Run.bind_value,StoredLookup.recordKey_value]; rfl
  have data := sortedAll (compareRecord a toSite s) cmp all cover
  have left : (makeOrders l st).value.records = (TrialWork.ListBuild.sortedSet (compareRecord a toSite s) all).value := by
    simp only [makeOrders,Run.bind_value,step_value,numbersK st,numbersM st]
    rfl
  exact left.trans (data.trans (recordsOf ..).symm)

theorem orders_vertices (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets) :
    (makeOrders l st).value.vertices = (Sparse.book a.game Fin.val Fin.val
      ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored)).rankVertices := by
  have eq : (makeOrders l st).value.vertices = ((makeOrders l st).value.records.filterMap Sum.getRight?) := by
    simp only [makeOrders,Run.bind_value,step_value,rights_value]
  rw [eq,orders_records]
  unfold Book.rankVertices
  congr 1
  funext e; cases e <;> rfl

end Kintali.QuotaSweep.SelectedBuilder
