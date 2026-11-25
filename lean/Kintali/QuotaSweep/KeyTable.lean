module

public import Kintali.QuotaSweep.RankTable
public import Kintali.ExactRecovery.Sparse

/-! # Compute each preference key once per sparse vertex and record -/

@[expose] public section
namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep

/-- Eager data argument for the ordinal count. The comparisons of stored keys
do not revisit quote costs, game fields or the layout. -/
@[noinline] def keyed {T X : Type*} (records : List T) (f : T → X) : List (T × X) :=
  records.map fun e => (e,f e)

@[noinline] def ordinals {T X : Type*} [LinearOrder X] (row : List (T × X)) : List (T × ℕ) :=
  row.map fun a => (a.1,row.countP (fun b => decide (b.2 < a.2)))

private theorem count_lt {T X : Type*} [DecidableEq T] [Fintype T] [LinearOrder X]
    (l : List T) (hn : l.Nodup) (all : ∀ t, t ∈ l) (f : T → X) (e : T) :
    l.countP (fun a => decide (f a < f e)) = Expanded.ordinalRank f e := by
  let p := fun a => decide (f a < f e)
  have hset : (l.filter p).toFinset = Finset.univ.filter (fun a => f a < f e) := by
    ext a
    simp [p,all a]
  change l.countP p = _
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hn.filter p),hset]
  rfl

theorem ordinals_keyed {T X : Type*} [DecidableEq T] [Fintype T] [LinearOrder X]
    (l : List T) (hn : l.Nodup) (all : ∀ t, t ∈ l) (f : T → X) :
    ordinals (keyed l f) = l.map (fun e => (e,Expanded.ordinalRank f e)) := by
  simp only [ordinals,keyed,List.map_map,List.countP_map,Function.comp_def]
  exact List.map_congr_left (fun e _ => congrArg (fun n => (e,n)) (count_lt l hn all f e))

variable {I J A H : Type*} {G : ℕ}
variable [Fintype I] [Fintype J] [Fintype A] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
variable [Encodable I] [Encodable J] [Encodable A] [Encodable H]

@[noinline] def keyedTable (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    Book.RankTable (B I H) J (E A H) :=
  let K := book g bi si L
  K.rankVertices.map fun v =>
    (v,ordinals (keyed K.records (fun r => Expanded.key g bi si (L.embedVertex v) (L.embedRecord r))))

theorem keyedTable_eq (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    keyedTable g bi si L = (book g bi si L).rankTable := by
  let K := book g bi si L
  have hn : K.records.Nodup := by simp [K,book]
  unfold keyedTable Book.rankTable
  apply List.map_congr_left
  intro v _
  exact congrArg (fun row => (v,row)) (ordinals_keyed K.records hn K.complete _)

def keyedBook (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    Book (B I H) J (E A H) :=
  let K := book g bi si L
  K.withRanks (keyedTable g bi si L) (by rw [keyedTable_eq]; exact K.readRanks_eq)

@[simp] theorem keyedBook_eq (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    keyedBook g bi si L = book g bi si L := by
  let K := book g bi si L
  have h (t : Book.RankTable (B I H) J (E A H)) (he : t = K.rankTable)
      (hr : Book.readRanks t = K.market.rank) : K.withRanks t hr = K := by
    subst t
    exact K.cacheRanks_eq
  exact h _ (keyedTable_eq ..) (by rw [keyedTable_eq]; exact K.readRanks_eq)

end Kintali.ExactRecovery.Sparse
