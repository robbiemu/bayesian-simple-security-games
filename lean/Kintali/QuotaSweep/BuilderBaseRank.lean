module

public import Kintali.QuotaSweep.BuilderOrderSpec
import all Kintali.QuotaSweep.KeyTable

/-! Construct an ordinal market from the supplied records and key callback.
The subsequent materialized rank table replaces this first lookup closure. -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder
open Kintali.ExactRecovery

variable {I J A H : Type} {G : ℕ} [Fintype I] [Fintype J] [Fintype A] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
variable [Encodable I] [Encodable J]

@[noinline, nospecialize] def listRank {V R : Type} (rs : List R) (make : V → R → Expanded.Key)
    (v : V) (e : R) : ℕ := rs.countP fun f => decide (make v f < make v e)

/-- Opposite endpoint tags are distinct by construction. The list-backed
set therefore needs no equality dictionary to insert its two records. -/
def directEnds (l : Sparse.Layout I J G A H) : Sparse.R I J A H → Finset (Sparse.V I J H)
  | .inl e => ⟨([Sum.inl (l.buyer e),Sum.inr (l.site e)] : List (Sparse.V I J H)),by simp⟩
  | .inr v => ⟨[v],by simp⟩

omit [Fintype I] [Fintype J] [Fintype A] [Fintype H] [DecidableEq A] [Encodable I] [Encodable J] in
theorem directEnds_eq (l : Sparse.Layout I J G A H) : directEnds l = l.ends := by
  funext e
  ext v
  cases e <;> simp [directEnds,Sparse.Layout.ends]

def listMarket (g : Game I J) (bi : I → ℕ) (sj : J → ℕ) (l : Sparse.Layout I J G A H)
    (rs : List (Sparse.R I J A H)) (unique : rs.Nodup) (complete : ∀ r, r ∈ rs)
    (make : Sparse.V I J H → Sparse.R I J A H → Expanded.Key)
    (correct : ∀ v e, make v e = Expanded.key g bi sj (l.embedVertex v) (l.embedRecord e)) :
    Market (Sparse.V I J H) (Sparse.R I J A H) :=
  let m := Sparse.market g bi sj l
  let ranking : listRank rs make = m.rank := by
    funext v e
    simpa only [listRank,correct,m,Sparse.market,Sparse.rank] using
      (Sparse.count_lt rs unique complete (fun f => Expanded.key g bi sj (l.embedVertex v) (l.embedRecord f)) e)
  { ends := directEnds l, rank := listRank rs make, degree := by rw [directEnds_eq]; exact m.degree
    rank_injective := by rw [ranking,directEnds_eq]; exact m.rank_injective
    slack_last := by rw [ranking,directEnds_eq]; exact m.slack_last }

theorem listMarket_eq (g : Game I J) (bi : I → ℕ) (sj : J → ℕ) (l : Sparse.Layout I J G A H)
    (rs : List (Sparse.R I J A H)) (unique : rs.Nodup) (complete : ∀ r, r ∈ rs)
    (make : Sparse.V I J H → Sparse.R I J A H → Expanded.Key)
    (correct : ∀ v e, make v e = Expanded.key g bi sj (l.embedVertex v) (l.embedRecord e)) :
    listMarket g bi sj l rs unique complete make correct = Sparse.market g bi sj l := by
  have equal : listRank rs make = Sparse.rank g bi sj l := by
    funext v e
    simpa only [listRank,correct,Sparse.rank] using
      (Sparse.count_lt rs unique complete (fun f => Expanded.key g bi sj (l.embedVertex v) (l.embedRecord f)) e)
  unfold listMarket Sparse.market
  simp only [equal,directEnds_eq]


end Kintali.QuotaSweep.SelectedBuilder
