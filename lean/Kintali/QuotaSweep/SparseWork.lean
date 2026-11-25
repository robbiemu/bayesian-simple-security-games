module

public import Kintali.QuotaSweep.SparseContact
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Sparse contact operation and table bounds

The counter charges finite table scans, graph walks and exact scalar operations.
It treats a primitive rank or endpoint read at its supplied upper charge.
The concrete rank table uses a pair of association-list lookups. Preparing
the ordinal row for every vertex costs at most one key comparison per sparse
record, for every row entry. No elementary grid record enters these counts.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E] (K : Book B S E)

private theorem length_of_complete {T : Type*} [DecidableEq T] [Fintype T] (l : List T)
    (h : ∀ t, t ∈ l) : Fintype.card T ≤ l.length := by
  have heq : l.toFinset = Finset.univ := by ext t; simp [h t]
  simpa only [heq,Finset.card_univ] using l.toFinset_card_le

theorem vertex_count_le [Fintype B] [Fintype S] :
    Fintype.card (Vertex B S) ≤ K.records.length :=
  (length_of_complete K.vertexOrder K.mem_vertexOrder).trans K.vertexOrder_length

theorem record_count_le [Fintype B] [Fintype S] [Fintype E] :
    Fintype.card (Record B S E) ≤ K.records.length := length_of_complete _ K.complete

/-- The lookup cost is the number of index equality tests across the two
materialized lists. Every rank-table row stores exactly one natural per record. -/
def measuredRankRead (table : RankTable B S E) (v : Vertex B S) (r : Record B S E) : ℕ × ℕ :=
  let row := Work.search v [] table
  let value := Work.search r 0 row.1
  (value.1,row.2+value.2)

theorem rankTable_rows : K.rankTable.length = K.rankVertices.length := by simp [rankTable]

theorem rankTable_width (v : Vertex B S) :
    (Work.search v [] K.rankTable).1.length = K.records.length := by
  let row := fun u : Vertex B S => K.records.map fun r => (r,K.market.rank u r)
  change (Work.search v [] (K.rankVertices.map fun u => (u,row u))).1.length = _
  have hr := Work.read_tabulate (fun u => (row u,0)) K.rankVertices [] (K.mem_rankVertices v)
  rw [Work.tabulate_value] at hr
  rw [hr]
  simp [row]

theorem measuredRankRead_value (v : Vertex B S) (e : Record B S E) :
    (measuredRankRead K.rankTable v e).1 = K.market.rank v e := by
  let row := fun u : Vertex B S => K.records.map fun r => (r,K.market.rank u r)
  have hr := Work.read_tabulate (fun u => (row u,0)) K.rankVertices [] (K.mem_rankVertices v)
  rw [Work.tabulate_value] at hr
  have hq := Work.read_tabulate (fun r => (K.market.rank v r,0)) K.records 0 (K.complete e)
  rw [Work.tabulate_value] at hq
  change (Work.search e 0 (Work.search v [] (K.rankVertices.map fun u => (u,row u))).1).1 = _
  rw [hr]
  exact hq

theorem measuredRankRead_work (v : Vertex B S) (e : Record B S E) :
    (measuredRankRead K.rankTable v e).2 ≤ 2*K.records.length := by
  have hs := Work.search_work v [] K.rankTable
  rw [K.rankTable_rows] at hs
  have hlen : K.rankVertices.length ≤ K.records.length := List.length_filterMap_le ..
  have hr := Work.search_work e 0 (Work.search v [] K.rankTable).1
  rw [K.rankTable_width] at hr
  change (Work.search v [] K.rankTable).2+(Work.search e 0 (Work.search v [] K.rankTable).1).2 ≤ _
  omega

/-- The cache stores one rank integer for each pair of a slack vertex
and a record. -/
theorem rankTable_cells :
    (K.rankTable.map (fun row => row.2.length)).sum = K.rankVertices.length*K.records.length := by
  unfold rankTable
  simp only [List.map_map,Function.comp_def,List.length_map]
  induction K.rankVertices with
  | nil => simp
  | cons v vs _ => simp [Nat.add_mul,Nat.add_comm]

/-- A bound on the live explicit table entries of a stage. Counting the
old, endpoint and crossing allocations simultaneously also covers the budget
branch. The rank matrix sits alongside these linear-sized tables. -/
theorem materialized_entries [Fintype B] [Fintype S] (unit : ℕ) (P : Parameters B S)
    (z : Stored B S E) (hz : z.entries.length ≤ K.records.length) :
    let r := K.records.length
    let g := (K.graph unit z.read P.rate).1
    let f := (K.frame unit P z).1
    let bs := (K.releaseTable unit z.read).1
    let arcs := (K.edges unit g.markers).1
    let candidates := (Work.tabulate (candidate g z.read) K.buyerOrder).1
    let finish := (K.applyFrame f z f.duration).1
    let stop := (K.applyFrame f z (K.budgetTime P z.view)).1
    (K.rankTable.map (fun row => row.2.length)).sum + K.rankTable.length + bs.length +
      g.markers.length + arcs.length + g.rates.length + candidates.length + f.slopes.length +
      z.entries.length + finish.entries.length + stop.entries.length ≤ r*r+10*r := by
  have vr : K.rankVertices.length ≤ K.records.length := List.length_filterMap_le ..
  have mapped := K.graph_table_lengths unit z.read P.rate
  simp only [rankTable_cells,rankTable_rows,releaseTable,edges,Work.tabulate_length,
    mapped.1,mapped.2,frame_length,applyFrame_length]
  have hmul := Nat.mul_le_mul_right K.records.length vr
  have bv := K.buyerOrder_length
  have vv := K.vertexOrder_length
  omega

private theorem small_stage {n r : ℕ} (hn : n ≤ r) :
    stageLimit n r (r+8*(r+1)+1)+1 ≤ 250*(r+2)^4 := by
  have raise : stageLimit n r (r+8*(r+1)+1) ≤ stageLimit r r (r+8*(r+1)+1) := by
    unfold stageLimit frameLimit graphLimit
    gcongr
  apply (Nat.succ_le_succ raise).trans
  unfold stageLimit frameLimit graphLimit marksLimit buyerTableLimit proposalLimit choiceLimit comparisonCharge acceptLimit
  ring_nf
  omega

/-- With the concrete sparse-book charge, the whole run costs at most
`300*(R+2)^5` counted index/scalar operations after the book is prepared. -/
theorem contactWork_polynomial [Fintype B] [Fintype S] [Fintype E] (P : Parameters B S) :
    (K.contactWork P (8*(K.records.length+1))).2 ≤ 300*(K.records.length+2)^5 := by
  let r := K.records.length
  have h := K.contactWork_bound P (8*(r+1))
  have hh := small_stage K.vertex_count_le
  have hmul := Nat.mul_le_mul (Nat.succ_le_succ K.record_count_le) hh
  apply h.trans
  apply (Nat.add_le_add_left hmul _).trans
  change r*(8*(r+1)+2)+(r+1)*(250*(r+2)^4) ≤ 300*(r+2)^5
  ring_nf
  omega

end Kintali.QuotaSweep.Book

namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep

variable {I J A H : Type*} {G : ℕ}
variable [Fintype I] [Fintype J] [Fintype A] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
variable [Encodable I] [Encodable J] [Encodable A] [Encodable H]

/-- The result equals the ordinal-rank definition and counts one key
comparison for each entry of the domain. -/
def measuredOrdinal {T key : Type*} [Fintype T] [LinearOrder key] (f : T → key) (e : T) : ℕ × ℕ :=
  ∑ r, (if f r < f e then 1 else 0,1)

theorem measuredOrdinal_value {T key : Type*} [Fintype T] [LinearOrder key] (f : T → key) (e : T) :
    (measuredOrdinal f e).1 = Expanded.ordinalRank f e := by
  rw [measuredOrdinal,Prod.fst_sum,Expanded.ordinalRank,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem measuredOrdinal_comparisons {T key : Type*} [Fintype T] [LinearOrder key] (f : T → key) (e : T) :
    (measuredOrdinal f e).2 = Fintype.card T := by simp [measuredOrdinal,Prod.snd_sum]

def measuredRanks (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :=
  let K := book g bi si L
  Work.tabulate (fun v =>
    Work.tabulate (measuredOrdinal fun r => Expanded.key g bi si (L.embedVertex v) (L.embedRecord r))
      K.records) K.rankVertices

theorem measuredRanks_value (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    (measuredRanks g bi si L).1 = (book g bi si L).rankTable := by
  simp [measuredRanks,Work.tabulate_value,measuredOrdinal_value,Book.rankTable,book,market,rank]

theorem records_length (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    (book g bi si L).records.length = Fintype.card (R I J A H) := by simp [book]

/-- Includes two tabulation passes in addition to the key comparisons.
Each key is the stored real quote or private representative with four
lexicographic fields. A completed table has one row per listed slack vertex. -/
theorem measuredRanks_work (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    let r := Fintype.card (R I J A H)
    (measuredRanks g bi si L).2 ≤ r*(r*(r+1)+1) := by
  let K := book g bi si L
  let r := Fintype.card (R I J A H)
  have hsize : K.records.length = r := records_length ..
  have hr : K.rankVertices.length ≤ r := (List.length_filterMap_le ..).trans_eq hsize
  apply (Work.tabulate_work _ (r*(r+1)) _ K.rankVertices).trans (Nat.mul_le_mul_right _ hr)
  intro v
  rw [← hsize]
  apply Work.tabulate_work
  intro t
  rw [measuredOrdinal_comparisons,hsize]

section Selected

variable {k m : ℕ} (g : Game (Fin k) (Fin m)) (redirect : Fin k → Fin m) (s : QuoteSearch.Selection (k*m))

theorem selectedRun_length (σ : ℚ) :
    (selectedRun (G := G) g redirect s σ).1.entries.length =
      (book g Fin.val Fin.val (selectedLayout (G := G) g redirect s)).records.length := by
  simp [selectedRun,Book.indexedContact_eq,Book.contactWork_length]

theorem selectedRun_work (σ : ℚ) :
    let r := (book g Fin.val Fin.val (selectedLayout (G := G) g redirect s)).records.length
    (selectedRun (G := G) g redirect s σ).2 ≤ 300*(r+2)^5 := by
  simpa [selectedRun,selectedParameters,Book.indexedContact_eq] using
    (Book.contactWork_polynomial (keyedBook g Fin.val Fin.val (selectedLayout (G := G) g redirect s).stored)
      (selectedParameters g redirect s σ))

end Selected

end Kintali.ExactRecovery.Sparse
