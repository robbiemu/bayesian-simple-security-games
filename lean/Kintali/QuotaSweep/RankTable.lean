module

public import Kintali.QuotaSweep.Run

/-! # Materialized ordinal ranks for a sparse book -/

@[expose] public section

namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E)

abbrev RankTable (B S E : Type*) := List (Vertex B S × List (Record B S E × ℕ))

def rankVertices : List (Vertex B S) :=
  K.records.filterMap fun
    | .inl _ => none
    | .inr v => some v

theorem mem_rankVertices (v : Vertex B S) : v ∈ K.rankVertices :=
  List.mem_filterMap.mpr ⟨.inr v, K.complete _, rfl⟩

@[noinline] def rankTable : RankTable B S E :=
  K.rankVertices.map fun v => (v, K.records.map fun e => (e, K.market.rank v e))

@[noinline] def readRanks (table : RankTable B S E) (v : Vertex B S) (e : Record B S E) : ℕ :=
  (((table.lookup v).getD []).lookup e).getD 0

@[simp] theorem readRanks_eq : readRanks K.rankTable = K.market.rank := by
  funext v e
  unfold readRanks rankTable
  rw [List.lookup_graph _ (K.mem_rankVertices v), Option.getD_some,
    List.lookup_graph _ (K.complete e), Option.getD_some]

@[noinline] def withRanks (table : RankTable B S E) (h : readRanks table = K.market.rank) : Book B S E :=
  { K with
    market :=
      { K.market with
        rank := readRanks table
        rank_injective := by rw [h]; exact K.market.rank_injective
        slack_last := by rw [h]; exact K.market.slack_last } }

def cacheRanks : Book B S E := K.withRanks K.rankTable K.readRanks_eq

@[simp] theorem cacheRanks_eq : K.cacheRanks = K := by
  unfold cacheRanks withRanks
  cases K with
  | mk M buyer site eb eo ev recs complete retained =>
    have ranks := (readRanks_eq
      (Book.mk M buyer site eb eo ev recs complete retained))
    cases M with
    | mk ends rank deg inj last =>
      simp only [ranks]

end Kintali.QuotaSweep.Book
