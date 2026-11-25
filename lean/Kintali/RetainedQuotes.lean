module

public import Kintali.ExactRecovery.Book
public import Kintali.QuotaSweep.QuotePartitions
public import Kintali.QuoteSearch.Algorithm
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.NodupEquivFin

/-!
# Constructing the restricted real-bid list

Enumerate only the selected optional quotes and the caps. At each
site the retained indices, together with 0 and G, give the private
group boundaries.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery.Sparse

open QuoteSearch QuotaSweep

variable {k m G : ℕ}

abbrev ListedBid (k m G : ℕ) := Fin k × Fin m × Quote G

def selectedOptional (s : Selection (k * m)) (i : Fin k) (j : Fin m) (z : Quote G) : Bool :=
  decide (z.val < G ∧ z.val ∈ s[finProdFinEquiv (i, j)])

def parseQuotes (G : ℕ) (indices : List ℕ) : List (Quote G) :=
  indices.filterMap fun j => if h : j < G then some ⟨j, Nat.lt_succ_of_lt h⟩ else none

theorem mem_parseQuotes (indices : List ℕ) (z : Quote G) :
    z ∈ parseQuotes G indices ↔ z.val < G ∧ z.val ∈ indices := by
  unfold parseQuotes
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hg : i < G
    · simp [hg] at h
      subst z
      exact ⟨hg, hi⟩
    · simp [hg] at h
  · rintro ⟨hz, hm⟩
    refine ⟨z.val, hm, ?_⟩
    simp [hz]

variable (g : Game (Fin k) (Fin m)) (redirect : Fin k → Fin m)

/-- The eligible cap is always included. Repeated optional indices
are deduplicated by the finset of quotes. -/
def realAt (s : Selection (k * m)) (p : Fin k × Fin m) : Finset (Quote G) :=
  (insert (cap G) ((parseQuotes G s[finProdFinEquiv p]).toFinset)).filter
    fun z => 0 < g.gain p.2 ∧ Holdings.quoteCost g p.1 p.2 z ≤ Holdings.outsideCost g redirect p.1

theorem mem_realAt (s : Selection (k * m)) (i : Fin k) (j : Fin m) (z : Quote G) :
    z ∈ realAt g redirect s (i, j) ↔
      Holdings.Eligible g redirect i j z ∧ (z = cap G ∨ selectedOptional s i j z = true) := by
  simp [realAt, Holdings.Eligible, mem_parseQuotes, selectedOptional, and_comm]

def realBids (s : Selection (k * m)) : Finset (ListedBid k m G) :=
  Finset.univ.biUnion fun p : Fin k × Fin m => (realAt g redirect s p).image (fun z => (p.1, p.2, z))

theorem mem_realBids (s : Selection (k * m)) (i : Fin k) (j : Fin m) (z : Quote G) :
    (i, j, z) ∈ realBids g redirect s ↔ z ∈ realAt g redirect s (i, j) := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h
    obtain ⟨q, hq, equal⟩ := Finset.mem_image.mp hp
    have hi : p.1 = i := congrArg Prod.fst equal
    have hj : p.2 = j := congrArg (fun b => b.2.1) equal
    have hz : q = z := congrArg (fun b => b.2.2) equal
    have hs : p = (i, j) := Prod.ext hi hj
    simpa [hs, hz] using hq
  · intro h
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _, Finset.mem_image.mpr ⟨z, h, rfl⟩⟩

theorem realAt_card_le (s : Selection (k * m)) (p : Fin k × Fin m) :
    (realAt g redirect s p : Finset (Quote G)).card ≤ s[finProdFinEquiv p].length + 1 := by
  have h : (parseQuotes G s[finProdFinEquiv p]).length ≤ s[finProdFinEquiv p].length :=
    List.length_filterMap_le _ _
  exact ((Finset.card_filter_le _ _).trans (Finset.card_insert_le _ _)).trans
    (Nat.add_le_add_right ((List.toFinset_card_le _).trans h) 1)

def siteCuts (s : Selection (k * m)) (j : Fin m) : Finset ℕ :=
  insert 0 (insert G (((realBids g redirect s : Finset (ListedBid k m G)).filter
    fun b => b.2.1 = j).image fun b => b.2.2.val))

theorem siteCuts_le (s : Selection (k * m)) (j : Fin m) {z : ℕ}
    (h : z ∈ siteCuts (G := G) g redirect s j) : z ≤ G := by
  simp only [siteCuts, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at h
  rcases h with rfl | rfl | ⟨b, _, rfl⟩
  · omega
  · rfl
  · exact Nat.le_of_lt_succ b.2.2.isLt

def partition (s : Selection (k * m)) (j : Fin m) : QuotePartition G :=
  QuotePartition.ofCuts (siteCuts g redirect s j) (by simp [siteCuts]) (by simp [siteCuts])
    (fun _ hz => siteCuts_le g redirect s j hz)

theorem retained_at_boundary (s : Selection (k * m)) (i : Fin k) (j : Fin m) (z : Quote G)
    (h : (i, j, z) ∈ realBids g redirect s) :
    ∃ q, (partition (G := G) g redirect s j).cut q = z.val := by
  apply QuotePartition.exists_cut_of_mem
  simp only [siteCuts, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
  exact Or.inr (Or.inr ⟨(i,j,z), ⟨h,rfl⟩,rfl⟩)

section Indexing

def listedLE (a b : ListedBid k m G) : Prop := Encodable.encode a ≤ Encodable.encode b

instance : DecidableRel (listedLE (k := k) (m := m) (G := G)) :=
  fun a b => inferInstanceAs (Decidable (Encodable.encode a ≤ Encodable.encode b))

instance : IsTrans (ListedBid k m G) listedLE :=
  ⟨fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂⟩

instance : Std.Antisymm (listedLE (k := k) (m := m) (G := G)) :=
  ⟨fun _ _ h₁ h₂ => Encodable.encode_injective (Nat.le_antisymm h₁ h₂)⟩

instance : Std.Total (listedLE (k := k) (m := m) (G := G)) :=
  ⟨fun a b => Nat.le_total (Encodable.encode a) (Encodable.encode b)⟩

def realOrder (s : Selection (k * m)) : List (ListedBid k m G) :=
  (realBids g redirect s).sort listedLE

theorem realOrder_length (s : Selection (k * m)) :
    (realOrder (G := G) g redirect s).length = (realBids g redirect s : Finset (ListedBid k m G)).card := by
  simp [realOrder]

theorem mem_realOrder (s : Selection (k * m)) (b : ListedBid k m G) :
    b ∈ realOrder g redirect s ↔ b ∈ realBids g redirect s := by
  simp [realOrder]

def realEmbedding (s : Selection (k * m)) :
    Fin (realOrder (G := G) g redirect s).length ↪ ListedBid k m G where
  toFun := (realOrder g redirect s).get
  inj' := List.Nodup.injective_get (by simp [realOrder])

theorem realEmbedding_range (s : Selection (k * m)) (b : ListedBid k m G) :
    (∃ i, realEmbedding g redirect s i = b) ↔ b ∈ realBids g redirect s := by
  rw [← mem_realOrder g redirect s]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem ..
  · intro h
    obtain ⟨i, hLength, hi⟩ := List.getElem_of_mem h
    exact ⟨⟨i,hLength⟩, hi⟩

end Indexing
end Kintali.ExactRecovery.Sparse
