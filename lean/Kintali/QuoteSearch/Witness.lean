module

public import Kintali.ContactComparison

/-!
# Adding the next quotes to the fixed witness

Kintali's Lemma 6 compares the two budget contacts using the full
contact's positive support. To recover a small residual directly from
the trial holdings, include the next eligible optional quote at the
full coverage for each buyer–site pair. A permanent cap quote is
already retained and needs no place in this extra witness.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.QuoteSearch

variable {Pair Record : Type*} [Fintype Pair] [DecidableEq Record]

def extraQuotes (next : Pair → Option Record) : Finset Record :=
  Finset.univ.biUnion fun p => (next p).toFinset

theorem mem_extraQuotes {next : Pair → Option Record} {e : Record} :
    e ∈ extraQuotes next ↔ ∃ p, next p = some e := by
  simp [extraQuotes]

theorem extraQuotes_card (next : Pair → Option Record) :
    (extraQuotes next).card ≤ Fintype.card Pair := by
  calc
    _ ≤ ∑ p : Pair, ((next p).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Pair, 1 := Finset.sum_le_sum (fun p _ => by cases next p <;> simp)
    _ = _ := by simp

theorem extendedWitness_card (support : Finset Record) (next : Pair → Option Record) :
    (support ∪ extraQuotes next).card ≤ support.card + Fintype.card Pair :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (extraQuotes_card next) _)

variable {Vertex Site : Type*}
variable [DecidableEq Vertex] [Fintype Vertex] [Fintype Record] [Fintype Site]
variable {M : Market Vertex Record}

/-- Either the enlarged witness has an omitted blocker, or the
coverages agree and the trial has no blocking next optional quote
at that coverage. The latter is the input to relaxed recovery. -/
theorem contact_and_next_or_blocker
    {restricted full support : Finset Record} {trial target : Record → ℚ}
    {tTrial tFull σ : ℚ} {isSite : Vertex → Bool} {rate mass : Vertex → ℚ}
    {outside : Site → Finset Record}
    (next : (Site → ℚ) → Pair → Option Record)
    (hBipartite : ∀ e, (M.ends e).card = 2 → (∑ v ∈ M.ends e, Market.side isSite v) = 0)
    (hRate : ∀ v, 0 ≤ rate v) (hσ : 0 < σ)
    (hOutside : ∀ j e, e ∈ outside j → ∃ v, isSite v = false ∧ M.ends e = {v})
    (hTrial : M.StableOn restricted (Market.pressureQuota isSite rate mass tTrial) trial)
    (hFull : M.StableOn full (Market.pressureQuota isSite rate mass tFull) target)
    (hSub : restricted ⊆ full) (hSupport : support ⊆ full)
    (hHold : ∀ e, (M.ends e).card = 2 → 0 < target e → e ∈ restricted ∪ support)
    (hNextInFull : ∀ p e, next (Market.coverage outside σ target) p = some e → e ∈ full)
    (hBudget : (∑ j, Market.coverage outside σ trial j) = ∑ j, Market.coverage outside σ target j) :
    (Market.coverage outside σ trial = Market.coverage outside σ target ∧
      ∀ p e, next (Market.coverage outside σ trial) p = some e → ¬M.Blocks trial e) ∨
      ∃ e ∈ support ∪ extraQuotes (next (Market.coverage outside σ target)),
        e ∉ restricted ∧ M.Blocks trial e := by
  classical
  let witness := support ∪ extraQuotes (next (Market.coverage outside σ target))
  have hWitness : witness ⊆ full := by
    intro e he
    rcases Finset.mem_union.mp he with hs | hn
    · exact hSupport hs
    · obtain ⟨p, hp⟩ := mem_extraQuotes.mp hn
      exact hNextInFull p e hp
  have hHolds : ∀ e, (M.ends e).card = 2 → 0 < target e → e ∈ restricted ∪ witness := by
    intro e hEnds hPos
    rcases Finset.mem_union.mp (hHold e hEnds hPos) with hr | hsup
    · exact Finset.mem_union_left _ hr
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hsup)
  by_cases hb : ∃ e ∈ witness, e ∉ restricted ∧ M.Blocks trial e
  · exact Or.inr hb
  · have hEqual :=
      (Market.contact_eq_or_omitted_blocker hBipartite hRate hσ hOutside hTrial hFull hSub
        hWitness hHolds hBudget).resolve_right hb
    refine Or.inl ⟨hEqual, ?_⟩
    intro p e he
    by_cases hr : e ∈ restricted
    · exact hTrial.stable e hr
    · rw [hEqual] at he
      have nh := mem_extraQuotes.mpr ⟨p, he⟩
      exact fun hblock => hb ⟨e, Finset.mem_union_right _ nh, hr, hblock⟩

end Kintali.QuoteSearch
