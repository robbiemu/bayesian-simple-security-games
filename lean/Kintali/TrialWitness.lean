module

public import Kintali.TrialContactView

open scoped BigOperators
@[expose] public section

namespace Kintali.MarketTrial
open ExactRecovery ExactRecovery.Expanded QuotaSweep QuoteSearch

variable {k m : ℕ} (g : Game (Fin k) (Fin m))

def recordCodes (r : ExpandedRecord g) : Finset (BidIndex (k * m)) :=
  match r with
  | .inl (.inl (i, j, z)) => {(finProdFinEquiv (i, j), z.val)}
  | _ => ∅

theorem extended_optional (hm : 0 < m) (F : FullContact g hm) {r : ExpandedRecord g}
    (hr : r ∈ extended g (redirect g hm) (privateScale g) F.allocation) :
    ∃ (i : Fin k) (j : Fin m) (z : Fin (grid g)), r = bid (realBid i j z.castSucc) ∧
      Holdings.Eligible g (redirect g hm) i j z.castSucc := by
  have asOptional (i : Fin k) (j : Fin m) (z : Quote (grid g))
      (hcap : z ≠ cap (grid g)) (hel : Holdings.Eligible g (redirect g hm) i j z)
      (eq : r = bid (realBid i j z)) :
      ∃ (i : Fin k) (j : Fin m) (a : Fin (grid g)), r = bid (realBid i j a.castSucc) ∧
        Holdings.Eligible g (redirect g hm) i j a.castSucc := by
    have hz : z.val < grid g := by
      by_contra! hle
      apply hcap
      exact Fin.ext (by have h := z.isLt; simp [cap]; omega)
    exact ⟨i, j, ⟨z.val, hz⟩, eq, hel⟩
  rcases Finset.mem_union.mp hr with hs | hn
  · obtain ⟨i, j, z, eq, hcap, _⟩ := mem_supporting.mp hs
    have hr := supporting_subset F.stable hs
    rw [eq] at hr
    let B := book g Fin.val Fin.val (redirect g hm) (allQuotes (G := grid g))
    exact asOptional i j z hcap ((retained_real ..).mp (B.mem_retainedRecords.mp hr)).1 eq
  · obtain ⟨⟨i,j⟩, hq⟩ := mem_extraQuotes.mp hn
    obtain ⟨_, permanent, hel, eq⟩ := (nextOptional_spec ..).mp hq
    exact asOptional i j _ permanent hel eq.symm

def witness (hm : 0 < m) (F : FullContact g hm) : Finset (BidIndex (k * m)) :=
  (extended g (redirect g hm) (privateScale g) F.allocation).biUnion (recordCodes g)

theorem witness_card (hm : 0 < m) (F : FullContact g hm) : (witness g hm F).card ≤ witnessBound g := by
  let ww := extended g (redirect g hm) (privateScale g) F.allocation
  calc
    _ ≤ ∑ r ∈ ww, (recordCodes g r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ ww, 1 := Finset.sum_le_sum (fun r _ => by
      rcases r with (⟨i,j,z⟩ | q) | b <;> simp [recordCodes])
    _ = ww.card := by simp
    _ ≤ _ := by
      have h := extended_card_active F.stable
      simpa [ww, witnessBound, show Expanded.activeSites g = BudgetContact.activeSites g from rfl,
        BudgetContact.activeSites_card] using h

theorem witness_eligible (hm : 0 < m) (F : FullContact g hm) (valid : g.Valid)
    {w : BidIndex (k * m)} (hw : w ∈ witness g hm F) :
    w.2 < (eligible g hm)[w.1] := by
  obtain ⟨r, hr, hw'⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨i,j,z,rfl,hel⟩ := extended_optional g hm F hr
  have he : w = (finProdFinEquiv (i,j), z.val) := by
    simpa [recordCodes, bid, realBid] using hw'
  subst w
  exact (optionalEligible g hm valid i j z).mp hel

end Kintali.MarketTrial
