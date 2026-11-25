module

public import Kintali.FullContact
public import Kintali.RetainedQuotes
public import Kintali.ExactRecovery.QuoteOrder

/-!
# The expanded meaning of the sparse trial view

The compressed trial can read buyer and site acceptance without
enumerating the full quote grid. The finite expanded market provides
the specification used by the proofs.
-/

@[expose] public section

namespace Kintali.MarketTrial

open ExactRecovery ExactRecovery.Expanded QuotaSweep QuoteSearch

variable {k m : ℕ} {g : Game (Fin k) (Fin m)}

structure Matches (hm : 0 < m) (s : Selection (k * m)) (view : ContactView k m (grid g))
    (X : ExpandedRecord g → ℚ) : Prop where
  stable : Stable g Fin.val Fin.val (redirect g hm) (Sparse.selectedOptional s) (privateScale g)
    view.pressure X
  pressure_nonneg : 0 ≤ view.pressure
  budget : (∑ j, (holdings X).physical g (privateScale g) j) = g.resources
  coverage : view.coverage = (holdings X).physical g (privateScale g)
  joint : view.joint = (holdings X).joint (redirect g hm)
  buyer : ∀ i j (z : Fin (grid g)),
    Holdings.Eligible g (redirect g hm) i j z.castSucc →
    (view.buyerAccepts i j z.castSucc = true ↔
      (market g Fin.val Fin.val).Accepts X (.inl (.inl i)) (bid (realBid i j z.castSucc)))
  site : ∀ i j (z : Fin (grid g)),
    Holdings.Eligible g (redirect g hm) i j z.castSucc →
    (view.siteAccepts i j z.castSucc = true ↔
      (market g Fin.val Fin.val).Accepts X (.inr j) (bid (realBid i j z.castSucc)))

variable (g)

private theorem get_ofFn {A : Type*} {n : ℕ} (f : Fin n → A) (p : Fin n) :
    (Vector.ofFn f).get p = f p := by
  change (Vector.ofFn f)[p.val] = f p
  exact Vector.getElem_ofFn p.isLt

theorem eligible_at (hm : 0 < m) (i : Fin k) (j : Fin m) :
    (eligible g hm)[finProdFinEquiv (i, j)] =
      eligibleCount g (redirect g hm) (grid g) i j := by
  let p := finProdFinEquiv (i, j)
  have hp : finProdFinEquiv.symm p = (i, j) := Equiv.symm_apply_apply _ _
  change (Vector.ofFn (fun p : Fin (k * m) =>
    eligibleCount g (redirect g hm) (grid g) (finProdFinEquiv.symm p).1
      (finProdFinEquiv.symm p).2)).get p = _
  rw [get_ofFn, hp]

theorem optionalEligible (hm : 0 < m) (valid : g.Valid) (i : Fin k) (j : Fin m)
    (z : Fin (grid g)) :
    Holdings.Eligible g (redirect g hm) i j z.castSucc ↔ z.val < (eligible g hm)[finProdFinEquiv (i, j)] := by
  rw [eligible_at]
  exact eligible_iff_lt_count g (redirect g hm) (gridSize_pos g (contactTolerance g)) i j
    (valid.slope_nonneg i j) z

theorem intervals_match (hm : 0 < m) (valid : g.Valid)
    {s : Selection (k * m)} {view : ContactView k m (grid g)} {X : ExpandedRecord g → ℚ}
    (matchView : Matches hm s view X) (i : Fin k) (j : Fin m) :
    let p := finProdFinEquiv (i, j)
    let r := (blockerIntervals g hm view)[p]
    (r.lo ≤ r.hi ∧ r.hi ≤ (eligible g hm)[p]) ∧
      ∀ (z : Fin (grid g)), Holdings.Eligible g (redirect g hm) i j z.castSucc →
        (r.Contains z.val ↔ (market g Fin.val Fin.val).Blocks X (bid (realBid i j z.castSucc))) := by
  let p := finProdFinEquiv (i, j)
  let count := (eligible g hm)[p]
  have hc : count ≤ grid g := by
    change (eligible g hm)[finProdFinEquiv (i, j)] ≤ grid g
    rw [eligible_at]
    exact eligibleCount_le g (redirect g hm) (grid g) i j
  let buyer := atOptional (view.buyerAccepts i j)
  let site := atOptional (view.siteAccepts i j)
  have hb (z : ℕ) (hz : z < count) :
      buyer z = true ↔
        (market g Fin.val Fin.val).Accepts X (.inl (.inl i))
          (bid (realBid i j (Fin.castSucc ⟨z, hz.trans_le hc⟩))) := by
    unfold buyer atOptional
    simp only [dite_eq_left (hz.trans_le hc)]
    exact matchView.buyer i j ⟨z, hz.trans_le hc⟩
      ((optionalEligible g hm valid i j ⟨z, hz.trans_le hc⟩).mpr hz)
  have hs (z : ℕ) (hz : z < count) :
      site z = true ↔
        (market g Fin.val Fin.val).Accepts X (.inr j)
          (bid (realBid i j (Fin.castSucc ⟨z, hz.trans_le hc⟩))) := by
    unfold site atOptional
    simp only [dite_eq_left (hz.trans_le hc)]
    exact matchView.site i j ⟨z, hz.trans_le hc⟩
      ((optionalEligible g hm valid i j ⟨z, hz.trans_le hc⟩).mpr hz)
  have hBuyer : ∀ a b, a ≤ b → b < count → buyer b = true → buyer a = true := by
    intro a b hab hb' ha
    exact (hb a (hab.trans_lt hb')).mpr (buyer_accepts_lower (valid.slope_nonneg i j)
      (show a ≤ b from hab) ((hb b hb').mp ha))
  have hSite : ∀ a b, a ≤ b → b < count → site a = true → site b = true := by
    intro a b hab hb' ha
    exact (hs b hb').mpr (site_accepts_higher (show a ≤ b from hab) ((hs a (hab.trans_lt hb')).mp ha))
  have he : (blockerIntervals g hm view)[p] = intervalFor buyer site count := by
    have hp : finProdFinEquiv.symm p = (i, j) := Equiv.symm_apply_apply _ _
    change (Vector.ofFn (fun q : Fin (k * m) =>
      intervalFor (atOptional (view.buyerAccepts (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))
        (atOptional (view.siteAccepts (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2))
        (eligible g hm)[q])).get p = intervalFor buyer site count
    rw [get_ofFn, hp]
  change ((blockerIntervals g hm view)[p].lo ≤ (blockerIntervals g hm view)[p].hi ∧
    (blockerIntervals g hm view)[p].hi ≤ count) ∧ _
  rw [he]
  obtain ⟨h1, h2, htest⟩ := intervalFor_spec buyer site count hBuyer hSite
  refine ⟨⟨h1, h2⟩, ?_⟩
  intro z hz
  have hcount := (optionalEligible g hm valid i j z).mp hz
  rw [htest z.val hcount, hb z.val hcount, hs z.val hcount, blocks_iff_accepts]

end Kintali.MarketTrial
