module

public import Kintali.TrialWitness

/-!
# Each failed trial exposes a fixed witness bid

The trial computes its relaxed point and blockers from sparse data.
The analytical full contact certifies progress even for adaptively
chosen restrictions.
-/

@[expose] public section

namespace Kintali.MarketTrial

open ExactRecovery ExactRecovery.Expanded QuotaSweep QuoteSearch

variable {k m : ℕ} (g : Game (Fin k) (Fin m))

theorem prepare_correct (valid : g.Valid) (normal : ¬g.DirectCase)
    (getContact : Selection (k * m) → ContactView k m (grid g))
    (hContact : ∀ s, ValidSelection (4 * witnessBound g) (eligible g valid.targets) s →
      ∃ X, Matches (g := g) valid.targets s (getContact s) X) :
    (prepare g valid.targets getContact).Correct (fun a => g.IsBayesNash a.coverage a.attacks) := by
  let hm := valid.targets
  obtain ⟨F⟩ := fullContact_exists g valid normal
  refine ⟨?_, ?_, witness g hm F, witness_card g hm F, ?_⟩
  · change 0 < witnessBound g
    have h := BudgetContact.activeSites_card g
    have hp := (BudgetContact.interior_budget g normal).2
    unfold witnessBound
    omega
  · intro p
    obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective p
    change (eligible g hm)[finProdFinEquiv (i,j)] ≤ grid g
    rw [eligible_at]
    exact eligibleCount_le g (redirect g hm) (grid g) i j
  · constructor
    · intro w hw
      exact witness_eligible g hm F valid hw
    · intro s a _ ha
      exact cleared_correct g hm getContact ha
    · intro s ranges hs hReply
      change ValidSelection (4 * witnessBound g) (eligible g hm) s at hs
      change run g hm getContact s = .blocked ranges at hReply
      obtain ⟨X, hX⟩ := hContact s hs
      let view := getContact s
      let pat := pattern g hm view
      have hBad : relaxedCheck g pat view ≠ true := by
        intro hc
        simp [run, pat, view, hc] at hReply
      have hRanges : ranges = blockerIntervals g hm view := by
        have he : @Reply.blocked (k * m) (Strategy k m) ranges =
            .blocked (blockerIntervals g hm view) := by
          simpa [run, pat, view, hBad] using hReply.symm
        exact Reply.blocked.inj he
      subst ranges
      constructor
      · intro p
        obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective p
        obtain ⟨bounds, characterize⟩ := intervals_match g hm valid hX i j
        refine ⟨bounds.1, bounds.2, ?_⟩
        intro z hz hBlock
        have hSmall := hs.index (finProdFinEquiv (i,j)) z hz
        have hh : z < grid g := hSmall.trans_le (by rw [eligible_at]; exact eligibleCount_le ..)
        let q : Fin (grid g) := ⟨z,hh⟩
        have hel := (optionalEligible g hm valid i j q).mpr hSmall
        have hOrd := (characterize q hel).mp hBlock
        let K := book (G := grid g) g Fin.val Fin.val (redirect g hm) (Sparse.selectedOptional s)
        have reten : bid (realBid i j q.castSucc) ∈ K.retainedRecords := by
          apply K.mem_retainedRecords.mpr
          exact (retained_real ..).mpr ⟨hel, Or.inr (by
            change decide (z < grid g ∧ z ∈ s[finProdFinEquiv (i, j)]) = true
            exact decide_eq_true ⟨hh, hz⟩)⟩
        exact hX.stable.stable _ reten hOrd
      · have hEta := contactTolerance_pos g
        have hGrid : 0 < grid g := gridSize_pos g (contactTolerance g)
        have hσ : 0 < privateScale g := sigma_pos g hEta
        let ref := g.bestTarget hm view.coverage
        have hRef (i : Fin k) (j : Fin m) :
            g.cost i (ref i) ((holdings X).physical g (privateScale g) (ref i)) ≤
              g.cost i j ((holdings X).physical g (privateScale g) j) := by
          rw [← hX.coverage]
          exact g.bestTarget_spec hm view.coverage i j
        rcases relaxed_or_omitted hX.stable F.stable hGrid hσ hX.pressure_nonneg
            (redirect_min g hm) hX.budget F.budget ref hRef
            ⟨hEta.le, contactTolerance_le_one g⟩ valid.slope_nonneg valid.gain_nonneg
            (slope_step_le g hEta) (gain_sigma_le g hEta.le) with hGood | ⟨r,hr,_,hb⟩
        · apply (hBad ((relaxedCheck_spec g pat view).mpr ?_)).elim
          have hCov : view.coverage = (holdings X).physical g (privateScale g) := hX.coverage
          have hJoint : view.joint = (holdings X).joint (redirect g hm) := hX.joint
          change Relaxed g (contactPattern g view.coverage ref (contactTolerance g) hEta.le)
            view.coverage view.joint view.pressure (contactTolerance g)
          rw [hCov, hJoint]
          exact hGood
        · obtain ⟨i,j,z,rfl,hel⟩ := extended_optional g hm F hr
          refine ⟨(finProdFinEquiv (i,j), z.val), ?_, ?_⟩
          · exact Finset.mem_biUnion.mpr ⟨_, hr, Finset.mem_singleton_self _⟩
          · exact ((intervals_match g hm valid hX i j).2 z hel).mpr hb

end Kintali.MarketTrial
