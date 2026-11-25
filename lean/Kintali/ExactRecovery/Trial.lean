module

public import Kintali.ExactRecovery.Witness

/-! # The trial's holdings or a fixed-witness blocker

Apply the contact comparison in the *same* expanded ordinal market, at the
two respective pressures. A nonblocking next optional quote is supplied by
the enlarged witness; an eligible next cap is permanent in every restriction.
-/

open scoped BigOperators
open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Expanded

variable {I J : Type*} {G : ℕ} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J] [Encodable I] [Encodable J]
variable {g : Game I J} {bi : I → ℕ} {si : J → ℕ} {redirect : I → J}
variable {optional : I → J → Quote G → Bool} {X Y : R I J G → ℚ} {σ t u η : ℚ}

theorem no_next_or_omitted
    (trial : Stable g bi si redirect optional σ t X) (full : Stable g bi si redirect allQuotes σ u Y)
    (grid : 0 < G) (scale : 0 < σ)
    (equalBudget : (∑ j, (holdings X).physical g σ j) = ∑ j, (holdings Y).physical g σ j) :
    (holdings X).NextClear g redirect σ ∨
    ∃ r ∈ extended g redirect σ Y, r ∉ retained g bi si redirect optional ∧
      (market g bi si).Blocks X r := by
  let M := market (G := G) g bi si
  let isSite : V I J G → Bool := Sum.elim (fun _ => false) (fun _ => true)
  let rate : V I J G → ℚ := Book.injection (siteRate g)
  let mass : V I J G → ℚ := Sum.elim (buyerMass g σ) (fun _ => 0)
  have qeq (s : ℚ) : quota (G := G) g σ s = Market.pressureQuota isSite rate mass s :=
    (quota_eq_sweep ..).trans (Book.quota_eq_pressureQuota ..)
  have sameModel (a : R I J G → ℚ) (s : ℚ) (sel : I → J → Quote G → Bool)
      (st : Stable g bi si redirect sel σ s a) :
      M.StableOn (retained g bi si redirect sel) (Market.pressureQuota isSite rate mass s) a := by
    rw [← qeq]
    exact st
  have bipartite (r : R I J G) (degree : (M.ends r).card = 2) :
      ∑ v ∈ M.ends r, Market.side isSite v = 0 := by
    rcases r with r | v
    · simp [M, market, ends, Market.side, isSite]
    · simp [M, market, ends] at degree
  have nonnegative (v : V I J G) : 0 ≤ rate v := by
    cases v with
    | inl => exact le_rfl
    | inr j =>
      unfold rate Book.injection siteRate
      simp only [Sum.elim_inr]
      split_ifs with active
      · exact one_div_nonneg.mpr active.le
      · rfl
  have outer (j : J) (r : R I J G) (hr : r ∈ privateOutsideSet g j) :
      ∃ v, isSite v = false ∧ M.ends r = {v} := by
    by_cases site : 0 < g.gain j
    · simp only [privateOutsideSet, ite_eq_left site, Finset.mem_image, Finset.mem_univ, true_and] at hr
      obtain ⟨k,rfl⟩ := hr
      exact ⟨_,rfl,rfl⟩
    · simp [privateOutsideSet, site] at hr
  have cx : Market.coverage (privateOutsideSet g) σ X = (holdings X).physical g σ :=
    funext (coverage_eq_physical trial scale grid)
  have cy : Market.coverage (privateOutsideSet g) σ Y = (holdings Y).physical g σ :=
    funext (coverage_eq_physical full scale grid)
  have nextIn (pair : I × J) (r : R I J G)
      (chosen : nextOptional g redirect (Market.coverage (privateOutsideSet g) σ Y) pair = some r) :
      r ∈ retained g bi si redirect allQuotes := by
    rcases pair with ⟨i,j⟩
    obtain ⟨_,_,eligible,rfl⟩ := (nextOptional_spec ..).mp chosen
    apply (book g bi si redirect allQuotes).mem_retainedRecords.mpr
    exact (retained_real ..).mpr ⟨eligible,Or.inr rfl⟩
  have hb : (∑ j, Market.coverage (privateOutsideSet g) σ X j) =
      ∑ j, Market.coverage (privateOutsideSet g) σ Y j := by rwa [cx, cy]
  rcases QuoteSearch.contact_and_next_or_blocker (M := M) (nextOptional g redirect)
      bipartite nonnegative scale outer (sameModel _ _ _ trial) (sameModel _ _ _ full)
      (retained_subset ..) (supporting_subset full) (covers_full_purchases full optional) nextIn hb
    with ⟨_,clear⟩ | blocker
  · rw [cx] at clear
    exact Or.inl (next_clear_of_witness trial clear)
  · exact Or.inr (by simpa only [extended, cy] using blocker)

/-- A trial's actual holdings and the budget equation give either an explicit
near-feasible point, or a blocker in the same fixed, finite witness set. -/
theorem relaxed_or_omitted
    (trial : Stable g bi si redirect optional σ t X) (full : Stable g bi si redirect allQuotes σ u Y)
    (grid : 0 < G) (scale : 0 < σ) (pressure : 0 ≤ t)
    (outsideMin : ∀ i j, Holdings.outsideCost g redirect i ≤ g.cost i j (Holdings.endpoint g j))
    (trialBudget : (∑ j, (holdings X).physical g σ j) = g.resources)
    (fullBudget : (∑ j, (holdings Y).physical g σ j) = g.resources)
    (reference : I → J) (refMin : ∀ i j, g.cost i (reference i) ((holdings X).physical g σ (reference i)) ≤
      g.cost i j ((holdings X).physical g σ j))
    (eBounds : 0 ≤ η ∧ η ≤ 1) (slope : ∀ i j, 0 ≤ g.slope i j) (gain : ∀ j, 0 ≤ g.gain j)
    (step : ∀ i j, 0 < g.gain j → g.slope i j / G ≤ η)
    (smallPrivate : ∀ j, g.gain j * σ ≤ η) :
    Relaxed g (contactPattern g ((holdings X).physical g σ) reference η eBounds.1)
        ((holdings X).physical g σ) ((holdings X).joint redirect) t η ∨
    ∃ r ∈ extended g redirect σ Y, r ∉ retained g bi si redirect optional ∧
      (market g bi si).Blocks X r := by
  apply (no_next_or_omitted trial full grid scale (trialBudget.trans fullBudget.symm)).imp_left
  intro next
  exact Holdings.contact_relaxed (stableContact trial grid scale pressure outsideMin trialBudget)
    reference refMin next (caps_clear trial) eBounds slope gain step smallPrivate

end Kintali.ExactRecovery.Expanded
