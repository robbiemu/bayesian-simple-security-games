module

public import Kintali.ExactRecovery.Holdings
public import Kintali.ExactRecovery.Determinant
import Mathlib.Tactic.Linarith

/-! # Lemma 4, recovery at the full contact

The argument only uses nonblocking of the eligible next quote and the
permanent cap. Thus it applies to a restricted contact when those same
specific bids are known not to block. The attack flows in the relaxed
witness are computed directly from the given holdings.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery.Holdings

variable {I J : Type*} {G : ℕ}

def NextClear (a : Holdings I J G) (g : Game I J) (redirect : I → J) (σ : ℚ) : Prop :=
  ∀ i j, a.physical g σ j < 1 →
    let z := nextQuote G (a.physical g σ j)
    Eligible g redirect i j z → ¬a.costBlock g i j z

def CapClear (a : Holdings I J G) (g : Game I J) (redirect : I → J) : Prop :=
  ∀ i j, Eligible g redirect i j (cap G) → ¬a.costBlock g i j (cap G)

def HeldCost (a : Holdings I J G) (g : Game I J) (redirect : I → J) (i : I) (c : ℚ) : Prop :=
  (0 < a.outside i ∧ c = outsideCost g redirect i) ∨
    ∃ j z, 0 < a.real i j z ∧ c = quoteCost g i j z

variable [Fintype I] [Fintype J] {a : Holdings I J G} {g : Game I J} {redirect : I → J}
variable {σ t η : ℚ} (h : a.Contact g redirect σ t)

include h in
theorem held_le_outside {i : I} {c : ℚ} (held : a.HeldCost g redirect i c) :
    c ≤ outsideCost g redirect i := by
  obtain ⟨_,rfl⟩ | ⟨j,z,hp,rfl⟩ := held
  · rfl
  · exact (h.eligible_purchase i j z hp).2

include h in
/-- A held record costs at most η more than the physical cost at *every*
target, whether the next quote is eligible, pruned, or unnecessary. -/
theorem held_le_target (clear : a.NextClear g redirect σ) (ηnonneg : 0 ≤ η)
    (slope : ∀ i j, 0 ≤ g.slope i j) (step : ∀ i j, 0 < g.gain j → g.slope i j / G ≤ η)
    {i : I} {c : ℚ} (held : a.HeldCost g redirect i c) (j : J) :
    c ≤ g.cost i j (a.physical g σ j) + η := by
  have outside := held_le_outside h held
  have minCost := h.outside_min i j
  by_cases site : 0 < g.gain j
  · by_cases below : a.physical g σ j < 1
    · let z := nextQuote G (a.physical g σ j)
      obtain ⟨higher, close⟩ := nextQuote_bounds h.grid_pos (physical_bounds h j).1 below
      have atQuote : c ≤ quoteCost g i j z := by
        by_cases eligible : Eligible g redirect i j z
        · by_contra! dearer
          apply clear i j below eligible
          refine ⟨?_, siteAccepts_of_above h site higher⟩
          obtain ⟨out,_⟩ | ⟨k,w,purchased,rfl⟩ := held
          · exact Or.inl out
          · exact Or.inr ⟨k,w,purchased,dearer⟩
        · have pruned : outsideCost g redirect i < quoteCost g i j z :=
            lt_of_not_ge (fun le => eligible ⟨site,le⟩)
          exact outside.trans pruned.le
      apply atQuote.trans
      have inc := mul_le_mul_of_nonneg_left close (slope i j)
      change g.intercept i j + g.slope i j * price z ≤
        g.intercept i j + g.slope i j * a.physical g σ j + η
      change g.slope i j * price z ≤ _ at inc
      rw [mul_add, mul_one_div] at inc
      linarith [step i j site]
    · have full := le_antisymm (physical_bounds h j).2 (le_of_not_gt below)
      rw [full]
      simp only [endpoint, ite_eq_left site] at minCost
      linarith
  · simp only [physical, endpoint, ite_eq_right site] at minCost ⊢
    linarith

include h in
/-- Outside mass redirected into a positive-gain site goes only to a fully
covered site. The buyer prefers the eligible cap even at equal cost. -/
theorem outside_endpoint (clear : a.CapClear g redirect) {i : I} (out : 0 < a.outside i) :
    a.physical g σ (redirect i) = endpoint g (redirect i) := by
  let j := redirect i
  by_cases site : 0 < g.gain j
  · have value : price (cap G) = 1 := cap_price h.grid_pos
    have eligible : Eligible g redirect i j (cap G) := by
      refine ⟨site,?_⟩
      simp [quoteCost, outsideCost, endpoint, j, site, value]
    have full : a.physical g σ j = 1 := by
      apply le_antisymm (physical_bounds h j).2
      by_contra! below
      exact clear i j eligible ⟨Or.inl out, siteAccepts_of_above h site (value ▸ below)⟩
    change a.physical g σ j = endpoint g j
    simpa [endpoint, site] using full
  · change a.physical g σ j = endpoint g j
    simp [physical, endpoint, site]

variable [DecidableEq J]

/-- Outside balance is assigned to its endpoint-cost minimizer. -/
def joint (a : Holdings I J G) (redirect : I → J) (i : I) (j : J) : ℚ :=
  (∑ z, a.real i j z) + if redirect i = j then a.outside i else 0

def redirected (a : Holdings I J G) (redirect : I → J) (j : J) : ℚ :=
  ∑ i, if redirect i = j then a.outside i else 0

include h in
theorem joint_nonneg (i : I) (j : J) : 0 ≤ a.joint redirect i j := by
  apply add_nonneg (Finset.sum_nonneg (fun z _ => h.real_nonneg i j z))
  split_ifs <;> first | exact h.outside_nonneg i | exact le_rfl

include h in
theorem joint_sum (i : I) : (∑ j, a.joint redirect i j) = g.prior i := by
  simpa [joint, Finset.sum_add_distrib] using h.buyer_balance i

include h in
theorem positive_joint_marked (next : a.NextClear g redirect σ) (caps : a.CapClear g redirect)
    (ηnonneg : 0 ≤ η) (slope : ∀ i j, 0 ≤ g.slope i j)
    (step : ∀ i j, 0 < g.gain j → g.slope i j / G ≤ η) {i : I} {j : J}
    (flow : 0 < a.joint redirect i j) (k : J) :
    g.cost i j (a.physical g σ j) ≤ g.cost i k (a.physical g σ k) + η := by
  by_cases bought : ∃ z, 0 < a.real i j z
  · obtain ⟨z,hz⟩ := bought
    have held : a.HeldCost g redirect i (quoteCost g i j z) := Or.inr ⟨j,z,hz,rfl⟩
    apply le_trans _ (held_le_target h next ηnonneg slope step held k)
    exact add_le_add_right (mul_le_mul_of_nonneg_left (purchased_quote_ge h hz) (slope i j)) _
  · have zero (z : Quote G) : a.real i j z = 0 :=
      le_antisymm (le_of_not_gt (fun pos => bought ⟨z,pos⟩)) (h.real_nonneg i j z)
    by_cases target : redirect i = j
    · subst j
      have out : 0 < a.outside i := by simpa [joint, zero] using flow
      have held : a.HeldCost g redirect i (outsideCost g redirect i) := Or.inl ⟨out,rfl⟩
      rw [outside_endpoint h caps out]
      exact held_le_target h next ηnonneg slope step held k
    · simp [joint, zero, target] at flow

omit [Fintype J] in
private theorem pressure_split (j : J) :
    g.pressure (a.joint redirect) j = (a.realTotal j + a.redirected redirect j) * g.gain j := by
  simp [Game.pressure, joint, realTotal, redirected, Finset.sum_add_distrib]

include h in
theorem pressure_at_most (caps : a.CapClear g redirect) (gain : ∀ j, 0 ≤ g.gain j)
    {j : J} (below : a.physical g σ j < 1) : g.pressure (a.joint redirect) j ≤ t := by
  by_cases site : 0 < g.gain j
  · have noRedirect : a.redirected redirect j = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with target
      · apply le_antisymm _ (h.outside_nonneg i)
        by_contra! out
        have full := outside_endpoint h caps out
        rw [target] at full
        simp [endpoint, site] at full
        exact below.ne full
      · rfl
    rw [pressure_split, noRedirect, add_zero]
    have balance := (eq_div_iff site.ne').mp (h.site_balance j site)
    have extra : 0 ≤ (a.privateTotal j + a.vacancy j) * g.gain j :=
      mul_nonneg (add_nonneg (privateTotal_bounds h j).1 (h.vacancy_nonneg j)) site.le
    linarith only [balance, extra]
  · have zero := le_antisymm (le_of_not_gt site) (gain j)
    simpa [Game.pressure, zero] using h.pressure_nonneg

include h in
theorem pressure_at_least (smallPrivate : ∀ j, g.gain j * σ ≤ η) {j : J}
    (positive : 0 < a.physical g σ j) : t ≤ g.pressure (a.joint redirect) j + η := by
  have site : 0 < g.gain j := by
    by_contra! nonpos
    simp [physical, not_lt.mpr nonpos] at positive
  have noVac : a.vacancy j = 0 := le_antisymm
    (le_of_not_gt (fun vac => positive.ne' (vacancy_implies_zero h vac))) (h.vacancy_nonneg j)
  have balance := (eq_div_iff site.ne').mp (h.site_balance j site)
  rw [noVac, add_zero, add_mul] at balance
  have redirectedNonneg : 0 ≤ a.redirected redirect j := Finset.sum_nonneg
    (fun i _ => by split_ifs <;> first | exact h.outside_nonneg i | exact le_rfl)
  have small := (mul_le_mul_of_nonneg_right (privateTotal_bounds h j).2 site.le).trans
    ((mul_comm σ (g.gain j)).le.trans (smallPrivate j))
  rw [pressure_split, add_mul]
  linarith [mul_nonneg redirectedNonneg site.le]

include h in
/-- The restricted-contact form of the relaxation used in Lemma 4. Its point
consists of the physical coverage, the actual redirected holdings and t. -/
theorem contact_relaxed (reference : I → J)
    (refMin : ∀ i j, g.cost i (reference i) (a.physical g σ (reference i)) ≤
      g.cost i j (a.physical g σ j))
    (next : a.NextClear g redirect σ) (caps : a.CapClear g redirect)
    (eBounds : 0 ≤ η ∧ η ≤ 1) (slope : ∀ i j, 0 ≤ g.slope i j)
    (gain : ∀ j, 0 ≤ g.gain j) (step : ∀ i j, 0 < g.gain j → g.slope i j / G ≤ η)
    (smallPrivate : ∀ j, g.gain j * σ ≤ η) :
    Relaxed g (contactPattern g (a.physical g σ) reference η eBounds.1) (a.physical g σ)
      (a.joint redirect) t η := by
  refine ⟨physical_bounds h, h.budget, joint_nonneg h, joint_sum h, ?_, h.pressure_nonneg,
    eBounds, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hm
    apply le_antisymm _ (joint_nonneg h i j)
    by_contra! pos
    have bound := positive_joint_marked h next caps eBounds.1 slope step pos (reference i)
    simp [contactPattern, bound] at hm
  · intro i j
    exact (refMin i j).trans (le_add_of_nonneg_right eBounds.1)
  · intro i j hm
    simpa [contactPattern] using hm
  · intro j hs
    by_contra hx
    simp [contactPattern, statusAt, hx] at hs
    split at hs <;> contradiction
  · intro j hs
    by_contra hx
    by_cases hz : a.physical g σ j = 0 <;> simp [contactPattern, statusAt, hx, hz] at hs
  · intro j hs
    have below : a.physical g σ j < 1 := lt_of_le_of_ne (physical_bounds h j).2 (by
      intro eq
      simp [contactPattern, statusAt, eq] at hs)
    exact (pressure_at_most h caps gain below).trans (le_add_of_nonneg_right eBounds.1)
  · intro j hs
    have positive : 0 < a.physical g σ j := lt_of_le_of_ne (physical_bounds h j).1 (by
      intro eq
      simp [contactPattern, statusAt, eq.symm] at hs)
    exact pressure_at_least h smallPrivate positive

include h in
/-- Lemma 4. Stability at every eligible quote implies that the full
contact's marked pattern has an exact rational solution. -/
theorem full_contact_exact (reference : I → J)
    (refMin : ∀ i j, g.cost i (reference i) (a.physical g σ (reference i)) ≤
      g.cost i j (a.physical g σ j))
    (full : ∀ i j z, Eligible g redirect i j z → ¬a.costBlock g i j z)
    (eBounds : 0 ≤ η ∧ η ≤ 1) (small : η < 1 / (height g : ℚ))
    (slope : ∀ i j, 0 ≤ g.slope i j) (gain : ∀ j, 0 ≤ g.gain j)
    (step : ∀ i j, 0 < g.gain j → g.slope i j / G ≤ η)
    (smallPrivate : ∀ j, g.gain j * σ ≤ η) (priorSum : ∑ i, g.prior i = 1)
    (budget : 0 < g.resources) :
    ∃ x q t', Relaxed g (contactPattern g (a.physical g σ) reference η eBounds.1) x q t' 0 :=
  recover g _ priorSum gain budget
    (contact_relaxed h reference refMin (fun i j _ eligible => full i j _ eligible)
      (fun i j => full i j _) eBounds slope gain step smallPrivate) small

end Kintali.ExactRecovery.Holdings
