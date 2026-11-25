module

public import Kintali.QuotaSweep.Run
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-!
# Budget contact and continuous private balances

The deterministic finite computation returns the first budget contact
at positive pressure. To sample the unrestricted sweep at any rational
pressure, use that pressure as the upper endpoint and a budget target
strictly below the empty sum. Fixed-quota invariance makes every such
sample agree on private purchases.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

/-- Lemma 3 on a finite restricted book. The inputs say that every monitored
private buyer retains its bid, and its site's upper quota strictly exceeds
the combined masses of that site's incident buyers. All conclusions concern the computed output. -/
theorem budget_contact {P : Parameters B S} (hr : ∀ s, 0 ≤ P.rate s)
    (hm : ∀ b, 0 ≤ P.mass b) (hu : 0 < P.upper) (htarget : 0 < P.target)
    (hstart : P.target < ∑ b ∈ P.privateBuyers, P.mass b)
    (possible : S → Finset B) (hpossible : ∀ e, K.buyer e ∈ possible (K.site e))
    (hbid : ∀ b ∈ P.privateBuyers, ∃ e ∈ K.retained, K.buyer e = b ∧
      (∑ c ∈ possible (K.site e), P.mass c) < P.rate (K.site e) * P.upper) :
    K.Feasible P (K.firstContact P) ∧ 0 < (K.firstContact P).pressure ∧
      (K.firstContact P).pressure < P.upper ∧
      privateOutside P.privateBuyers (K.firstContact P).allocation = P.target ∧
      ∀ y : State B S E, K.Feasible P y → y.pressure < (K.firstContact P).pressure →
        P.target < privateOutside P.privateBuyers y.allocation := by
  let z := K.firstContact P
  have h := K.firstContact_spec hr hm hu hstart
  have hne : z.pressure ≠ P.upper := by
    intro heq
    have hstable : K.market.StableOn K.retainedRecords (quota P.rate P.mass P.upper) z.allocation :=
      heq ▸ h.stable
    have hzero : privateOutside P.privateBuyers z.allocation = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      obtain ⟨e, he, rfl, hupper⟩ := hbid b hb
      have hexc := (K.sitePurchases_le_mass hstable (K.site e) (possible (K.site e))
        (fun f hf => hf ▸ hpossible f)).trans_lt hupper
      have hbal := K.vacancy_balance hstable (K.site e)
      exact K.private_filled_of_vacancy hstable he (by linarith)
    exact htarget.not_ge ((h.budget : P.target ≤ privateOutside P.privateBuyers z.allocation).trans_eq hzero)
  have hone : privateOutside P.privateBuyers z.allocation = P.target := h.stops.resolve_right hne
  have hpos : 0 < z.pressure := by
    by_contra! hz
    have hinit := K.initial_stable P.rate hm
    have hle := K.privateOutside_antitone (p := P.privateBuyers) hr hz h.stable hinit
    exact hstart.not_ge (hle.trans_eq hone)
  exact ⟨h.stable, hpos, lt_of_le_of_ne h.bounded hne, hone, h.first⟩

/-- A stable allocation in the same restriction at every nonnegative rational pressure. -/
def atPressure (rate : S → ℚ) (mass : B → ℚ) (t : ℚ) : Record B S E → ℚ :=
  if 0 < t then (K.firstContact ⟨rate, mass, ∅, t, -1⟩).allocation else initial mass

theorem atPressure_stable {rate : S → ℚ} {mass : B → ℚ} (hr : ∀ s, 0 ≤ rate s)
    (hm : ∀ b, 0 ≤ mass b) {t : ℚ} (ht : 0 ≤ t) :
    K.market.StableOn K.retainedRecords (quota rate mass t) (K.atPressure rate mass t) := by
  by_cases hp : 0 < t
  · let P : Parameters B S := ⟨rate, mass, ∅, t, -1⟩
    have h := K.firstContact_spec (P := P) hr hm hp (by simp [P])
    have hu := h.stops.resolve_left (by simp [privateOutside, P])
    have hs := h.stable
    unfold Feasible at hs
    rw [hu] at hs
    simpa [atPressure, hp, P] using hs
  · have he := le_antisymm (le_of_not_gt hp) ht
    subst t
    simpa [atPressure] using K.initial_stable rate hm

/-- A quantitative continuity bound follows from the total slack-variation
theorem. It applies to the private buyers of any one site, or to all sites. -/
theorem privateOutside_lipschitz {x y : Record B S E → ℚ} {rate : S → ℚ} {mass : B → ℚ}
    {t u : ℚ} (p : Finset B) (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x)
    (hy : K.market.StableOn K.retainedRecords (quota rate mass u) y) :
    |privateOutside p x - privateOutside p y| ≤ (∑ s, |rate s|) * |t - u| := by
  have hbound := Market.slack_variation_le hx hy
  simp only [Fintype.sum_sum_type, K.bid_degree, K.ends_outside, K.ends_vacancy,
    Finset.card_singleton, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, Finset.sum_const_zero, zero_add,
    quota, Sum.elim_inl, Sum.elim_inr, sub_self, abs_zero, ← mul_sub, abs_mul,
    ← Finset.sum_mul] at hbound
  rw [privateOutside, privateOutside, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hsubset := Finset.sum_le_univ_sum_of_nonneg (s := p)
    (fun b => abs_nonneg (x (outside b) - y (outside b)))
  exact hsubset.trans ((le_add_of_nonneg_right (Finset.sum_nonneg fun s _ =>
    abs_nonneg (x (vacancy s) - y (vacancy s)))).trans hbound)

theorem outside_sweep_continuous {rate : S → ℚ} {mass : B → ℚ} (hr : ∀ s, 0 ≤ rate s)
    (hm : ∀ b, 0 ≤ mass b) (p : Finset B) :
    ContinuousOn (fun t => privateOutside p (K.atPressure rate mass t)) (Set.Ici 0) := by
  let C : ℚ := ∑ s, |rate s|
  have hC : 0 ≤ C := Finset.sum_nonneg fun s _ => abs_nonneg (rate s)
  let L : NNReal := ⟨(C : ℝ), by exact_mod_cast hC⟩
  apply (show LipschitzOnWith L _ (Set.Ici (0 : ℚ)) from ?_).continuousOn
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u hu
  have hb := K.privateOutside_lipschitz p (K.atPressure_stable hr hm ht)
    (K.atPressure_stable hr hm hu)
  simp only [Rat.dist_eq]
  change |(privateOutside p (K.atPressure rate mass t) : ℝ) -
      (privateOutside p (K.atPressure rate mass u) : ℝ)| ≤ (C : ℝ) * |(t : ℝ) - (u : ℝ)|
  exact (show
    |((privateOutside p (K.atPressure rate mass t) : ℚ) : ℝ) -
      (privateOutside p (K.atPressure rate mass u) : ℝ)| ≤
      (C : ℝ) * |(t : ℝ) - (u : ℝ)| by exact_mod_cast hb)

end Kintali.QuotaSweep.Book
