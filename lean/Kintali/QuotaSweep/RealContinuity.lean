module

public import Kintali.QuotaSweep.RealSweep
public import Mathlib.Topology.Algebra.Order.Archimedean
public import Mathlib.Topology.DenseEmbedding
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! # Continuity and monotonicity between the exact event pressures -/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

noncomputable def realOutside (p : Finset B) (x : Record B S E → ℝ) : ℝ :=
  ∑ b ∈ p, x (outside b)

omit [Fintype E] in
theorem realOutside_move (p : Finset B) (P : Parameters B S) (z : State B S E) (u : ℝ) :
    realOutside p (K.realMove P z u) = (privateOutside p z.allocation : ℝ) +
      u * (privateOutside p (K.direction z.allocation (K.through z.allocation P.rate)) : ℝ) := by
  simp [realOutside, realMove, privateOutside, Finset.sum_add_distrib, Finset.mul_sum]

private theorem clipped_affine {a b s t c e f g d h L : ℚ} (hd : 0 ≤ d) (hh : 0 ≤ h)
    (test : ∀ q, 0 ≤ q → q ≤ d → ∀ r, 0 ≤ r → r ≤ h →
      (a+q*b)-(c+r*e) ≤ L*max 0 ((f+r*g)-(s+q*t)))
    {u v : ℝ} (hu : 0 ≤ u) (hud : u ≤ d) (hv : 0 ≤ v) (hvh : v ≤ h) :
    (a+u*b)-(c+v*e) ≤ (L : ℝ)*max 0 ((f+v*g)-(s+u*t)) := by
  let clip (cap x : ℝ) := max 0 (min cap x)
  let good (x y : ℝ) := (a+clip d x*b)-(c+clip h y*e) ≤
    (L : ℝ)*max 0 ((f+clip h y*g)-(s+clip d x*t))
  have hclosed : IsClosed {w : ℝ × ℝ | good w.1 w.2} := by
    apply isClosed_le <;> dsimp [good, clip] <;> fun_prop
  have hr (x y : ℚ) : good x y := by
    have hq := test (max 0 (min d x)) (le_max_left ..) (max_le hd (min_le_left ..))
      (max 0 (min h y)) (le_max_left ..) (max_le hh (min_le_left ..))
    dsimp [good, clip]
    exact_mod_cast hq
  have he : good u v := (Rat.denseRange_cast (𝕜 := ℝ)).induction_on₂ hclosed hr u v
  simpa [good, clip, min_eq_right hud, max_eq_right hu, min_eq_right hvh, max_eq_right hv] using he

/-- A one-sided quantitative bound proves monotonicity at equal or increasing
pressure and bounds the total variation along a segment or between segments. -/
theorem realOutside_compare {P : Parameters B S} (hr : ∀ j, 0 ≤ P.rate j) (p : Finset B)
    {τ ν : ℝ} {x y : Record B S E → ℝ} (hx : K.Sample P τ x) (hy : K.Sample P ν y) :
    realOutside p x - realOutside p y ≤ ((∑ j, |P.rate j| : ℚ) : ℝ) * max 0 (ν-τ) := by
  obtain ⟨z,d,u,hz,hd,hstep,hu,hud,rfl,rfl⟩ := hx
  obtain ⟨w,h,v,hw,hh,wend,hv,hvh,rfl,rfl⟩ := hy
  rw [K.realOutside_move, K.realOutside_move]
  apply clipped_affine hd hh _ hu hud hv hvh
  intro q hq hqd r hr' hrh
  have h₁ := K.stable_segment hz hr hq (hqd.trans hstep)
  have h₂ := K.stable_segment hw hr hr' (hrh.trans wend)
  rw [← K.privateOutside_move, ← K.privateOutside_move]
  rcases le_total (z.pressure + q * K.speed z.allocation) (w.pressure + r * K.speed w.allocation)
    with ht | ht
  · rw [max_eq_right (sub_nonneg.mpr ht)]
    have hl := K.privateOutside_lipschitz p h₁ h₂
    rw [abs_sub_comm (z.pressure + q * K.speed z.allocation), abs_of_nonneg (sub_nonneg.mpr ht)] at hl
    exact (le_abs_self _).trans hl
  · rw [max_eq_left (sub_nonpos.mpr ht), mul_zero]
    exact sub_nonpos.mpr (K.privateOutside_antitone hr ht h₂ h₁)

theorem realSweep_stable {P : Parameters B S} (hr : ∀ s, 0 ≤ P.rate s) (hm : ∀ b, 0 ≤ P.mass b)
    (hu : 0 < P.upper) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 (P.upper : ℝ)) :
    K.StableReal P.rate P.mass τ (K.realSweep P τ) :=
  K.sample_stable hr (K.realSweep_sample P hr hm hu hτ)

theorem realOutside_antitone {P : Parameters B S} (hr : ∀ s, 0 ≤ P.rate s)
    (hm : ∀ b, 0 ≤ P.mass b) (hu : 0 < P.upper) (p : Finset B) :
    AntitoneOn (fun t => realOutside p (K.realSweep P t)) (Set.Icc 0 (P.upper : ℝ)) := by
  intro t ht u htu hle
  have hb := K.realOutside_compare hr p (K.realSweep_sample P hr hm hu htu)
    (K.realSweep_sample P hr hm hu ht)
  rw [max_eq_left (sub_nonpos.mpr hle), mul_zero] at hb
  exact sub_nonpos.mp hb

theorem realOutside_continuous {P : Parameters B S} (hr : ∀ s, 0 ≤ P.rate s)
    (hm : ∀ b, 0 ≤ P.mass b) (hu : 0 < P.upper) (p : Finset B) :
    ContinuousOn (fun t => realOutside p (K.realSweep P t)) (Set.Icc 0 (P.upper : ℝ)) := by
  let C : ℚ := ∑ j, |P.rate j|
  let L : NNReal := ⟨(C : ℝ), by exact_mod_cast Finset.sum_nonneg (fun j _ => abs_nonneg (P.rate j))⟩
  apply (show LipschitzOnWith L _ _ from ?_).continuousOn
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u htu
  have hx := K.realSweep_sample P hr hm hu ht
  have hy := K.realSweep_sample P hr hm hu htu
  have bound (a b : ℝ) : max 0 (b-a) ≤ |a-b| := by
    exact max_le (abs_nonneg _) (by rw [abs_sub_comm]; exact le_abs_self _)
  rw [Real.dist_eq, Real.dist_eq, abs_le]
  constructor
  · have h := (K.realOutside_compare hr p hy hx).trans
      (mul_le_mul_of_nonneg_left (bound u t) L.property)
    rw [abs_sub_comm u t] at h
    change _ ≤ (L : ℝ) * |t-u| at h
    linarith
  · exact (K.realOutside_compare hr p hx hy).trans
      (mul_le_mul_of_nonneg_left (bound t u) L.property)

/-- Purchased private mass is continuous and nondecreasing as pressure grows. -/
theorem privatePurchases_regular {P : Parameters B S} (hr : ∀ s, 0 ≤ P.rate s)
    (hm : ∀ b, 0 ≤ P.mass b) (hu : 0 < P.upper) (p : Finset B) :
    let purchased := fun t => ((∑ b ∈ p, P.mass b : ℚ) : ℝ) - realOutside p (K.realSweep P t)
    MonotoneOn purchased (Set.Icc 0 (P.upper : ℝ)) ∧
      ContinuousOn purchased (Set.Icc 0 (P.upper : ℝ)) := by
  exact ⟨fun _ ha _ hb h => sub_le_sub_left (K.realOutside_antitone hr hm hu p ha hb h) _,
    continuousOn_const.sub (K.realOutside_continuous hr hm hu p)⟩

end Kintali.QuotaSweep.Book
