module

public import Kintali.QuotaSweep.Arithmetic
import all StochasticGames.Precision
import Mathlib.Tactic.Positivity

/-!
# Uniform bit bounds for the executable sweep

The integer rate bound uses at most `|V|+1` positions for each of `|V|`
sources. Bounding every position separately also covers the terminal. The
same polynomial factor bounds the numerator of a release rate or of the
total private rate. Consequently the denominator size grows additively
in bits, even across a complete run of the recursive implementation.
-/

open scoped BigOperators
open StochasticGames.Precision
open Kintali.QuotaSweep.Arithmetic

@[expose] public section
namespace Kintali.QuotaSweep

namespace Routing
variable {V : Type*} [DecidableEq V] [Fintype V]

def rateBound (V : Type*) [Fintype V] (D A : ℕ) : ℕ :=
  max D (Fintype.card (Option V) * (Fintype.card V * A))

theorem path_bounded {D A : ℕ} {inject : V → ℚ} (h : ∀ v, Bounded D A (inject v))
    (next : V → Option V) (v : V) : Bounded D (rateBound V D A) (pathRate next inject v) := by
  apply bounded_mono _ (le_max_right ..)
  have harr (k : ℕ) : Bounded D (Fintype.card V * A) (arrival next inject k v) := by
    apply bounded_sum Finset.univ
    intro u _
    split
    · exact h u
    · exact bounded_zero D A
  simpa [pathRate] using bounded_sum (Finset.range (Fintype.card (Option V))) (fun k _ => harr k)

end Routing

namespace Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] (K : Book B S E)

def recordBound (B S : Type*) [Fintype B] [Fintype S] (D A : ℕ) : ℕ :=
  Fintype.card S * Routing.rateBound (Vertex B S) D A +
  Fintype.card B * Routing.rateBound (Vertex B S) D A

/-- Per-event factor for the common denominator. -/
def factorBound (B S : Type*) [Fintype B] [Fintype S] (D A : ℕ) : ℕ :=
  max 1 (max D (max (Routing.rateBound (Vertex B S) D A)
    (Fintype.card B * recordBound B S D A)))

theorem through_bounded {D A : ℕ} {rate : S → ℚ} (hr : ∀ s, Bounded D A (rate s))
    (x : Record B S E → ℚ) (v : Vertex B S) :
    Bounded D (Routing.rateBound (Vertex B S) D A) (K.through x rate v) := by
  unfold through
  split
  · rcases K.aroundCycle_zero_or_one x v with h | h <;> rw [h]
    · exact bounded_zero _ _
    · exact bounded_mono ⟨Clears.one D, by simp⟩ (le_max_left D _ )
  · exact Routing.path_bounded (fun v => by
      cases v with
      | inl _ => exact bounded_zero D A
      | inr s => exact hr s) _ _

theorem direction_bounded {D A : ℕ} {rate : S → ℚ} (hr : ∀ s, Bounded D A (rate s))
    (x : Record B S E → ℚ) (r : Record B S E) :
    Bounded D (recordBound B S D A) (K.direction x (K.through x rate) r) := by
  apply bounded_sub
  · apply bounded_sum Finset.univ
    intro s _
    split
    · exact K.through_bounded hr x _
    · exact bounded_zero _ _
  · apply bounded_sum Finset.univ
    intro b _
    split
    · exact K.through_bounded hr x _
    · exact bounded_zero _ _

theorem budgetSlope_bounded {D A : ℕ} {P : Parameters B S}
    (hr : ∀ s, Bounded D A (P.rate s)) (z : State B S E) :
    Bounded D (Fintype.card B * recordBound B S D A) (K.budgetSlope P z) := by
  exact bounded_mono (bounded_sum P.privateBuyers (fun b _ => K.direction_bounded hr _ (outside b)))
    (Nat.mul_le_mul_right _ (Finset.card_le_univ _))

/-- A single scale for the pressure, allocation and two stopping constants. -/
structure Scale (P : Parameters B S) (z : State B S E) (d : ℕ) : Prop where
  pressure : Clears d z.pressure
  allocation : ∀ e, Clears d (z.allocation e)
  target : Clears d P.target
  upper : Clears d P.upper

private theorem segment_scale {D A d : ℕ} {P : Parameters B S} {z : State B S E}
    (hr : ∀ s, Bounded D A (P.rate s)) (h : Scale P z d) (δ : ℚ) (c : ℕ)
    (hδ : ∀ v slope : ℚ, Clears d v → Clears D slope → Clears (d*c) (v + δ*slope)) :
    Scale P (K.segment P z δ) (d*c) := by
  have hs : Clears D (K.speed z.allocation) := by
    unfold speed
    split
    · exact Clears.zero _
    · exact Clears.one _
  refine ⟨hδ _ _ h.pressure hs, ?_, clears_multiple h.target c, clears_multiple h.upper c⟩
  intro e
  simp only [segment, snapshot_eq, move]
  exact hδ _ _ (h.allocation e) (K.direction_bounded hr _ e).1

theorem budget_scale {D A d : ℕ} {P : Parameters B S} {z : State B S E}
    (hD : 0 < D) (hr : ∀ s, Bounded D A (P.rate s)) (h : Scale P z d) :
    ∃ c : ℕ, 0 < c ∧ c ≤ factorBound B S D A ∧
      Scale P (K.segment P z (K.budgetTime P z)) (d*c) := by
  have hg := h.target.sub (clears_sum P.privateBuyers (fun b _ => h.allocation (outside b)))
  obtain ⟨c, hp, hc, ha⟩ := affine_ratio hD hg (K.budgetSlope_bounded hr z)
  refine ⟨c, hp, hc.trans (max_le_max_left 1 ?_), K.segment_scale hr h _ c ha⟩
  exact (le_max_right ..).trans (le_max_right ..)

theorem duration_scale {D A d : ℕ} {P : Parameters B S} {z : State B S E}
    (hD : 0 < D) (hr : ∀ s, Bounded D A (P.rate s)) (h : Scale P z d) :
    ∃ c : ℕ, 0 < c ∧ c ≤ factorBound B S D A ∧
      Scale P (K.segment P z (K.duration z.allocation P.rate z.pressure P.upper)) (d*c) := by
  let δ := K.duration z.allocation P.rate z.pressure P.upper
  have hm : δ ∈ K.times z.allocation P.rate z.pressure P.upper := K.duration_mem ..
  have cases' : δ = P.upper-z.pressure ∨ δ ∈ K.exhaustions z.allocation P.rate := by
    by_cases hc : K.hasCycle z.allocation = true
    · exact Or.inr (by simpa [times, hc] using hm)
    · simpa [times, hc] using hm
  rcases cases' with hc | he
  · refine ⟨D, hD, (le_max_left ..).trans (le_max_right ..), K.segment_scale hr h _ D ?_⟩
    intro v slope hv hs
    change Clears (d*D) (v+δ*slope)
    rw [hc]
    exact affine_cap hv (h.upper.sub h.pressure) hs
  · obtain ⟨b, _, hb⟩ := K.mem_exhaustions.mp he
    obtain ⟨c, hp, hc, ha⟩ := affine_ratio hD (h.allocation (K.worst z.allocation b))
      (K.through_bounded hr z.allocation (.inl b))
    refine ⟨c, hp, hc.trans (max_le_max_left 1 ?_), K.segment_scale hr h _ c ?_⟩
    · exact (le_max_left ..).trans (le_max_right ..)
    · intro v slope hv hs
      change Clears (d*c) (v+δ*slope)
      rw [← hb]
      exact ha _ _ hv hs

/-- One positive common denominator for the final result and the stopping
constants. Its value is bounded by the initial scale times `factorBound^fuel`. -/
theorem run_scale {D A d : ℕ} {P : Parameters B S} (hD : 0 < D)
    (hr : ∀ s, Bounded D A (P.rate s)) (fuel : ℕ) (z : State B S E)
    (hd : 0 < d) (h : Scale P z d) :
    ∃ d' : ℕ, 0 < d' ∧ d' ≤ d * factorBound B S D A ^ fuel ∧ Scale P (K.run P fuel z) d' := by
  induction fuel generalizing z d with
  | zero => exact ⟨d, hd, by simp, h⟩
  | succ n ih =>
    let F := factorBound B S D A
    have hf : 1 ≤ F := le_max_left ..
    have short {c : ℕ} (hc : c ≤ F) : d*c ≤ d*F^(n+1) := by
      exact Nat.mul_le_mul_left _ (hc.trans (by simpa [pow_succ] using
        (Nat.mul_le_mul_right F (one_le_pow₀ hf : 1 ≤ F^n))))
    simp only [run]
    split
    · obtain ⟨c, hp, hc, hnew⟩ := K.budget_scale hD hr h
      exact ⟨d*c, Nat.mul_pos hd hp, short hc, hnew⟩
    · obtain ⟨c, hp, hc, hnew⟩ := K.duration_scale hD hr h
      split
      · exact ⟨d*c, Nat.mul_pos hd hp, short hc, hnew⟩
      · obtain ⟨d', hp', hbound, hfinal⟩ := ih _ (Nat.mul_pos hd hp) hnew
        refine ⟨d', hp', hbound.trans ?_, hfinal⟩
        change d*c*F^n ≤ d*F^(n+1)
        calc
          _ ≤ d*F*F^n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d hc)
          _ = _ := by rw [pow_succ', Nat.mul_assoc]

end Book
end Kintali.QuotaSweep
