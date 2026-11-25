module

public import Kintali.QuotaSweep.Endpoints
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Deterministic finite sweep and its exact rational budget stop

On a crossing segment the budget equation has a unique rational solution.
The driver recurses only on an internal exhaustion, which strictly decreases
the remaining-record cardinality. The saved table prevents recomputation
of the allocation history when the next stage scans its records.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep

structure State (B S E : Type*) where
  pressure : ℚ
  allocation : Record B S E → ℚ

structure Parameters (B S : Type*) where
  rate : S → ℚ
  mass : B → ℚ
  privateBuyers : Finset B
  upper : ℚ
  target : ℚ

namespace Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E)

/-- Build the association list eagerly; the next state holds only this table. -/
@[noinline] def snapshot (x : Record B S E → ℚ) : List (Record B S E × ℚ) :=
  K.records.map fun e => (e, x e)

/-- Taking the completed table as a data argument prevents a partial
application from postponing the table construction until every lookup. -/
@[noinline] def saved (t : ℚ) (entries : List (Record B S E × ℚ)) : State B S E :=
  ⟨t, fun e => (entries.lookup e).getD 0⟩

@[simp] theorem saved_pressure (t : ℚ) (entries : List (Record B S E × ℚ)) :
    (saved t entries).pressure = t := rfl

@[simp] theorem snapshot_eq (t : ℚ) (x : Record B S E → ℚ) :
    (saved t (K.snapshot x)).allocation = x := by
  funext e
  simp [saved, snapshot, List.lookup_graph x (K.complete e)]

variable [Fintype B] [Fintype S]

def segment (P : Parameters B S) (z : State B S E) (δ : ℚ) : State B S E :=
  saved (z.pressure + δ * K.speed z.allocation)
    (K.snapshot (K.move z.allocation (K.through z.allocation P.rate) δ))

def budgetSlope (P : Parameters B S) (z : State B S E) : ℚ :=
  privateOutside P.privateBuyers (K.direction z.allocation (K.through z.allocation P.rate))

def budgetTime (P : Parameters B S) (z : State B S E) : ℚ :=
  (P.target - privateOutside P.privateBuyers z.allocation) / K.budgetSlope P z

theorem budget_affine (P : Parameters B S) (z : State B S E) (δ : ℚ) :
    privateOutside P.privateBuyers (K.segment P z δ).allocation =
      privateOutside P.privateBuyers z.allocation + δ * K.budgetSlope P z := by
  simp [segment, budgetSlope, K.privateOutside_move]

theorem crossing_time {P : Parameters B S} {z : State B S E} {δ : ℚ}
    (hδ : 0 < δ) (hstart : P.target < privateOutside P.privateBuyers z.allocation)
    (hend : privateOutside P.privateBuyers (K.segment P z δ).allocation ≤ P.target) :
    0 < K.budgetTime P z ∧ K.budgetTime P z ≤ δ ∧ K.budgetSlope P z < 0 ∧
      privateOutside P.privateBuyers (K.segment P z (K.budgetTime P z)).allocation = P.target := by
  rw [K.budget_affine] at hend ⊢
  have hs : K.budgetSlope P z < 0 := by
    by_contra! h
    linarith [mul_nonneg hδ.le h]
  refine ⟨div_pos_of_neg_of_neg (sub_neg.mpr hstart) hs, (div_le_iff_of_neg hs).mpr ?_, hs, ?_⟩
  · linarith
  · rw [budgetTime, div_mul_cancel₀ _ hs.ne]
    ring

/-- Run from a pressure below the upper endpoint with the private outside
total above target. A budget tie stops before processing further cycles. -/
def run (P : Parameters B S) : ℕ → State B S E → State B S E
  | 0, z => z
  | fuel + 1, z =>
    let finish := K.segment P z (K.duration z.allocation P.rate z.pressure P.upper)
    if privateOutside P.privateBuyers finish.allocation ≤ P.target then
      K.segment P z (K.budgetTime P z)
    else if P.upper ≤ finish.pressure then finish
    else run P fuel finish

def firstContact (P : Parameters B S) [Fintype E] : State B S E :=
  K.run P (Fintype.card (Record B S E) + 1) ⟨0, initial P.mass⟩

variable [Fintype E]

def Feasible (P : Parameters B S) (z : State B S E) : Prop :=
  K.market.StableOn K.retainedRecords (quota P.rate P.mass z.pressure) z.allocation

theorem feasible_segment {P : Parameters B S} {z : State B S E} (hz : K.Feasible P z)
    (hr : ∀ s, 0 ≤ P.rate s) {δ : ℚ} (hδ : 0 ≤ δ)
    (hle : δ ≤ K.duration z.allocation P.rate z.pressure P.upper) :
    K.Feasible P (K.segment P z δ) := by
  simpa [Feasible, segment] using K.stable_segment hz hr hδ hle

structure SweepResult (P : Parameters B S) (start finish : State B S E) : Prop where
  stable : K.Feasible P finish
  advances : start.pressure ≤ finish.pressure
  bounded : finish.pressure ≤ P.upper
  budget : P.target ≤ privateOutside P.privateBuyers finish.allocation
  stops : privateOutside P.privateBuyers finish.allocation = P.target ∨ finish.pressure = P.upper
  first : ∀ (y : State B S E), K.Feasible P y → y.pressure < finish.pressure →
    P.target < privateOutside P.privateBuyers y.allocation

private theorem crossing_first {P : Parameters B S} {z : State B S E} {δ : ℚ}
    (hz : K.Feasible P z) (hr : ∀ s, 0 ≤ P.rate s)
    (hstart : P.target < privateOutside P.privateBuyers z.allocation)
    (hle : δ ≤ K.duration z.allocation P.rate z.pressure P.upper) (hs : K.budgetSlope P z < 0)
    (hc : privateOutside P.privateBuyers (K.segment P z δ).allocation = P.target)
    (y : State B S E) (hy : K.Feasible P y)
    (ht : y.pressure < (K.segment P z δ).pressure) :
    P.target < privateOutside P.privateBuyers y.allocation := by
  by_cases h : y.pressure ≤ z.pressure
  · exact hstart.trans_le (K.privateOutside_antitone hr h hy hz)
  · have htime := lt_of_not_ge h
    have hspeed : K.speed z.allocation = 1 := by
      by_cases hcycle : K.hasCycle z.allocation = true
      · simp [segment, speed, hcycle] at ht
        exact False.elim (ht.asymm htime)
      · simp [speed, hcycle]
    simp only [segment, saved_pressure, hspeed, mul_one] at ht
    let u := y.pressure - z.pressure
    have hu : 0 ≤ u := sub_nonneg.mpr htime.le
    have hud : u < δ := by dsimp [u]; linarith
    have hmid := K.feasible_segment hz hr hu (hud.le.trans hle)
    have heq : (K.segment P z u).pressure = y.pressure := by simp [segment, hspeed, u]
    have hcompare := K.privateOutside_antitone (p := P.privateBuyers) hr heq.ge hy hmid
    rw [K.budget_affine] at hc hcompare
    linarith [mul_lt_mul_of_neg_right hud hs]

/-- The full event count includes one final segment for the upper pressure or budget. -/
theorem run_spec (P : Parameters B S) (hr : ∀ s, 0 ≤ P.rate s)
    (fuel : ℕ) (z : State B S E) (hz : K.Feasible P z)
    (ht : z.pressure < P.upper) (hb : P.target < privateOutside P.privateBuyers z.allocation)
    (hcount : (K.remaining z.allocation).card < fuel) :
    K.SweepResult P z (K.run P fuel z) := by
  induction fuel generalizing z with
  | zero => omega
  | succ n ih =>
    let δ := K.duration z.allocation P.rate z.pressure P.upper
    let finish := K.segment P z δ
    have hw := fun b => K.worst_positive_of_flow (x := z.allocation) hr (b := b)
    have hd : 0 < δ := K.duration_pos hw ht
    have hsf : K.Feasible P finish := K.feasible_segment hz hr hd.le le_rfl
    have hspeed : 0 ≤ K.speed z.allocation := by unfold speed; split <;> decide
    have hadv : z.pressure ≤ finish.pressure := le_add_of_nonneg_right (mul_nonneg hd.le hspeed)
    have hcap : finish.pressure ≤ P.upper := K.pressure_le_upper ht.le
    change K.SweepResult P z (if privateOutside P.privateBuyers finish.allocation ≤ P.target then
      K.segment P z (K.budgetTime P z) else if P.upper ≤ finish.pressure then finish
      else K.run P n finish)
    split
    · rename_i hcross
      obtain ⟨hu, hle, hs, heq⟩ := K.crossing_time hd hb hcross
      refine ⟨K.feasible_segment hz hr hu.le hle, le_add_of_nonneg_right (mul_nonneg hu.le hspeed),
        ?_, heq.ge, Or.inl heq, K.crossing_first hz hr hb hle hs heq⟩
      exact (add_le_add_right (mul_le_mul_of_nonneg_right hle hspeed) z.pressure).trans hcap
    · rename_i hmiss
      have hmore := lt_of_not_ge hmiss
      split
      · rename_i hupper
        refine ⟨hsf, hadv, hcap, hmore.le, Or.inr (le_antisymm hcap hupper), ?_⟩
        intro y hy hlt
        exact hmore.trans_le (K.privateOutside_antitone hr hlt.le hy hsf)
      · rename_i hbelow
        have hbelow' := lt_of_not_ge hbelow
        have he := (K.upper_or_exhaustion z.allocation P.rate z.pressure P.upper).resolve_left
          hbelow'.ne
        obtain ⟨b, hrate, hzero⟩ := he
        have hnew := K.move_purchases (x := z.allocation) (K.through_nonneg hr z.allocation) hd.le
        have hlt : (K.remaining finish.allocation).card < (K.remaining z.allocation).card := by
          simpa [finish, segment] using K.remaining_card_lt hnew (hw b hrate) hzero
        have subrun := ih finish hsf hbelow' hmore (by omega)
        exact ⟨subrun.stable, hadv.trans subrun.advances, subrun.bounded, subrun.budget, subrun.stops, subrun.first⟩

theorem firstContact_spec {P : Parameters B S} (hr : ∀ s, 0 ≤ P.rate s)
    (hm : ∀ b, 0 ≤ P.mass b) (hu : 0 < P.upper)
    (hb : P.target < ∑ b ∈ P.privateBuyers, P.mass b) :
    K.SweepResult P ⟨0, initial P.mass⟩ (K.firstContact P) :=
  K.run_spec P hr _ _ (K.initial_stable P.rate hm) hu hb
    (Nat.lt_succ_of_le (Finset.card_le_univ _))

end Book
end Kintali.QuotaSweep
