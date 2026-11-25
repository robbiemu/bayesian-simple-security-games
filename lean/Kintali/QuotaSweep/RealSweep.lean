module

public import Kintali.QuotaSweep.Contact
public import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stable allocations at every real pressure on the computed sweep

The graph events have rational coordinates. For a real query, follow the
same finite event sequence and interpolate on the first segment containing
the query. The support at any such point is contained in the support at
the rational midpoint, where ordinal stability has already been checked.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

def RealAccepts (x : Record B S E → ℝ) (v : Vertex B S) (e : Record B S E) : Prop :=
  ∃ f, v ∈ K.market.ends f ∧ K.market.rank v e < K.market.rank v f ∧ 0 < x f

def realQuota (rate : S → ℚ) (mass : B → ℚ) (t : ℝ) : Vertex B S → ℝ :=
  Sum.elim (fun b => (mass b : ℝ)) (fun s => (rate s : ℝ) * t)

structure StableReal (rate : S → ℚ) (mass : B → ℚ) (t : ℝ) (x : Record B S E → ℝ) : Prop where
  nonneg : ∀ e, 0 ≤ x e
  balance : ∀ v, (∑ e, if v ∈ K.market.ends e then x e else 0) = realQuota rate mass t v
  support : ∀ e, (K.market.ends e).card = 2 → 0 < x e → e ∈ K.retainedRecords
  stable : ∀ e ∈ K.retainedRecords, ¬((K.market.ends e).card = 2 ∧
    ∀ v ∈ K.market.ends e, K.RealAccepts x v e)

noncomputable def realMove (P : Parameters B S) (z : State B S E) (u : ℝ)
    (e : Record B S E) : ℝ :=
  (z.allocation e : ℝ) + u * (K.direction z.allocation (K.through z.allocation P.rate) e : ℝ)

def Sample (P : Parameters B S) (τ : ℝ) (y : Record B S E → ℝ) : Prop :=
  ∃ (z : State B S E) (d : ℚ) (u : ℝ), K.Feasible P z ∧
    0 ≤ d ∧ d ≤ K.duration z.allocation P.rate z.pressure P.upper ∧
    0 ≤ u ∧ u ≤ d ∧ τ = (z.pressure : ℝ) + u * (K.speed z.allocation : ℝ) ∧ y = K.realMove P z u

private theorem cast_load (v : Vertex B S) (x : Record B S E → ℚ) :
    (∑ e, if v ∈ K.market.ends e then (x e : ℝ) else 0) =
      ((∑ e, if v ∈ K.market.ends e then x e else 0 : ℚ) : ℝ) := by
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : v ∈ K.market.ends e <;> simp [hi]

/-- A sample obeys real nonnegativity, balances, retained support and the
two-ended blocking test. This includes pressures at which a cycle is processed. -/
theorem sample_stable {P : Parameters B S} {τ : ℝ} {y : Record B S E → ℝ}
    (hr : ∀ s, 0 ≤ P.rate s) (hs : K.Sample P τ y) : K.StableReal P.rate P.mass τ y := by
  obtain ⟨z, d, u, hz, hd, hstep, hu, hud, rfl, rfl⟩ := hs
  let q := K.through z.allocation P.rate
  let slope := K.direction z.allocation q
  have hf := K.stable_segment hz hr hd hstep
  have hm := K.stable_segment hz hr (show 0 ≤ d/2 by linarith)
    ((show d/2 ≤ d by linarith).trans hstep)
  have hp {e : Record B S E} (h : 0 < K.realMove P z u e) : 0 < K.move z.allocation q (d/2) e := by
    by_contra! hn
    have hinit := hz.nonneg e
    have hend := hf.nonneg e
    change 0 ≤ z.allocation e + d * slope e at hend
    change z.allocation e + d/2 * slope e ≤ 0 at hn
    have hmid : z.allocation e + d/2*slope e =
        (z.allocation e + (z.allocation e + d*slope e))/2 := by ring
    have hz' : z.allocation e = 0 := by linarith
    have hprod : d * slope e = 0 := by linarith
    change 0 < (z.allocation e : ℝ) + u * (slope e : ℝ) at h
    rcases mul_eq_zero.mp hprod with he | he
    · have hud' : u ≤ 0 := by simpa [he] using hud
      simp [hz', le_antisymm hud' hu] at h
    · simp [hz', he] at h
  refine ⟨?_, ?_, fun e hc he => hm.support e hc (hp he), ?_⟩
  · intro e
    change 0 ≤ (z.allocation e : ℝ) + u * (slope e : ℝ)
    by_cases h : 0 ≤ (slope e : ℝ)
    · exact add_nonneg (by exact_mod_cast hz.nonneg e) (mul_nonneg hu h)
    · have he : 0 ≤ (z.allocation e : ℝ) + (d : ℝ) * (slope e : ℝ) := by
        exact_mod_cast hf.nonneg e
      linarith [mul_le_mul_of_nonpos_right hud (le_of_not_ge h)]
  · intro v
    have split (e : Record B S E) :
        (if v ∈ K.market.ends e then K.realMove P z u e else 0) =
        (if v ∈ K.market.ends e then (z.allocation e : ℝ) else 0) +
          u * (if v ∈ K.market.ends e then (slope e : ℝ) else 0) := by
      by_cases hi : v ∈ K.market.ends e <;> simp [realMove, q, slope, hi]
    simp only [split, Finset.sum_add_distrib, ← Finset.mul_sum, K.cast_load, hz.balance]
    have hdir := K.sum_direction (K.through_conservation z.allocation P.rate) v
    change (∑ e, if v ∈ K.market.ends e then slope e else 0) = _ at hdir
    rw [hdir]
    cases v <;> simp [quota, realQuota, injection]
    ring
  · intro r hret hb
    apply hm.stable r hret
    refine ⟨hb.1, ?_⟩
    intro v hv
    obtain ⟨f, hi, better, pos⟩ := hb.2 v hv
    exact ⟨f, hi, better, hp pos⟩

/-- Real-valued queries share the finite rational event schedule. -/
noncomputable def realRun (P : Parameters B S) (τ : ℝ) : ℕ → State B S E → Record B S E → ℝ
  | 0, z => fun e => z.allocation e
  | fuel+1, z =>
    let d := K.duration z.allocation P.rate z.pressure P.upper
    let finish := K.segment P z d
    if τ ≤ z.pressure then fun e => z.allocation e
    else if τ ≤ finish.pressure then K.realMove P z (τ-z.pressure)
    else realRun P τ fuel finish

theorem realRun_sample (P : Parameters B S) (hr : ∀ s, 0 ≤ P.rate s) (τ : ℝ)
    (fuel : ℕ) (z : State B S E) (hz : K.Feasible P z) (ht : z.pressure < P.upper)
    (hlo : (z.pressure : ℝ) ≤ τ) (hhi : τ ≤ P.upper)
    (hcount : (K.remaining z.allocation).card < fuel) :
    K.Sample P τ (K.realRun P τ fuel z) := by
  induction fuel generalizing z with
  | zero => omega
  | succ n ih =>
    let d := K.duration z.allocation P.rate z.pressure P.upper
    let finish := K.segment P z d
    have hw := fun b => K.worst_positive_of_flow (x := z.allocation) hr (b := b)
    have hd : 0 < d := K.duration_pos hw ht
    change K.Sample P τ (if τ ≤ (z.pressure : ℝ) then fun e => ↑(z.allocation e)
      else if τ ≤ (finish.pressure : ℝ) then K.realMove P z (τ-z.pressure)
      else K.realRun P τ n finish)
    split
    · rename_i hu
      refine ⟨z,d,0,hz,hd.le,le_rfl,le_rfl,by exact_mod_cast hd.le,?_,?_⟩
      · simpa using le_antisymm hu hlo
      · funext e; simp [realMove]
    · rename_i hu
      have hlt := lt_of_not_ge hu
      split
      · rename_i hfin
        have hspeed : K.speed z.allocation = 1 := by
          by_cases hc : K.hasCycle z.allocation = true
          · have he : finish.pressure = z.pressure := by simp [finish, segment, speed, hc]
            rw [he] at hfin
            exact False.elim (hlt.not_ge hfin)
          · simp [speed, hc]
        have hf : finish.pressure = z.pressure+d := by simp [finish, segment, hspeed]
        rw [hf, Rat.cast_add] at hfin
        exact ⟨z,d,τ-z.pressure,hz,hd.le,le_rfl,sub_nonneg.mpr hlo,by linarith,by simp [hspeed],rfl⟩
      · rename_i hfin
        have hfu := (lt_of_not_ge hfin).trans_le hhi
        have hbelow : finish.pressure < P.upper := by exact_mod_cast hfu
        have he := (K.upper_or_exhaustion z.allocation P.rate z.pressure P.upper).resolve_left hbelow.ne
        obtain ⟨b, hb, hzero⟩ := he
        have hnew := K.move_purchases (x := z.allocation) (K.through_nonneg hr z.allocation) hd.le
        have hlt' : (K.remaining finish.allocation).card < (K.remaining z.allocation).card := by
          simpa [finish, segment] using K.remaining_card_lt hnew (hw b hb) hzero
        exact ih finish (K.feasible_segment hz hr hd.le le_rfl) hbelow (le_of_not_ge hfin)
          (by omega)

/-- A real-valued stable sweep between zero and the rational upper pressure. -/
noncomputable def realSweep (P : Parameters B S) (τ : ℝ) : Record B S E → ℝ :=
  K.realRun P τ (Fintype.card (Record B S E)+1) ⟨0,initial P.mass⟩

theorem realSweep_sample (P : Parameters B S) (hr : ∀ s, 0 ≤ P.rate s) (hm : ∀ b, 0 ≤ P.mass b)
    (hu : 0 < P.upper) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 (P.upper : ℝ)) :
    K.Sample P τ (K.realSweep P τ) :=
  K.realRun_sample P hr τ _ _ (K.initial_stable _ hm) hu (by simpa using hτ.1) hτ.2
    (Nat.lt_succ_of_le (Finset.card_le_univ _))

end Kintali.QuotaSweep.Book
