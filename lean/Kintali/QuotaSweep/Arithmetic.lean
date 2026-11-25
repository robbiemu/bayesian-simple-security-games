module

public import Kintali.QuotaSweep.Run
public import StochasticGames.Precision
import all StochasticGames.Precision
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational arithmetic on a common denominator

An exhaustion or budget stop uses a ratio between an amount on scale `B`
and a rate on scale `D`. Multiplication by the absolute integer numerator
of that rate clears every updated record and the pressure on one common
scale. A stop at the upper pressure costs a factor of at most `D`.
-/

open scoped BigOperators
open StochasticGames.Precision

@[expose] public section
namespace Kintali.QuotaSweep.Arithmetic

theorem clears_multiple {d : ℕ} {x : ℚ} (h : Clears d x) (c : ℕ) : Clears (d*c) x := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i * (c : ℤ), ?_⟩
  push_cast
  calc
    _ = ((d : ℚ) * x) * c := by ring
    _ = _ := by rw [hi]

theorem clears_mul {d e : ℕ} {x y : ℚ} (hx : Clears d x) (hy : Clears e y) :
    Clears (d*e) (x*y) := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨i*j, ?_⟩
  push_cast
  calc
    _ = ((d : ℚ)*x)*((e : ℚ)*y) := by ring
    _ = _ := by rw [hi,hj]

theorem denominator_dvd {d : ℕ} {x : ℚ} (hd : 0 < d) (hx : Clears d x) : x.den ∣ d := by
  obtain ⟨i, hi⟩ := hx
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : x = (i : ℚ) / d := (eq_div_iff hd').mpr (by simpa [mul_comm] using hi)
  rw [he]
  have h := Rat.den_dvd i (d : ℤ)
  exact_mod_cast (by simpa [Rat.divInt_eq_div] using h :
    (((i : ℚ) / (d : ℚ)).den : ℤ) ∣ (d : ℤ))

/-- A common scale and a uniform bound for integer numerators on that scale. -/
def Bounded (D N : ℕ) (q : ℚ) : Prop := Clears D q ∧ |(D : ℚ)*q| ≤ N

theorem bounded_zero (D N : ℕ) : Bounded D N 0 := ⟨Clears.zero D, by simp⟩

theorem bounded_mono {D N M : ℕ} {q : ℚ} (h : Bounded D N q) (hle : N ≤ M) :
    Bounded D M q := ⟨h.1, h.2.trans (by exact_mod_cast hle)⟩

theorem bounded_neg {D N : ℕ} {q : ℚ} (h : Bounded D N q) : Bounded D N (-q) :=
  ⟨by simpa using (Clears.zero D).sub h.1, by simpa using h.2⟩

theorem bounded_sub {D M N : ℕ} {x y : ℚ} (hx : Bounded D M x) (hy : Bounded D N y) :
    Bounded D (M+N) (x-y) := by
  refine ⟨hx.1.sub hy.1, ?_⟩
  rw [mul_sub, Nat.cast_add]
  exact (abs_sub _ _).trans (add_le_add hx.2 hy.2)

theorem clears_sum {A : Type*} {D : ℕ} (s : Finset A) {f : A → ℚ}
    (h : ∀ a ∈ s, Clears D (f a)) : Clears D (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Clears.zero D
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih (fun b hb => h b (by simp [hb])))

theorem bounded_sum {A : Type*} {D N : ℕ} (s : Finset A) {f : A → ℚ}
    (h : ∀ a ∈ s, Bounded D N (f a)) : Bounded D (s.card*N) (∑ a ∈ s, f a) := by
  refine ⟨clears_sum s fun a ha => (h a ha).1, ?_⟩
  rw [Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun a ha => (h a ha).2).trans_eq
    (by simp))

/-- A positive rate with bounded integer numerator gives a strictly positive
factor no larger than that bound. This one factor works for every affine record. -/
private theorem affine_ratio_pos {B D N : ℕ} {gap q : ℚ} (hD : 0 < D)
    (hg : Clears B gap) (hq : Bounded D N q) (hp : 0 < q) :
    ∃ c : ℕ, 0 < c ∧ c ≤ N ∧ ∀ v slope : ℚ, Clears B v → Clears D slope →
      Clears (B*c) (v + (gap/q)*slope) := by
  obtain ⟨k, hk⟩ := hq.1
  have hkq : (0 : ℚ) < k := hk ▸ mul_pos (by exact_mod_cast hD) hp
  have hkpos : 0 < k := by exact_mod_cast hkq
  let c := k.toNat
  have hc : (c : ℚ) = (D : ℚ)*q := by
    rw [hk]
    exact_mod_cast Int.toNat_of_nonneg hkpos.le
  refine ⟨c, by dsimp [c]; omega, ?_, ?_⟩
  · have hb := hq.2
    rw [abs_of_pos (mul_pos (by exact_mod_cast hD) hp), ← hc] at hb
    exact_mod_cast hb
  · intro v slope hv hs
    obtain ⟨a, ha⟩ := hv
    obtain ⟨g, hgap⟩ := hg
    obtain ⟨j, hj⟩ := hs
    refine ⟨a*c + g*j, ?_⟩
    push_cast
    calc
      _ = ((B : ℚ)*v)*c + ((B : ℚ)*gap)*((D : ℚ)*slope) := by
        rw [hc]
        field_simp [hp.ne']
      _ = _ := by rw [ha, hgap, hj]

theorem affine_ratio {B D N : ℕ} {gap q : ℚ} (hD : 0 < D)
    (hg : Clears B gap) (hq : Bounded D N q) :
    ∃ c : ℕ, 0 < c ∧ c ≤ max 1 N ∧ ∀ v slope : ℚ, Clears B v → Clears D slope →
      Clears (B*c) (v + (gap/q)*slope) := by
  rcases lt_trichotomy q 0 with hn | rfl | hp
  · obtain ⟨c, hc, hb, h⟩ := affine_ratio_pos hD
      (show Clears B (-gap) by simpa using (Clears.zero B).sub hg) (bounded_neg hq) (neg_pos.mpr hn)
    exact ⟨c, hc, hb.trans (le_max_right ..), by simpa using h⟩
  · exact ⟨1, by decide, le_max_left .., fun v _ hv _ => by simpa using hv⟩
  · obtain ⟨c, hc, hb, h⟩ := affine_ratio_pos hD hg hq hp
    exact ⟨c, hc, hb.trans (le_max_right ..), h⟩

theorem affine_cap {B D : ℕ} {v gap slope : ℚ} (hv : Clears B v) (hg : Clears B gap)
    (hs : Clears D slope) : Clears (B*D) (v + gap*slope) :=
  (clears_multiple hv D).add (clears_mul hg hs)

end Kintali.QuotaSweep.Arithmetic
