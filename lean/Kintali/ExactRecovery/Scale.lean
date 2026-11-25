module

public import Kintali.ExactRecovery.Pattern
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Clearing the game tables

Every pattern uses the same denominator and integer entry bound. Repeated
rational data may be stored once in the product of denominators. The maximum
of the absolute reduced numerators bounds the magnitudes of their rationals.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Distinct input rationals used on either side of a pattern row. -/
def data (g : Game I J) : Finset ℚ :=
  {1, (g.resources : ℚ)} ∪ Finset.univ.image g.prior ∪ Finset.univ.image g.gain ∪
    Finset.univ.image (fun a : I × J => g.intercept a.1 a.2) ∪
    Finset.univ.image (fun a : I × J => g.slope a.1 a.2)

def denominator (g : Game I J) : ℕ := ∏ a ∈ data g, a.den

def magnitude (g : Game I J) : ℕ := max 1 ((data g).sup fun a => a.num.natAbs)

def scaled (g : Game I J) (a : ℚ) : ℤ := a.num * (denominator g / a.den : ℕ)

def atomBound (g : Game I J) : ℤ := (magnitude g : ℤ) * (denominator g : ℤ)

abbrev Variable (I J : Type*) := (I × J) ⊕ (J ⊕ Bool)

/-- The paper's integer H = (n C)^n, with C = 2 D M and
n = km + m + 2 (the two Boolean coordinates are threshold and residual). -/
def height (g : Game I J) : ℕ :=
  let n := Fintype.card (Variable I J)
  (n * (2 * denominator g * magnitude g)) ^ n

theorem variable_count :
    Fintype.card (Variable I J) = Fintype.card I * Fintype.card J + Fintype.card J + 2 := by
  simp [Variable, Nat.add_assoc]

theorem denominator_pos (g : Game I J) : 0 < denominator g :=
  Finset.prod_pos fun a _ => Nat.pos_of_ne_zero a.den_ne_zero

theorem magnitude_pos (g : Game I J) : 0 < magnitude g :=
  lt_of_lt_of_le (by decide : 0 < 1) (le_max_left ..)

theorem height_pos (g : Game I J) : 0 < height g := by
  have hn : 0 < Fintype.card (Variable I J) := by rw [variable_count]; omega
  unfold height
  exact pow_pos (Nat.mul_pos hn (Nat.mul_pos (Nat.mul_pos (by decide) (denominator_pos g))
    (magnitude_pos g))) _

theorem atomBound_pos (g : Game I J) : 0 < atomBound g :=
  mul_pos (by exact_mod_cast magnitude_pos g) (by exact_mod_cast denominator_pos g)

theorem denominator_le_atomBound (g : Game I J) : (denominator g : ℤ) ≤ atomBound g := by
  change _ ≤ (magnitude g : ℤ) * denominator g
  simpa using mul_le_mul_of_nonneg_right (by exact_mod_cast magnitude_pos g :
    (1 : ℤ) ≤ magnitude g) (by positivity : (0 : ℤ) ≤ denominator g)

theorem prior_mem (g : Game I J) (i : I) : g.prior i ∈ data g := by
  simp [data, Finset.mem_image_of_mem g.prior (Finset.mem_univ i)]

theorem gain_mem (g : Game I J) (j : J) : g.gain j ∈ data g := by
  simp [data, Finset.mem_image_of_mem g.gain (Finset.mem_univ j)]

theorem intercept_mem (g : Game I J) (i : I) (j : J) : g.intercept i j ∈ data g := by
  have h := Finset.mem_image_of_mem (fun a : I × J => g.intercept a.1 a.2)
    (Finset.mem_univ (i,j))
  exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem slope_mem (g : Game I J) (i : I) (j : J) : g.slope i j ∈ data g :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem (fun a : I × J => g.slope a.1 a.2)
    (Finset.mem_univ (i,j)))

theorem budget_mem (g : Game I J) : (g.resources : ℚ) ∈ data g := by simp [data]

theorem scaled_cast (g : Game I J) {a : ℚ} (ha : a ∈ data g) :
    (scaled g a : ℚ) = (denominator g : ℚ) * a := by
  have hd : a.den ∣ denominator g := Finset.dvd_prod_of_mem _ ha
  have cancel : (denominator g / a.den : ℕ) * a.den = denominator g :=
    Nat.div_mul_cancel hd
  have num : (a.num : ℚ) = a * (a.den : ℚ) := by
    exact ((div_eq_iff (by exact_mod_cast a.den_ne_zero)).mp a.num_div_den)
  simp only [scaled, Int.cast_mul, Int.cast_natCast, num]
  calc
    _ = ((denominator g / a.den : ℕ) : ℚ) * (a.den : ℚ) * a := by ring
    _ = _ := by rw [← Nat.cast_mul, cancel]

theorem scaled_abs_le (g : Game I J) {a : ℚ} (ha : a ∈ data g) :
    |scaled g a| ≤ atomBound g := by
  have hm : a.num.natAbs ≤ magnitude g :=
    (Finset.le_sup (f := fun r : ℚ => r.num.natAbs) ha).trans (le_max_right ..)
  have hu : |a.num| ≤ (magnitude g : ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hm)
  unfold scaled atomBound
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (denominator g / a.den : ℕ))]
  exact mul_le_mul hu (by exact_mod_cast Nat.div_le_self (denominator g) a.den)
    (by positivity) (by positivity)

end Kintali.ExactRecovery
