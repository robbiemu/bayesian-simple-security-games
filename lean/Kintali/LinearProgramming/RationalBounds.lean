module

public import Kintali.LinearProgramming.Recovery
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Binary lengths during exact repair

Put the coordinates of the input point on a single integer scale. The row
slacks then have that same denominator. A single multiplication by the
pivot determinant clears the entire repaired output.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open scoped BigOperators
open StochasticGames.BinarySize

variable {m n k : ℕ}

namespace SlackWindow

theorem radix_size (n h : ℕ) :
    (radix n h).size ≤ n.size + n.size + h.size + (height n h).size + 2 := by
  have a := size_mul_le n n
  have b := size_mul_le (n*n) h
  have c := size_mul_le (n*n*h) (height n h)
  have d := size_succ_le (amplification n h)
  have e := size_succ_le (amplification n h + 1)
  unfold amplification at d e
  rw [Nat.add_assoc, show 1 + 1 = 2 by decide] at e
  unfold radix amplification
  omega

theorem divisor_size_polynomial {m n h L : ℕ} (rows : m ≤ L) (cols : n ≤ L) (bits : h.size ≤ L) :
    (divisor m n h).size ≤ 16 * (L+2)^3 := by
  have sz := (size_le_self n).trans cols
  have sn : (n+1).size ≤ L+1 := (size_le_self _).trans (by omega)
  have hs : (height n h).size ≤ 1 + (L+1)*(L+1+L) := by
    apply (minorBound_size ..).trans
    gcongr
  have kr := radix_size n h
  have kbound : (radix n h).size ≤ L+L+L+(1+(L+1)*(L+1+L))+2 := by omega
  apply (divisor_size m n h).trans
  calc
    _ ≤ (1+(L+1)*(L+1+L)) + (1+(L+1)*(L+L+L+(1+(L+1)*(L+1+L))+2)) := by gcongr
    _ ≤ _ := by nlinarith

end SlackWindow

structure ScaledPoint (n : ℕ) where
  num : Fin n → ℤ
  den : ℕ
  positive : 0 < den

namespace ScaledPoint

def denominator (x : Fin n → ℚ) : ℕ := ∏ j, (x j).den

def encode (x : Fin n → ℚ) : ScaledPoint n where
  num j := System.scaleEntry (denominator x) (x j)
  den := denominator x
  positive := Finset.prod_pos (fun j _ => (x j).den_pos)

def value (X : ScaledPoint n) : Fin n → ℚ := fun j => (X.num j : ℚ) / (X.den : ℚ)

@[simp] theorem value_encode (x : Fin n → ℚ) : (encode x).value = x := by
  funext j
  change ((System.scaleEntry (denominator x) (x j) : ℤ) : ℚ) / (denominator x : ℚ) = x j
  have good : (denominator x : ℚ) ≠ 0 := by
    have h : 0 < denominator x := (encode x).positive
    exact_mod_cast h.ne'
  have dv : (x j).den ∣ denominator x :=
    Finset.dvd_prod_of_mem (fun t => (x t).den) (Finset.mem_univ j)
  rw [System.scaleEntry_cast (x j) dv, div_eq_iff good, mul_comm]

theorem denominator_size (x : Fin n → ℚ) :
    (denominator x).size ≤ 1 + ∑ j, (x j).den.size :=
  System.prod_size_le Finset.univ (fun j => (x j).den)

theorem encoded_num_size (x : Fin n → ℚ) (j : Fin n) :
    ((encode x).num j).natAbs.size ≤ (x j).num.natAbs.size + (denominator x).size :=
  System.scaleEntry_size ..

def residual (P : System (Fin m) (Fin n)) (X : ScaledPoint n) (i : Fin m) : ℤ :=
  (X.den : ℤ) * P.rhs i - P.coeff.mulVec X.num i

theorem cast_residual (P : System (Fin m) (Fin n)) (X : ScaledPoint n) (i : Fin m) :
    ((X.residual P i : ℤ) : ℚ) = (X.den : ℚ) * P.slack X.value i := by
  have dpos : (X.den : ℚ) ≠ 0 := by exact_mod_cast X.positive.ne'
  have nums : (fun j => ((X.num j : ℤ) : ℚ)) = (X.den : ℚ) • X.value := by
    funext j
    change ((X.num j : ℤ) : ℚ) = (X.den : ℚ) * (((X.num j : ℤ) : ℚ) / (X.den : ℚ))
    field_simp
  have dot := (Int.castRingHom ℚ).map_mulVec P.coeff X.num i
  change ((P.coeff.mulVec X.num i : ℤ) : ℚ) = P.matrix.mulVec (fun j => ((X.num j : ℤ) : ℚ)) i at dot
  rw [nums, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at dot
  rw [residual, Int.cast_sub, Int.cast_mul, Int.cast_natCast, dot, System.slack]
  ring

def numerator (P : System (Fin m) (Fin n)) (q : Pivot m n k) (X : ScaledPoint n) (j : Fin n) : ℤ :=
  q.den * X.num j + q.lift.mulVec (fun t => X.residual P (q.rows t)) j

/-- This gives an alternative implementation which uses only integer dot
products and a single fraction per output coordinate. -/
theorem repair_eq_divInt (P : System (Fin m) (Fin n)) (q : Pivot m n k) (X : ScaledPoint n)
    (nonzero : q.den ≠ 0) (j : Fin n) :
    (q.repair P X.value) j = Rat.divInt (X.numerator P q j) (q.den * (X.den : ℤ)) := by
  let G := q.lift.map (Int.castRingHom ℚ)
  let s := fun t => P.slack X.value (q.rows t)
  have d : (X.den : ℚ) ≠ 0 := by exact_mod_cast X.positive.ne'
  have qd : (q.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr nonzero
  have dot := (Int.castRingHom ℚ).map_mulVec q.lift (fun t => X.residual P (q.rows t)) j
  change ((q.lift.mulVec (fun t => X.residual P (q.rows t)) j : ℤ) : ℚ) =
    G.mulVec (fun t => ((X.residual P (q.rows t) : ℤ) : ℚ)) j at dot
  have sr : (fun t => ((X.residual P (q.rows t) : ℤ) : ℚ)) = (X.den : ℚ) • s :=
    funext (fun t => X.cast_residual P (q.rows t))
  rw [sr, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at dot
  rw [Rat.divInt_eq_div, numerator, Int.cast_add, Int.cast_mul, dot, Int.cast_mul, Int.cast_natCast]
  change ((X.num j : ℤ) : ℚ) / (X.den : ℚ) + (q.den : ℚ)⁻¹ * G.mulVec s j = _
  field_simp

private theorem dot_bound {a : ℕ} (f v : Fin a → ℤ) {C V : ℕ} (hf : ∀ j, |f j| ≤ (C : ℤ))
    (hv : ∀ j, |v j| ≤ (V : ℤ)) : |f ⬝ᵥ v| ≤ ((a * C * V : ℕ) : ℤ) := by
  calc
    _ ≤ ∑ j, |f j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin a, (C : ℤ) * V := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul (hf j) (hv j) (abs_nonneg _) (by positivity)
    _ = _ := by simp [mul_assoc]

theorem residual_bound (P : System (Fin m) (Fin n)) (X : ScaledPoint n) {h B U : ℕ}
    (coeff : ∀ i j, |P.coeff i j| ≤ (h : ℤ)) (rhs : ∀ i, |P.rhs i| ≤ (B : ℤ))
    (num : ∀ j, |X.num j| ≤ (U : ℤ)) (i : Fin m) :
    |X.residual P i| ≤ ((X.den * B + n * h * U : ℕ) : ℤ) := by
  unfold residual
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
  push_cast
  exact add_le_add (mul_le_mul_of_nonneg_left (rhs i) (by positivity))
    (by exact_mod_cast dot_bound _ _ (coeff i) num)

theorem parts_bound (P : System (Fin m) (Fin n)) (q : Pivot m n k) (X : ScaledPoint n)
    {h B U g : ℕ} (coeff : ∀ i j, |P.coeff i j| ≤ (h : ℤ)) (rhs : ∀ i, |P.rhs i| ≤ (B : ℤ))
    (num : ∀ j, |X.num j| ≤ (U : ℤ)) (denBound : |q.den| ≤ (g : ℤ))
    (liftBound : ∀ j t, |q.lift j t| ≤ (g : ℤ)) (nonzero : q.den ≠ 0) (j : Fin n) :
    ((q.repair P X.value) j).num.natAbs ≤ g * U + k * g * (X.den * B + n * h * U) ∧
    ((q.repair P X.value) j).den ≤ g * X.den := by
  have numeratorBound : |X.numerator P q j| ≤ ((g * U + k*g*(X.den*B + n*h*U) : ℕ) : ℤ) := by
    unfold numerator
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.cast_add]
    apply add_le_add
    · exact_mod_cast mul_le_mul denBound (num j) (abs_nonneg _) (Int.natCast_nonneg g)
    · exact dot_bound _ _ (liftBound j) (fun t => X.residual_bound P coeff rhs num (q.rows t))
  have denominatorBound : |q.den * (X.den : ℤ)| ≤ ((g * X.den : ℕ) : ℤ) := by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _), Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right denBound (Int.natCast_nonneg _)
  rw [← Int.natCast_natAbs] at numeratorBound denominatorBound
  rw [X.repair_eq_divInt P q nonzero]
  have reduced := divInt_parts_le (X.numerator P q j) (q.den * (X.den : ℤ))
    (mul_ne_zero nonzero (Int.natCast_ne_zero.mpr X.positive.ne'))
  exact ⟨reduced.1.trans (by exact_mod_cast numeratorBound), reduced.2.trans (by exact_mod_cast denominatorBound)⟩

end ScaledPoint

end Kintali.LinearProgramming
