module

public import StochasticGames.BoundedLinearProgram
public import StochasticGames.BinarySize
public import Mathlib.Data.Rat.Lemmas
import all StochasticGames.BoundedLinearProgram
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Integer rows for exact rational feasibility

Multiply each rational inequality by the product of the positive denominators
in that row, including its right-hand side.  Feasibility is unchanged, and the
binary length of each resulting entry is bounded by the length of its own row.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open scoped BigOperators

structure System (Row Var : Type*) where
  coeff : Matrix Row Var ℤ
  rhs : Row → ℤ

variable {Row Var : Type*} [Fintype Var]

namespace System

def matrix (P : System Row Var) : Matrix Row Var ℚ :=
  P.coeff.map (fun a => (a : ℚ))

def Feasible (P : System Row Var) (x : Var → ℚ) : Prop :=
  ∀ i, P.matrix.mulVec x i ≤ (P.rhs i : ℚ)

def Bounded (P : System Row Var) : Prop :=
  ∃ B : ℚ, ∀ x, P.Feasible x → ∀ j, |x j| ≤ B

instance [Fintype Row] (P : System Row Var) (x : Var → ℚ) : Decidable (P.Feasible x) :=
  inferInstanceAs (Decidable (∀ i, P.matrix.mulVec x i ≤ (P.rhs i : ℚ)))

/-- One common positive multiplier per row. -/
def rowScale (a : Var → ℚ) (b : ℚ) : ℕ :=
  b.den * ∏ j, (a j).den

theorem rowScale_pos (a : Var → ℚ) (b : ℚ) : 0 < rowScale a b :=
  Nat.mul_pos b.den_pos (Finset.prod_pos (fun j _ => (a j).den_pos))

/-- Integer encoding of a rational coefficient whose denominator divides `D`. -/
def scaleEntry (D : ℕ) (q : ℚ) : ℤ :=
  q.num * (D / q.den : ℕ)

theorem scaleEntry_cast {D : ℕ} (q : ℚ) (divides : q.den ∣ D) :
    ((scaleEntry D q : ℤ) : ℚ) = (D : ℚ) * q := by
  have multiple : ((D / q.den : ℕ) : ℚ) * (q.den : ℚ) = (D : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel divides
  have num : (q.num : ℚ) = q * (q.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  calc
    _ = (q.num : ℚ) * ((D / q.den : ℕ) : ℚ) := by rw [scaleEntry, Int.cast_mul, Int.cast_natCast]
    _ = ((D / q.den : ℕ) : ℚ) * (q.den : ℚ) * q := by rw [num]; ring
    _ = _ := congrArg (· * q) multiple

def ofRational (A : Matrix Row Var ℚ) (b : Row → ℚ) : System Row Var where
  coeff i j := scaleEntry (rowScale (A i) (b i)) (A i j)
  rhs i := scaleEntry (rowScale (A i) (b i)) (b i)

theorem ofRational_coeff (A : Matrix Row Var ℚ) (b : Row → ℚ) (i : Row) (j : Var) :
    (((ofRational A b).coeff i j : ℤ) : ℚ) = (rowScale (A i) (b i) : ℚ) * A i j := by
  apply scaleEntry_cast
  exact (Finset.dvd_prod_of_mem (fun k => (A i k).den) (Finset.mem_univ j)).trans
    (dvd_mul_left _ _)

theorem ofRational_rhs (A : Matrix Row Var ℚ) (b : Row → ℚ) (i : Row) :
    (((ofRational A b).rhs i : ℤ) : ℚ) = (rowScale (A i) (b i) : ℚ) * b i := by
  apply scaleEntry_cast
  exact dvd_mul_right _ _

theorem ofRational_mulVec (A : Matrix Row Var ℚ) (b : Row → ℚ) (x : Var → ℚ) (i : Row) :
    (ofRational A b).matrix.mulVec x i = (rowScale (A i) (b i) : ℚ) * A.mulVec x i := by
  change (∑ j, (((ofRational A b).coeff i j : ℤ) : ℚ) * x j) = _
  simp_rw [ofRational_coeff, mul_assoc]
  exact (Finset.mul_sum ..).symm

theorem feasible_ofRational_iff (A : Matrix Row Var ℚ) (b : Row → ℚ) (x : Var → ℚ) :
    (ofRational A b).Feasible x ↔ StochasticGames.BoundedLinearProgram.Feasible A b x := by
  unfold Feasible StochasticGames.BoundedLinearProgram.Feasible
  apply forall_congr'
  intro i
  have pos : (0 : ℚ) < rowScale (A i) (b i) := by exact_mod_cast rowScale_pos (A i) (b i)
  rw [ofRational_mulVec, ofRational_rhs, mul_le_mul_iff_right₀ pos]

omit [Fintype Var] in
theorem prod_size_le (s : Finset Var) (a : Var → ℕ) :
    (∏ j ∈ s, a j).size ≤ 1 + ∑ j ∈ s, (a j).size := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have h := StochasticGames.BinarySize.size_mul_le (a j) (∏ k ∈ s, a k)
    omega

theorem rowScale_size (a : Var → ℚ) (b : ℚ) :
    (rowScale a b).size ≤ 1 + b.den.size + ∑ j, (a j).den.size := by
  have h := StochasticGames.BinarySize.size_mul_le b.den (∏ j, (a j).den)
  have k := prod_size_le Finset.univ (fun j => (a j).den)
  unfold rowScale
  omega

theorem scaleEntry_size (D : ℕ) (q : ℚ) :
    (scaleEntry D q).natAbs.size ≤ q.num.natAbs.size + D.size := by
  unfold scaleEntry
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact (StochasticGames.BinarySize.size_mul_le _ _).trans
    (Nat.add_le_add_left (Nat.size_le_size (Nat.div_le_self D q.den)) _)

end System

end Kintali.LinearProgramming
