module

public import Kintali.ExactRecovery.Rows
public import Kintali.ExactRecovery.Scale
public import StochasticGames.LinearFeasibilityGap
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Integer matrix for a marked pattern

The two affine terms of a comparison are compiled separately. Each contributes
at most D M to a matrix entry or the right-hand side. This also covers the
case where the marked target coincides with the reference.
-/

open scoped BigOperators
open StochasticGames BoundedLinearProgram LinearFeasibilityGap

@[expose] public section

namespace Kintali.ExactRecovery

variable {I J : Type*} [Fintype I] [Fintype J]

def vector (x : J → ℚ) (q : I → J → ℚ) (t e : ℚ) : Variable I J → ℚ
  | .inl (i,j) => q i j
  | .inr (.inl j) => x j
  | .inr (.inr false) => t
  | .inr (.inr true) => e

def coverageOf (y : Variable I J → ℚ) (j : J) : ℚ := y (.inr (.inl j))
def flowOf (y : Variable I J → ℚ) (i : I) (j : J) : ℚ := y (.inl (i,j))
def thresholdOf (y : Variable I J → ℚ) : ℚ := y (.inr (.inr false))
def residualOf (y : Variable I J → ℚ) : ℚ := y (.inr (.inr true))

omit [Fintype I] [Fintype J] in
theorem vector_eta (y : Variable I J → ℚ) :
    vector (coverageOf y) (flowOf y) (thresholdOf y) (residualOf y) = y := by
  funext v
  rcases v with ⟨i,j⟩ | j | b
  · rfl
  · rfl
  · cases b <;> rfl

def Atom.constant (g : Game I J) : Atom I J → ℤ
  | .one => denominator g
  | .budget => scaled g (g.resources : ℚ)
  | .prior i => scaled g (g.prior i)
  | .cost i j => scaled g (g.intercept i j)
  | _ => 0

variable [DecidableEq I] [DecidableEq J]

def Term.coefficient (g : Game I J) (a : Term I J) : Variable I J → ℤ
  | .inl (i,j) => match a.atom with
    | .flow h k => if i = h then (if j = k then denominator g else 0) else 0
    | .flowSum h => if i = h then denominator g else 0
    | .pressure k => if j = k then scaled g (g.gain k) else 0
    | _ => 0
  | .inr (.inl j) => match a.atom with
    | .coverage k => if j = k then denominator g else 0
    | .coverageSum => denominator g
    | .cost i k => if j = k then scaled g (g.slope i k) else 0
    | _ => 0
  | .inr (.inr false) => match a.atom with
    | .threshold => denominator g
    | _ => 0
  | .inr (.inr true) => if a.residual then denominator g else 0

omit [DecidableEq I] [DecidableEq J] in
private theorem atom_constant_bound (g : Game I J) (a : Atom I J) :
    |a.constant g| ≤ atomBound g := by
  cases a <;> simp [Atom.constant, (atomBound_pos g).le, denominator_le_atomBound,
    scaled_abs_le g (budget_mem g), fun i => scaled_abs_le g (prior_mem g i),
    fun i j => scaled_abs_le g (intercept_mem g i j)]

theorem term_coefficient_bound (g : Game I J) (a : Term I J) (v : Variable I J) :
    |a.coefficient g v| ≤ atomBound g := by
  have hd : |(denominator g : ℤ)| ≤ atomBound g := by simpa using denominator_le_atomBound g
  have hz : |(0 : ℤ)| ≤ atomBound g := by simpa using (atomBound_pos g).le
  have hg (j : J) := scaled_abs_le g (gain_mem g j)
  have hs (i : I) (j : J) := scaled_abs_le g (slope_mem g i j)
  rcases a with ⟨a,b⟩
  rcases v with ⟨i,j⟩ | j | z
  · cases a <;> simp only [Term.coefficient] <;> (try split_ifs) <;> first | exact hd | exact hz | apply hg
  · cases a <;> simp only [Term.coefficient] <;> (try split_ifs) <;> first | exact hd | exact hz | apply hs
  · cases z <;> cases a <;> cases b <;> first | exact hd | exact hz

/-- Append the scaled constant to the dot product. The result is exactly D
times the original affine term. -/
theorem term_value (g : Game I J) (x : J → ℚ) (q : I → J → ℚ) (t e : ℚ) (a : Term I J) :
    (∑ v, (a.coefficient g v : ℚ) * vector x q t e v) + (a.atom.constant g : ℚ) =
      (denominator g : ℚ) * a.value g x q t e := by
  have hp (i : I) := scaled_cast g (prior_mem g i)
  have hb := scaled_cast g (budget_mem g)
  have hc (i : I) (j : J) := scaled_cast g (intercept_mem g i j)
  have hs (i : I) (j : J) := scaled_cast g (slope_mem g i j)
  have hg (j : J) := scaled_cast g (gain_mem g j)
  rcases a with ⟨a,r⟩
  cases a <;> cases r <;>
    simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Term.coefficient,
      vector, Atom.constant, Atom.value, Term.value, Game.cost, Game.pressure, apply_ite Int.cast,
      Finset.sum_ite_irrel, Finset.mul_sum, Finset.sum_mul, hp, hb, hc, hs, hg,
      mul_add, mul_left_comm, mul_comm] <;> ring_nf <;>
    simp [mul_comm, Finset.sum_mul]

def matrix (g : Game I J) (p : Pattern I J) : Matrix (Row I J) (Variable I J) ℤ :=
  fun r v => (comparison p r).left.coefficient g v - (comparison p r).right.coefficient g v

def rhs (g : Game I J) (p : Pattern I J) (r : Row I J) : ℤ :=
  (comparison p r).right.atom.constant g - (comparison p r).left.atom.constant g

private theorem difference_bound {a b B : ℤ} (ha : |a| ≤ B) (hb : |b| ≤ B) :
    |a - b| ≤ 2 * B := by
  have h := abs_sub_le a 0 b
  simp only [sub_zero, zero_sub, abs_neg] at h
  linarith

theorem matrix_bound (g : Game I J) (p : Pattern I J) (r : Row I J) (v : Variable I J) :
    |matrix g p r v| ≤ 2 * atomBound g :=
  difference_bound (term_coefficient_bound g _ _) (term_coefficient_bound g _ _)

omit [DecidableEq I] [DecidableEq J] in
theorem rhs_bound (g : Game I J) (p : Pattern I J) (r : Row I J) :
    |rhs g p r| ≤ 2 * atomBound g :=
  difference_bound (atom_constant_bound g _) (atom_constant_bound g _)

/-- Clearing preserves each inequality, in both directions. -/
theorem feasible_vector_iff (g : Game I J) (p : Pattern I J) (x : J → ℚ)
    (q : I → J → ℚ) (t e : ℚ) :
    Feasible (rationalMatrix (matrix g p)) (rationalRhs (rhs g p) 1) (vector x q t e) ↔
      Relaxed g p x q t e := by
  rw [← all_rows_iff]
  apply forall_congr'
  intro r
  let c := comparison p r
  have L := term_value g x q t e c.left
  have R := term_value g x q t e c.right
  change (∑ v, ((c.left.coefficient g v - c.right.coefficient g v : ℤ) : ℚ) *
    vector x q t e v) ≤ ((c.right.atom.constant g - c.left.atom.constant g : ℤ) : ℚ) / 1 ↔
    c.left.value g x q t e ≤ c.right.value g x q t e
  simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, div_one]
  have pos : (0 : ℚ) < denominator g := by exact_mod_cast denominator_pos g
  have scaleLe : (denominator g : ℚ) * c.left.value g x q t e ≤
      (denominator g : ℚ) * c.right.value g x q t e ↔ _ := mul_le_mul_iff_right₀ pos
  rw [← scaleLe, ← L, ← R]
  constructor <;> intro h <;> linarith

theorem feasible_iff (g : Game I J) (p : Pattern I J) (y : Variable I J → ℚ) :
    Feasible (rationalMatrix (matrix g p)) (rationalRhs (rhs g p) 1) y ↔
      Relaxed g p (coverageOf y) (flowOf y) (thresholdOf y) (residualOf y) := by
  conv_lhs => rw [← vector_eta y]
  exact feasible_vector_iff g p _ _ _ _

end Kintali.ExactRecovery
