module

public import StochasticGames.AverageFeasibility
public import StochasticGames.BoundedLinearProgram
import all StochasticGames.AverageFeasibility
import all StochasticGames.BoundedLinearProgram
import Mathlib.Tactic.Linarith

/-! # The integer coefficient matrix of a branch

The column `none` stores the common slack. Doubling each average inequality
gives integral coefficients while leaving all input offsets on the right.
-/

@[expose] public section

namespace StochasticGames.BranchLinearization

open AverageFeasibility

variable {ι : Type*}

/-- Positions in the three input lists, followed by the lower and upper slack bounds. -/
abbrev Rows (system : System ι) :=
  Fin system.differences.length ⊕ Fin system.maxima.length ⊕ Fin system.averages.length ⊕ Bool

structure LinearRow (ι : Type*) where
  coeff : ι → ℤ
  slack : ℤ
  bound : ℚ

def indicator [DecidableEq ι] (a : Term ι) (j : ι) : ℤ :=
  if a.index = some j then 1 else 0

def difference [DecidableEq ι] (a b : Term ι) : LinearRow ι where
  coeff j := indicator a j - indicator b j
  slack := 0
  bound := b.offset - a.offset

def average [DecidableEq ι] (r : AverageRow ι) : LinearRow ι where
  coeff j := 2 * indicator r.lhs j - indicator r.first j - indicator r.second j
  slack := -2
  bound := r.first.offset + r.second.offset - 2 * r.lhs.offset

def slackBound (upper : Bool) : LinearRow ι where
  coeff _ := 0
  slack := if upper then 1 else -1
  bound := if upper then 1 else 0

def atPosition {α : Type*} (l : List α) (i : Fin l.length) : {a // a ∈ l} :=
  ⟨l.get i, List.get_mem l i⟩

def row [DecidableEq ι] (system : System ι) (branch : system.Branch) :
    Rows system → LinearRow ι
  | .inl i => let r := system.differences.get i; difference r.lhs r.rhs
  | .inr (.inl i) =>
    let r := atPosition system.maxima i
    difference r.val.lhs (branch r).val
  | .inr (.inr (.inl i)) => average (system.averages.get i)
  | .inr (.inr (.inr upper)) => slackBound upper

def matrix [DecidableEq ι] (system : System ι) (branch : system.Branch) :
    Matrix (Rows system) (Option ι) ℤ :=
  fun i j => j.elim (row system branch i).slack (row system branch i).coeff

def rhs [DecidableEq ι] (system : System ι) (branch : system.Branch) (i : Rows system) : ℚ :=
  (row system branch i).bound

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def Holds [Fintype ι] (r : LinearRow ι) (y : Option ι → K) : Prop :=
  (r.slack : K) * y none + ∑ j, (r.coeff j : K) * y (some j) ≤ (r.bound : K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem sum_indicator [Fintype ι] [DecidableEq ι] (a : Term ι) (x : ι → K) :
    ∑ j, (indicator a j : K) * x j = a.index.elim 0 x := by
  obtain ⟨idx, offset⟩ := a
  cases idx with
  | none => simp [indicator]
  | some i => simp [indicator, ite_mul]

private theorem holds_difference [Fintype ι] [DecidableEq ι] (a b : Term ι) (y : Option ι → K) :
    Holds (difference a b) y ↔ a.valueOver (fun j => y (some j)) ≤ b.valueOver (fun j => y (some j)) := by
  simp only [Holds, difference, Int.cast_zero, zero_mul, zero_add, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib, sum_indicator, Term.valueOver, Rat.cast_sub]
  constructor <;> intro h <;> linarith

private theorem holds_average [Fintype ι] [DecidableEq ι] (r : AverageRow ι) (y : Option ι → K) :
    Holds (average r) y ↔ r.lhs.valueOver (fun j => y (some j)) ≤
      (r.first.valueOver (fun j => y (some j)) + r.second.valueOver (fun j => y (some j))) / 2 + y none := by
  simp only [Holds, average, Int.cast_neg, Int.cast_ofNat, Int.cast_sub, Int.cast_mul, sub_mul,
    Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, sum_indicator, Term.valueOver, Rat.cast_sub, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat]
  constructor <;> intro h <;> linarith

private theorem holds_lower [Fintype ι] (y : Option ι → K) :
    Holds (slackBound false) y ↔ 0 ≤ y none := by
  simp [Holds, slackBound]

omit [IsStrictOrderedRing K] in
private theorem holds_upper [Fintype ι] (y : Option ι → K) :
    Holds (slackBound true) y ↔ y none ≤ 1 := by
  simp [Holds, slackBound]

omit [IsStrictOrderedRing K] in
private theorem feasible_rows [Fintype ι] [DecidableEq ι]
    (system : System ι) (branch : system.Branch) (y : Option ι → K) :
    BoundedLinearProgram.Feasible ((matrix system branch).map (fun z => (z : K)))
      (fun r => (rhs system branch r : K)) y ↔ ∀ i, Holds (row system branch i) y := by
  apply forall_congr'
  intro i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, matrix, rhs, Holds]

/-- Each matrix inequality is exactly its selected branch constraint, including both slack bounds. -/
theorem feasible_over_iff [Fintype ι] [DecidableEq ι]
    (system : System ι) (branch : system.Branch) (y : Option ι → K) :
    BoundedLinearProgram.Feasible ((matrix system branch).map (fun z => (z : K)))
      (fun r => (rhs system branch r : K)) y ↔
    system.RelaxedOver branch (fun i => y (some i)) (y none) ∧ 0 ≤ y none ∧ y none ≤ 1 := by
  rw [feasible_rows]
  constructor
  · intro allRows
    refine ⟨⟨?_, ?_, ?_⟩, (holds_lower y).1 (allRows (.inr (.inr (.inr false)))),
      (holds_upper y).1 (allRows (.inr (.inr (.inr true))))⟩
    · intro r hr
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (holds_difference _ _ y).1 (allRows (.inl i))
    · rintro ⟨r, hr⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (holds_difference _ _ y).1 (allRows (.inr (.inl i)))
    · intro r hr
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (holds_average _ y).1 (allRows (.inr (.inr (.inl i))))
  · rintro ⟨⟨hard, maxima, averages⟩, lower, upper⟩ i
    rcases i with i | i | i | b
    · exact (holds_difference _ _ y).2 (hard _ (List.get_mem _ i))
    · exact (holds_difference _ _ y).2 (maxima (atPosition system.maxima i))
    · exact (holds_average _ y).2 (averages _ (List.get_mem _ i))
    · cases b with
      | false => exact (holds_lower y).2 lower
      | true => exact (holds_upper y).2 upper

end OrderedField

theorem feasible_iff [Fintype ι] [DecidableEq ι]
    (system : System ι) (branch : system.Branch) (y : Option ι → ℚ) :
    BoundedLinearProgram.Feasible ((matrix system branch).map (fun z => (z : ℚ)))
      (rhs system branch) y ↔
    system.Relaxed branch (fun i => y (some i)) (y none) ∧ 0 ≤ y none ∧ y none ≤ 1 :=
  feasible_over_iff system branch y

private theorem indicator_bounds [DecidableEq ι] (a : Term ι) (j : ι) :
    0 ≤ indicator a j ∧ indicator a j ≤ 1 := by
  unfold indicator
  split <;> decide

/-- Repeated variables in a row preserve the uniform coefficient bound of two. -/
theorem entry_bound [DecidableEq ι] (system : System ι) (branch : system.Branch)
    (i : Rows system) (j : Option ι) : |matrix system branch i j| ≤ 2 := by
  have diff (a b : Term ι) (k : ι) : |(difference a b).coeff k| ≤ 2 := by
    have := indicator_bounds a k
    have := indicator_bounds b k
    rw [abs_le]
    dsimp [difference]
    omega
  have avg (r : AverageRow ι) (k : ι) : |(average r).coeff k| ≤ 2 := by
    have := indicator_bounds r.lhs k
    have := indicator_bounds r.first k
    have := indicator_bounds r.second k
    rw [abs_le]
    dsimp [average]
    omega
  rcases i with i | i | i | b
  · cases j with
    | none => change |(0 : ℤ)| ≤ 2; decide
    | some k => exact diff _ _ k
  · cases j with
    | none => change |(0 : ℤ)| ≤ 2; decide
    | some k => exact diff _ _ k
  · cases j with
    | none => change |(-2 : ℤ)| ≤ 2; decide
    | some k => exact avg _ k
  · cases j with
    | none => cases b <;> change |(_ : ℤ)| ≤ 2 <;> norm_num [matrix, row, slackBound]
    | some k => change |(0 : ℤ)| ≤ 2; decide

end StochasticGames.BranchLinearization
