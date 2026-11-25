module

public import Kintali.ExactRecovery.Pattern
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-! # The two sides of a relaxed pattern row

A row compares two affine terms, each of which may add the single common
residual. Inactive rows are the identity 0 ≤ 0. This keeps the row index type
fixed for every marking and status choice.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery

inductive Atom (I J : Type*) where
  | zero | one | budget | prior (i : I)
  | coverage (j : J) | coverageSum
  | flow (i : I) (j : J) | flowSum (i : I)
  | cost (i : I) (j : J) | pressure (j : J) | threshold

structure Term (I J : Type*) where
  atom : Atom I J
  residual : Bool := false

structure Comparison (I J : Type*) where
  left : Term I J
  right : Term I J

inductive Row (I J : Type*) where
  | coverageLower (j : J) | coverageUpper (j : J) | budgetLe | budgetGe
  | flowLower (i : I) (j : J) | rowLe (i : I) | rowGe (i : I) | unmarked (i : I) (j : J)
  | thresholdLower | residualLower | residualUpper
  | referenceCost (i : I) (j : J) | markedCost (i : I) (j : J)
  | fixLower (j : J) | fixUpper (j : J) | pressureLe (j : J) | pressureGe (j : J)
  deriving Fintype

variable {I J : Type*}

def compare (a b : Atom I J) (leftResidual rightResidual : Bool := false) : Comparison I J :=
  ⟨⟨a, leftResidual⟩, ⟨b, rightResidual⟩⟩

def comparison (p : Pattern I J) : Row I J → Comparison I J
  | .coverageLower j => compare .zero (.coverage j)
  | .coverageUpper j => compare (.coverage j) .one
  | .budgetLe => compare .coverageSum .budget
  | .budgetGe => compare .budget .coverageSum
  | .flowLower i j => compare .zero (.flow i j)
  | .rowLe i => compare (.flowSum i) (.prior i)
  | .rowGe i => compare (.prior i) (.flowSum i)
  | .unmarked i j => if p.marked i j then compare .zero .zero else compare (.flow i j) .zero
  | .thresholdLower => compare .zero .threshold
  | .residualLower => compare .zero .zero false true
  | .residualUpper => compare .zero .one true false
  | .referenceCost i j => compare (.cost i (p.reference i)) (.cost i j) false true
  | .markedCost i j => if p.marked i j then compare (.cost i j) (.cost i (p.reference i)) false true
      else compare .zero .zero
  | .fixLower j => if p.status j = .lower then compare (.coverage j) .zero else compare .zero .zero
  | .fixUpper j => if p.status j = .upper then compare .one (.coverage j) else compare .zero .zero
  | .pressureLe j => if p.status j = .upper then compare .zero .zero
      else compare (.pressure j) .threshold false true
  | .pressureGe j => if p.status j = .lower then compare .zero .zero
      else compare .threshold (.pressure j) false true

variable [Fintype I] [Fintype J]

def Atom.value (g : Game I J) (x : J → ℚ) (q : I → J → ℚ) (t : ℚ) : Atom I J → ℚ
  | .zero => 0
  | .one => 1
  | .budget => g.resources
  | .prior i => g.prior i
  | .coverage j => x j
  | .coverageSum => ∑ j, x j
  | .flow i j => q i j
  | .flowSum i => ∑ j, q i j
  | .cost i j => g.cost i j (x j)
  | .pressure j => g.pressure q j
  | .threshold => t

def Term.value (g : Game I J) (x : J → ℚ) (q : I → J → ℚ) (t e : ℚ) (a : Term I J) : ℚ :=
  a.atom.value g x q t + if a.residual then e else 0

def Comparison.Holds (g : Game I J) (x : J → ℚ) (q : I → J → ℚ) (t e : ℚ)
    (c : Comparison I J) : Prop := c.left.value g x q t e ≤ c.right.value g x q t e

attribute [local simp] comparison compare Comparison.Holds Term.value Atom.value

theorem all_rows_iff (g : Game I J) (p : Pattern I J) (x : J → ℚ) (q : I → J → ℚ) (t e : ℚ) :
    (∀ r, (comparison p r).Holds g x q t e) ↔ Relaxed g p x q t e := by
  constructor
  · intro h
    have lo (j : J) : 0 ≤ x j := by simpa using h (.coverageLower j)
    have hi (j : J) : x j ≤ 1 := by simpa using h (.coverageUpper j)
    have hn (i : I) (j : J) : 0 ≤ q i j := by simpa using h (.flowLower i j)
    refine ⟨fun j => ⟨lo j, hi j⟩, le_antisymm ?_ ?_, hn, fun i => le_antisymm ?_ ?_,
      ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using h .budgetLe
    · simpa using h .budgetGe
    · simpa using h (.rowLe i)
    · simpa using h (.rowGe i)
    · intro i j hm
      apply le_antisymm _ (hn i j)
      simpa [hm] using h (.unmarked i j)
    · simpa using h .thresholdLower
    · simpa using h .residualLower
    · simpa using h .residualUpper
    · intro i j
      simpa using h (.referenceCost i j)
    · intro i j hm
      simpa [hm] using h (.markedCost i j)
    · intro j hs
      apply le_antisymm _ (lo j)
      simpa [hs] using h (.fixLower j)
    · intro j hs
      apply le_antisymm (hi j)
      simpa [hs] using h (.fixUpper j)
    · intro j hs
      simpa [hs] using h (.pressureLe j)
    · intro j hs
      simpa [hs] using h (.pressureGe j)
  · intro h r
    cases r with
    | coverageLower j => simpa using (h.coverage_bounds j).1
    | coverageUpper j => simpa using (h.coverage_bounds j).2
    | budgetLe => simpa using h.budget.le
    | budgetGe => simpa using h.budget.ge
    | flowLower i j => simpa using h.nonneg i j
    | rowLe i => simpa using (h.row_sum i).le
    | rowGe i => simpa using (h.row_sum i).ge
    | thresholdLower => simpa using h.threshold_nonneg
    | residualLower => simpa using h.residual_bounds.1
    | residualUpper => simpa using h.residual_bounds.2
    | referenceCost i j => simpa using h.reference_le i j
    | unmarked i j =>
      cases hmark : p.marked i j <;> simp [hmark, h.unmarked]
    | markedCost i j =>
      cases hmark : p.marked i j <;> simp [hmark, h.marked_le]
    | fixLower j =>
      by_cases hs : p.status j = .lower <;> simp [hs, h.lower_coverage]
    | fixUpper j =>
      by_cases hs : p.status j = .upper <;> simp [hs, h.upper_coverage]
    | pressureLe j =>
      by_cases hs : p.status j = .upper <;> simp [hs, h.pressure_le]
    | pressureGe j =>
      by_cases hs : p.status j = .lower <;> simp [hs, h.pressure_ge]

end Kintali.ExactRecovery
