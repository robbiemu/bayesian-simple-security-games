module

public import Mathlib.Basic.Real.Basic

/-! Input rows and real dual labels for a simple stochastic reachability game. -/

@[expose] public section

namespace StochasticGames.Source

variable {ι : Type*}

/-- The absorbing terminals are Win (`true`) and Lose (`false`). -/
abbrev Position (ι : Type*) := ι ⊕ Bool

/-- A head and a list of remaining choices encode an arbitrary nonempty successor list.
Repeated occurrences, including the two fair-coin outcomes, are allowed. -/
inductive Row (ι : Type*) where
  | max (head : Position ι) (tail : List (Position ι))
  | min (head : Position ι) (tail : List (Position ι))
  | chance (left right : Position ι)

/-- Extend the complemented labels using the dual terminal literals from H4, §2. -/
def dualLabel (y : ι → ℝ) : Position ι → ℝ
  | .inl i => y i
  | .inr true => 0
  | .inr false => 1

/-- All original Max choices must support the label, one original Min choice suffices,
and a chance row uses the fair-coin arithmetic mean. -/
def Row.DualConstraint (row : Row ι) (y : ι → ℝ) (i : ι) : Prop :=
  match row with
  | .max head tail => ∀ j ∈ head :: tail, y i ≤ dualLabel y j
  | .min head tail => ∃ j ∈ head :: tail, y i ≤ dualLabel y j
  | .chance left right => y i ≤ (dualLabel y left + dualLabel y right) / 2

def DualFeasible (rows : ι → Row ι) (y : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∀ i, (rows i).DualConstraint y i

end StochasticGames.Source
