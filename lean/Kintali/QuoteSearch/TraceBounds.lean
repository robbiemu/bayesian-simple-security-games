module

public import Kintali.QuoteSearch.Algorithm

/-!
# Resource bounds on actual quote-search states

Apply the compressed-run bounds to the state reached after any number
of adaptive trials. The count follows the executable stopping branches.
-/

@[expose] public section

namespace Kintali.QuoteSearch

variable {pairs : ℕ} {Answer : Type*}

def intervalAt (J : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (p : Fin pairs) (t : ℕ) : ℕ × ℕ :=
  match trial (select J (stateAt J trial (initialTable quotes) t)) with
  | .cleared _ => (0, 0)
  | .blocked r => (r[p].lo, r[p].hi)

theorem stateAt_runs (J : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (p : Fin pairs) (t : ℕ) :
    (stateAt J trial (initialTable quotes) t)[p] =
      Runs.afterUpdates (intervalAt J trial quotes p) quotes[p] t := by
  induction t with
  | zero => simp [stateAt, initialTable, Runs.afterUpdates]
  | succ t ih =>
    cases hr : trial (select J (stateAt J trial (initialTable quotes) t)) with
    | cleared a =>
      simp [stateAt, turn, hr, Runs.afterUpdates, intervalAt, Runs.doubleInterval, ih]
    | blocked ranges =>
      simp [stateAt, turn, hr, double, Runs.afterUpdates, intervalAt]
      exact congrArg (Runs.doubleInterval ranges[p].lo ranges[p].hi) ih

theorem runCount_bound (J : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (p : Fin pairs) (t : ℕ) :
    (stateAt J trial (initialTable quotes) t)[p].length ≤ 1 + 2 * t := by
  rw [stateAt_runs]
  exact Runs.afterUpdates_count _ _ _

theorem weightWidth_bound (J : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (p : Fin pairs) (t : ℕ) :
    (Runs.weight (stateAt J trial (initialTable quotes) t)[p]).size ≤ quotes[p].size + t := by
  rw [stateAt_runs]
  exact Runs.afterUpdates_weight_size _ _ _

/-- Run the same search, returning the number of restricted trial calls. -/
def counted (J : ℕ) (trial : Trial pairs Answer) :
    ℕ → WeightTable pairs → Option Answer × ℕ
  | 0, _ => (none, 0)
  | fuel + 1, state =>
    match trial (select J state) with
    | .cleared answer => (some answer, 1)
    | .blocked ranges =>
      let rest := counted J trial fuel (double state ranges)
      (rest.1, rest.2 + 1)

theorem counted_spec (J : ℕ) (trial : Trial pairs Answer) (fuel : ℕ)
    (state : WeightTable pairs) :
    (counted J trial fuel state).1 = run J trial fuel state ∧
      (counted J trial fuel state).2 ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [counted, run]
  | succ t ih =>
    cases h : trial (select J state) with
    | cleared a => simp [counted, run, h]
    | blocked ranges =>
      obtain ⟨eq, ht⟩ := ih (double state ranges)
      simp [counted, run, h, eq, ht]

end Kintali.QuoteSearch
