module

public import Kintali.ExactRecovery.Matrix
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 2, uniform exact recovery

The normalized attack masses bound every column total by one. A positive
budget forces a target with positive coverage and an upper pressure bound on
the threshold. With the residual and the other coordinates bounded, a spanning
set of tight rows gives the Cramer gap. The elementary determinant bound
n! C^n ≤ (n C)^n gives exactly the integer height chosen in the paper.
-/

open scoped BigOperators
open StochasticGames BoundedLinearProgram LinearFeasibilityGap

@[expose] public section

namespace Kintali.ExactRecovery

variable {I J : Type*} [Fintype I] [Fintype J] {g : Game I J} {p : Pattern I J}

private theorem bounded_coordinates {x : J → ℚ} {q : I → J → ℚ} {t e : ℚ}
    (h : Relaxed g p x q t e) (priorSum : ∑ i, g.prior i = 1)
    (gain : ∀ j, 0 ≤ g.gain j) (budget : 0 < g.resources) :
    ∀ v, |vector x q t e v| ≤ 1 + ∑ j, g.gain j := by
  classical
  have row (i : I) (j : J) : q i j ≤ g.prior i :=
    (Finset.single_le_sum (fun k _ => h.nonneg i k) (Finset.mem_univ j)).trans_eq (h.row_sum i)
  have column (j : J) : (∑ i, q i j) ≤ 1 := (Finset.sum_le_sum (fun i _ => row i j)).trans_eq priorSum
  have total : 0 ≤ ∑ j, g.gain j := Finset.sum_nonneg (fun j _ => gain j)
  have one : 1 ≤ 1 + ∑ j, g.gain j := by linarith
  have positive : ∃ j, 0 < x j := by
    by_contra! hn
    have hz : (∑ j, x j) ≤ 0 := Finset.sum_nonpos (fun j _ => hn j)
    rw [h.budget] at hz
    exact (not_le_of_gt (by exact_mod_cast budget : (0 : ℚ) < g.resources)) hz
  obtain ⟨j, hj⟩ := positive
  have pressure : g.pressure q j ≤ ∑ k, g.gain k := calc
    _ ≤ g.gain j := by simpa [Game.pressure] using mul_le_mul_of_nonneg_right (column j) (gain j)
    _ ≤ _ := Finset.single_le_sum (fun k _ => gain k) (Finset.mem_univ j)
  have threshold := h.pressure_ge j (fun hs => hj.ne' (h.lower_coverage j hs))
  intro v
  rcases v with ⟨i,k⟩ | k | b
  · rw [vector, abs_of_nonneg (h.nonneg i k)]
    exact ((Finset.single_le_sum (fun i _ => h.nonneg i k) (Finset.mem_univ i)).trans (column k)).trans one
  · rw [vector, abs_of_nonneg (h.coverage_bounds k).1]
    exact (h.coverage_bounds k).2.trans one
  · cases b
    · rw [vector, abs_of_nonneg h.threshold_nonneg]
      linarith [h.residual_bounds.2]
    · rw [vector, abs_of_nonneg h.residual_bounds.1]
      exact h.residual_bounds.2.trans one

theorem determinantBound_le_height (g : Game I J) :
    determinantBound (Variable I J) (2 * atomBound g) ≤ (height g : ℚ) := by
  let n := Fintype.card (Variable I J)
  have factorial : (n.factorial : ℚ) ≤ (n : ℚ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have C : ((2 * atomBound g : ℤ) : ℚ) = (2 * denominator g * magnitude g : ℕ) := by
    simp [atomBound]
    ring
  let c := 2 * denominator g * magnitude g
  change (n.factorial : ℚ) * ((2 * atomBound g : ℤ) : ℚ)^n ≤ ((n * c)^n : ℕ)
  rw [C, Nat.cast_pow, Nat.cast_mul n c, mul_pow]
  exact mul_le_mul_of_nonneg_right factorial (pow_nonneg (Nat.cast_nonneg c) n)

/-- Any square row selection has determinant bounded by the game height,
including selections with repeated or dependent rows. -/
theorem determinant_le_height [DecidableEq I] [DecidableEq J]
    (g : Game I J) (p : Pattern I J) (rows : Variable I J → Row I J) :
    |(((matrix g p).submatrix rows id).det : ℚ)| ≤ (height g : ℚ) := by
  apply le_trans _ (determinantBound_le_height g)
  unfold determinantBound
  exact_mod_cast DeterminantGap.det_abs_le_of_entries ((matrix g p).submatrix rows id) _
    (fun i j => matrix_bound g p (rows i) j)

/-- Lemma 2. The height is calculated exclusively from game data and applies
simultaneously to every marked pattern. All returned coordinates are rational. -/
theorem recover (g : Game I J) (p : Pattern I J) (priorSum : ∑ i, g.prior i = 1)
    (gain : ∀ j, 0 ≤ g.gain j) (budget : 0 < g.resources)
    {x : J → ℚ} {q : I → J → ℚ} {t e : ℚ} (h : Relaxed g p x q t e)
    (small : e < 1 / (height g : ℚ)) : ∃ x' q' t', Relaxed g p x' q' t' 0 := by
  classical
  have bounded : Bounded (rationalMatrix (matrix g p)) (rationalRhs (rhs g p) 1) := by
    refine ⟨1 + ∑ j, g.gain j, fun y hy v => ?_⟩
    have hc := bounded_coordinates ((feasible_iff g p y).mp hy) priorSum gain budget v
    rwa [vector_eta y] at hc
  have positive : (0 : ℚ) < height g := by exact_mod_cast height_pos g
  let residual : Variable I J := .inr (.inr true)
  obtain ⟨y, feasible, smaller, gap⟩ := exists_point_with_gap_of_det_bound
    (matrix g p) (rhs g p) 1 (height g : ℚ) (by norm_num) positive (determinant_le_height g p)
    bounded (LinearMap.proj residual) ((feasible_vector_iff g p x q t e).mpr h)
  have yh := (feasible_iff g p y).mp feasible
  have zero : residualOf y = 0 := by
    apply le_antisymm _ yh.residual_bounds.1
    by_contra! pos
    have lower := gap residual pos
    have upper : y residual ≤ e := smaller
    rw [one_mul] at lower
    exact (not_lt_of_ge lower) (upper.trans_lt small)
  exact ⟨_, _, _, zero ▸ yh⟩

end Kintali.ExactRecovery
