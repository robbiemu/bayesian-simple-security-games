module

public import StochasticGames.SourceLinearization
import all StochasticGames.AverageFeasibility
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import all StochasticGames.Precision
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Precision for a simple stochastic game

For a threshold with denominator `b`, Section 3 tightens its complement by
`1 / (b * 3^(n+1))`. The comparison circuit then needs only the binary length
of that denominator plus `2*(n+1)` rounds. Both bounds depend on the input
before any branch or witness is chosen.
-/

@[expose] public section

namespace StochasticGames.SourcePrecision

open AverageFeasibility BoundedLinearProgram LinearFeasibilityGap Precision
open SourceRows SourceLinearization

def D (n b : ℕ) : ℕ := b * 3 ^ (n + 1)

def cutoff (n b : ℕ) (t : ℚ) : ℚ := 1 - t + 1 / (D n b : ℚ)

def depth (n b : ℕ) : ℕ := (D n b).size + 2 * (n + 1)

def gap (n b : ℕ) : ℚ := 1 / ((D n b : ℚ) * 4 ^ (n + 1))

theorem D_pos (n b : ℕ) (bpos : 0 < b) : 0 < D n b :=
  Nat.mul_pos bpos (pow_pos (by decide) _)

theorem clears_D {b : ℕ} {t : ℚ} (n : ℕ) (cleared : Clears b t) : Clears (D n b) t := by
  obtain ⟨z, hz⟩ := cleared
  refine ⟨3 ^ (n + 1) * z, ?_⟩
  simp only [D, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [← hz]
  ring

theorem cutoff_clears (n b : ℕ) (t : ℚ) (bpos : 0 < b) (cleared : Clears b t) :
    Clears (D n b) (cutoff n b t) := by
  have pos : (0 : ℚ) < D n b := by exact_mod_cast D_pos n b bpos
  have margin : Clears (D n b) (1 / (D n b : ℚ)) :=
    ⟨1, by rw [mul_div_cancel₀ _ pos.ne', Int.cast_one]⟩
  exact ((Clears.one _).sub (clears_D n cleared)).add margin

variable {n : ℕ}

/-- Tighten a positive strict margin while retaining the original selected rows. -/
theorem strengthen_selected
    (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (t : ℚ) (b : ℕ)
    (bpos : 0 < b) (cleared : Clears b t) {v : Fin n → ℝ}
    (branch : (base rows).Branch) (selected : Selected (base rows) branch v)
    (strict : 1 - (t : ℝ) < v s) :
    ∃ q : Fin n → ℚ, Selected (base rows) branch q ∧ cutoff n b t ≤ q s := by
  let p : ℚ := 1 - t
  have realP : (p : ℝ) = 1 - (t : ℝ) := by simp [p]
  let A := marginMatrix (base rows) branch s p
  let rhs := marginRhs (base rows) branch s p
  obtain ⟨c, rationalRhsEq, realRhsEq⟩ := cleared_rhs rhs b bpos
    (margin_rhs_cleared (base rows) branch s p ((Clears.one b).sub cleared) (base_cleared rows b))
  have realConstraints (y : Option (Fin n) → ℝ) :
      Feasible (RealStrictWitness.realMatrix A) (RealStrictWitness.realRhs c (b : ℚ)) y ↔
        Selected (base rows) branch (fun j => y (some j)) ∧ 0 ≤ y none ∧ y none ≤ 1 ∧
          (p : ℝ) + y none ≤ y (some s) := by
    rw [realRhsEq]
    exact margin_feasible_iff (base rows) branch s p y
  have bounded : Bounded (RealStrictWitness.realMatrix A) (RealStrictWitness.realRhs c (b : ℚ)) := by
    refine ⟨1, fun y hy i => ?_⟩
    obtain ⟨sel, lo, hi, _⟩ := (realConstraints y).1 hy
    cases i with
    | none => simpa [abs_of_nonneg lo] using hi
    | some j =>
      obtain ⟨lo, hi⟩ := box_of_hard sel.1 j
      simpa [abs_of_nonneg lo] using hi
  let m : ℝ := min 1 (v s - (p : ℝ))
  have mpos : 0 < m := lt_min zero_lt_one (sub_pos.2 (by rwa [realP]))
  let y (i : Option (Fin n)) := i.elim m v
  have feasible : Feasible (RealStrictWitness.realMatrix A) (RealStrictWitness.realRhs c (b : ℚ)) y := by
    apply (realConstraints y).2
    refine ⟨selected, mpos.le, min_le_left _ _, ?_⟩
    change (p : ℝ) + m ≤ v s
    linarith [show m ≤ v s - (p : ℝ) from min_le_right _ _]
  obtain ⟨z, feasibleZ, uniform⟩ :=
    RealStrictWitness.exists_uniform_margin_of_row_squares A c (b : ℚ) 3
      (by exact_mod_cast bpos) (by decide) (margin_row_squares (base rows) branch s p)
      bounded none feasible mpos
  rw [rationalRhsEq] at feasibleZ
  have rationalConstraints := (margin_feasible_iff (base rows) branch s p z).1
    (show Feasible (rationalMatrix A) (fun i => (rhs i : ℚ)) z from feasibleZ)
  obtain ⟨sel, _, _, threshold⟩ := rationalConstraints
  have margin : 1 / (D n b : ℚ) ≤ z none := by simpa [D] using uniform
  refine ⟨fun i => z (some i), sel, ?_⟩
  change p + 1 / (D n b : ℚ) ≤ z (some s)
  exact (add_le_add_right margin p).trans threshold

/-- A strict real certificate exists exactly when the tightened simultaneous
rows have a rational solution. The input denominator may be unreduced. -/
theorem strict_witness_iff
    (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (t : ℚ) (b : ℕ)
    (bpos : 0 < b) (cleared : Clears b t) :
    (∃ y : Fin n → ℝ, Source.DualFeasible rows y ∧ 1 - (t : ℝ) < y s) ↔
      ∃ q, (tightened rows s (cutoff n b t)).Exact q := by
  constructor
  · rintro ⟨v, valid, strict⟩
    obtain ⟨branch, selected⟩ :=
      (exact_iff_selected (base rows) v).1 ((exact_base_real_iff rows v).2 valid)
    obtain ⟨q, repaired, threshold⟩ :=
      strengthen_selected rows s t b bpos cleared branch selected strict
    exact ⟨q, (exact_rat_iff _ q).2 ((exact_tightened_iff rows s _ _).2
      ⟨(exact_iff_selected _ _).2 ⟨branch, repaired⟩, threshold⟩)⟩
  · rintro ⟨q, hq⟩
    obtain ⟨baseQ, threshold⟩ := (exact_tightened_iff rows s _ q).1 ((exact_rat_iff _ q).1 hq)
    refine ⟨fun i => (q i : ℝ), (exact_base_real_iff rows _).1 ((exact_cast_real _ q).2 baseQ), ?_⟩
    have dpos : (0 : ℚ) < (D n b : ℚ) := by exact_mod_cast D_pos n b bpos
    have strict : 1 - t < q s := (lt_add_of_pos_right _ (one_div_pos.mpr dpos)).trans_le threshold
    change 1 - (t : ℝ) < (q s : ℝ)
    exact_mod_cast strict

/-- The tightened rows have a real solution exactly when they have a rational one. -/
theorem tightened_real_iff_rational
    (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (t : ℚ) (b : ℕ)
    (bpos : 0 < b) (cleared : Clears b t) :
    (∃ y : Fin n → ℝ, SourceRows.Exact (tightened rows s (cutoff n b t)) y) ↔
      ∃ q, (tightened rows s (cutoff n b t)).Exact q := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨baseY, threshold⟩ := (exact_tightened_iff rows s _ y).1 hy
    apply (strict_witness_iff rows s t b bpos cleared).1
    refine ⟨y, (exact_base_real_iff rows y).1 baseY, ?_⟩
    have dpos : (0 : ℝ) < (D n b : ℝ) := by exact_mod_cast D_pos n b bpos
    exact (lt_add_of_pos_right _ (one_div_pos.mpr dpos)).trans_le (by simpa [cutoff] using threshold)
  · rintro ⟨q, hq⟩
    exact ⟨fun i => (q i : ℝ), (exact_cast_real _ q).2 ((exact_rat_iff _ q).1 hq)⟩

theorem gap_le_one (n b : ℕ) (bpos : 0 < b) : gap n b ≤ 1 := by
  have d : (1 : ℚ) ≤ (D n b : ℚ) := by exact_mod_cast D_pos n b bpos
  have denom : (1 : ℚ) ≤ (D n b : ℚ) * 4 ^ (n + 1) :=
    one_le_mul_of_one_le_of_one_le d (one_le_pow₀ (by decide))
  exact (div_le_iff₀ (zero_lt_one.trans_le denom)).2 (by simpa using denom)

private theorem relaxed_cast_real {ι : Type*} (system : System ι) (branch : system.Branch)
    (q : ι → ℚ) (slack : ℚ) :
    system.RelaxedOver branch (fun i => (q i : ℝ)) (slack : ℝ) ↔
      system.Relaxed branch q slack := by
  simp only [System.RelaxedOver, System.Relaxed, System.HardRows, System.AverageRows,
    Term.valueOver_ratCast]
  norm_cast

/-- H4, §3.2. Every original branch admitting a real relaxation with slack in
`[0,1]` has a rational minimizer among all such real relaxations. Its common
slack is zero or at least `1 / (D * 4^(n+1))`. -/
theorem tightened_minimum_slack
    (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (t : ℚ) (b : ℕ)
    (bpos : 0 < b) (cleared : Clears b t)
    (branch : (tightened rows s (cutoff n b t)).Branch)
    {x : Fin n → ℝ} {slack : ℝ} (lo : 0 ≤ slack) (hi : slack ≤ 1)
    (relaxed : (tightened rows s (cutoff n b t)).RelaxedOver branch x slack) :
    let sys := tightened rows s (cutoff n b t)
    ∃ (q : Fin n → ℚ) (ρ : ℚ), sys.Relaxed branch q ρ ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧
      (∀ (v : Fin n → ℝ) (e : ℝ), 0 ≤ e → e ≤ 1 → sys.RelaxedOver branch v e → (ρ : ℝ) ≤ e) ∧
      (ρ = 0 ∨ gap n b ≤ ρ) := by
  let sys := tightened rows s (cutoff n b t)
  let A := BranchLinearization.matrix sys branch
  let rhs := fun i => (BranchLinearization.rhs sys branch i : ℝ)
  have dpos : 0 < D n b := D_pos n b bpos
  have offsets := tightened_cleared rows s _ _ (cutoff_clears n b t bpos cleared)
  have denominator (r) : ∃ z : ℤ, (D n b : ℝ) * rhs r = z := by
    obtain ⟨z, hz⟩ := rhs_cleared sys branch offsets r
    exact ⟨z, by dsimp only [rhs]; exact_mod_cast hz⟩
  have norms (r) : Real.sqrt (∑ j, (A r j : ℝ)^2) ≤ 4 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by exact_mod_cast slack_row_squares sys branch r⟩
  have constraints (y : Option (Fin n) → ℝ) :
      Feasible (RealStrictWitness.realMatrix A) rhs y ↔
        sys.RelaxedOver branch (fun i => y (some i)) (y none) ∧
          0 ≤ y none ∧ y none ≤ 1 := BranchLinearization.feasible_over_iff sys branch y
  have bounded : Bounded (RealStrictWitness.realMatrix A) rhs := by
    refine ⟨1, fun y hy i => ?_⟩
    obtain ⟨sel, low, high⟩ := (constraints y).1 hy
    cases i with
    | none => simpa [abs_of_nonneg low] using high
    | some j =>
      have hard : Hard (base rows) (fun k => y (some k)) :=
        fun r hr => sel.1 r (List.mem_cons_of_mem _ hr)
      obtain ⟨lower, upper⟩ := box_of_hard hard j
      simpa [abs_of_nonneg lower] using upper
  let initial (i : Option (Fin n)) := i.elim slack x
  obtain ⟨m, hm, minimum⟩ := RealStrictWitness.exists_coordinate_minimum _ _ bounded none
    ((constraints initial).2 ⟨relaxed, lo, hi⟩)
  obtain ⟨q, feasibleQ, atMinimum, separation⟩ :=
    RealStrictWitness.exists_rational_extremal_coordinate A rhs (D n b) dpos 4 norms
      denominator bounded none m hm (Or.inl minimum)
  obtain ⟨holds, low, high⟩ := (constraints _).1 feasibleQ
  refine ⟨fun i => q (some i), q none, (relaxed_cast_real sys branch _ _).1 holds,
    by exact_mod_cast low, by exact_mod_cast high, ?_, ?_⟩
  · intro v e el eu admissible
    let y (i : Option (Fin n)) := i.elim e v
    exact atMinimum.le.trans (minimum y ((constraints y).2 ⟨admissible, el, eu⟩))
  · rcases low.eq_or_lt with zero | positive
    · left
      exact_mod_cast zero.symm
    · right
      have lower := separation (positive.trans_eq atMinimum)
      rw [← atMinimum] at lower
      have bound : (gap n b : ℝ) ≤ (q none : ℝ) := by simpa [gap] using lower
      exact_mod_cast bound

/-- A real slack smaller than the gap forces the attained minimum on that branch to be zero. -/
theorem tightened_real_gap
    (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (t : ℚ) (b : ℕ)
    (bpos : 0 < b) (cleared : Clears b t)
    (branch : (tightened rows s (cutoff n b t)).Branch) {x : Fin n → ℝ} {slack : ℝ}
    (low : 0 ≤ slack) (small : slack < (gap n b : ℝ))
    (relaxed : (tightened rows s (cutoff n b t)).RelaxedOver branch x slack) :
    ∃ q : Fin n → ℚ, (tightened rows s (cutoff n b t)).Relaxed branch q 0 := by
  have hi : slack ≤ 1 := small.le.trans (by exact_mod_cast gap_le_one n b bpos)
  obtain ⟨q, ρ, holds, _, _, minimum, zero | large⟩ :=
    tightened_minimum_slack rows s t b bpos cleared branch low hi relaxed
  · exact ⟨q, zero ▸ holds⟩
  · have lower : (gap n b : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast large
    exact False.elim ((not_lt_of_ge lower) ((minimum x slack low hi relaxed).trans_lt small))

/-- Rational relaxations are a special case of the real branch repair. -/
theorem tightened_gap
    (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (t : ℚ) (b : ℕ)
    (bpos : 0 < b) (cleared : Clears b t) :
    (tightened rows s (cutoff n b t)).HasGap (gap n b) := by
  rintro branch slack low small ⟨x, relaxed⟩
  exact tightened_real_gap rows s t b bpos cleared branch (by exact_mod_cast low)
    (by exact_mod_cast small) ((relaxed_cast_real _ branch x slack).2 relaxed)

theorem error_lt_gap (n b : ℕ) (bpos : 0 < b) :
    ShiftedComparisons.gapBound 1 (depth n b) / 2 < gap n b := by
  have bits : D n b < 2 ^ (D n b).size := Nat.size_le.mp le_rfl
  have bitsQ : (D n b : ℚ) < (2 : ℚ) ^ (D n b).size := by exact_mod_cast bits
  have dpos : (0 : ℚ) < D n b := by exact_mod_cast D_pos n b bpos
  have twoPowers : (2 : ℚ) ^ (2 * (n + 1)) = 4 ^ (n + 1) := by rw [pow_mul]; norm_num
  rw [ShiftedComparisons.gapBound_eq, depth, gap, div_div, pow_add, twoPowers]
  apply one_div_lt_one_div_of_lt (mul_pos dpos (pow_pos (by decide) _))
  have scaled := mul_lt_mul_of_pos_right bitsQ (pow_pos (by decide : (0 : ℚ) < 4) (n + 1))
  exact scaled.trans_le (le_mul_of_one_le_right (by positivity) (by decide))

/-- The explicit input depth preserves exact feasibility on the tightened system. -/
theorem exact_iff_compiled
    (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (t : ℚ) (b : ℕ)
    (bpos : 0 < b) (cleared : Clears b t) :
    (∃ q, (tightened rows s (cutoff n b t)).Exact q) ↔
      ∃ x, (tightened rows s (cutoff n b t)).Compiled 1 (depth n b) x :=
  System.exact_feasible_iff_compiled _ (by decide) (tightened_input_width rows s _)
    (tightened_gap rows s t b bpos cleared) _ (error_lt_gap n b bpos)

end StochasticGames.SourcePrecision
