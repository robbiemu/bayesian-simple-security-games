module

public import StochasticGames.SourceGame
public import StochasticGames.AverageFeasibility
import all StochasticGames.SourceGame
import all StochasticGames.AverageFeasibility
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Linarith

/-! # Inequalities of a simple stochastic game

The rows use the complemented labels from Section 2. Terminal labels are literals,
so neither terminal is counted among the variables of the linear programs.
-/

@[expose] public section

namespace StochasticGames.SourceRows

open AverageFeasibility Source

variable {ι : Type*}

def var (i : ι) : Term ι := ⟨some i, 0⟩

def literal (q : ℚ) : Term ι := ⟨none, q⟩

def successor : Position ι → Term ι
  | .inl i => var i
  | .inr true => literal 0
  | .inr false => literal 1

def box (i : ι) : List (DifferenceRow ι) :=
  [⟨literal 0, var i⟩, ⟨var i, literal 1⟩]

def choices (i : ι) : Row ι → List (DifferenceRow ι)
  | .max head tail => (head :: tail).map fun j => ⟨var i, successor j⟩
  | _ => []

def maxima (i : ι) : Row ι → List (MaxRow ι)
  | .min head tail => [⟨var i, (head :: tail).map successor⟩]
  | _ => []

def averages (i : ι) : Row ι → List (AverageRow ι)
  | .chance left right => [⟨var i, successor left, successor right⟩]
  | _ => []

def base {n : ℕ} (rows : Fin n → Row (Fin n)) : System (Fin n) where
  differences := (List.finRange n).flatMap fun i => box i ++ choices i (rows i)
  maxima := (List.finRange n).flatMap fun i => maxima i (rows i)
  averages := (List.finRange n).flatMap fun i => averages i (rows i)

def tightened {n : ℕ} (rows : Fin n → Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    System (Fin n) :=
  { base rows with differences := ⟨literal cutoff, var s⟩ :: (base rows).differences }

section Scalar

variable {K : Type*} [Field K]

def eval (x : ι → K) (t : Term ι) : K := t.valueOver x

@[simp] theorem eval_var (x : ι → K) (i : ι) : eval x (var i) = x i := by
  simp [eval, Term.valueOver, var]

@[simp] theorem eval_literal (x : ι → K) (q : ℚ) : eval x (literal q) = (q : K) := by
  simp [eval, Term.valueOver, literal]

variable [LinearOrder K]

def Hard (system : System ι) (x : ι → K) : Prop :=
  ∀ row ∈ system.differences, eval x row.lhs ≤ eval x row.rhs

def Exact (system : System ι) (x : ι → K) : Prop :=
  Hard system x ∧
  (∀ row ∈ system.maxima, ∃ t ∈ row.terms, eval x row.lhs ≤ eval x t) ∧
  (∀ row ∈ system.averages,
    eval x row.lhs ≤ (eval x row.first + eval x row.second) / 2)

def InCube (x : ι → K) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 1

theorem box_of_hard {n : ℕ} {rows : Fin n → Row (Fin n)} {x : Fin n → K}
    (hard : Hard (base rows) x) : InCube x := by
  intro i
  have member (r : DifferenceRow (Fin n)) (hr : r ∈ box i) :
      r ∈ (base rows).differences :=
    List.mem_flatMap.mpr ⟨i, by simp, List.mem_append_left _ hr⟩
  exact ⟨by simpa using hard _ (member ⟨literal 0, var i⟩ (by simp [box])),
    by simpa using hard _ (member ⟨var i, literal 1⟩ (by simp [box]))⟩

theorem exact_tightened_iff {n : ℕ} (rows : Fin n → Row (Fin n)) (s : Fin n)
    (cutoff : ℚ) (x : Fin n → K) :
    Exact (tightened rows s cutoff) x ↔ Exact (base rows) x ∧ (cutoff : K) ≤ x s := by
  simp only [Exact, Hard, tightened, List.forall_mem_cons, eval_literal, eval_var]
  tauto

variable [IsStrictOrderedRing K]

theorem term_in_cube {x : ι → K} (hx : InCube x) (j : Position ι) :
    0 ≤ eval x (successor j) ∧ eval x (successor j) ≤ 1 := by
  rcases j with i | b
  · simpa [successor] using hx i
  · cases b <;> simp [successor, zero_le_one]

end Scalar

theorem exact_rat_iff (system : System ι) (x : ι → ℚ) :
    system.Exact x ↔ Exact system x := by
  simp [System.Exact, System.HardRows, System.MaxRows, System.AverageRows, Exact, Hard,
    eval, Term.value]

theorem eval_successor_real (y : ι → ℝ) (j : Position ι) :
    eval y (successor j) = dualLabel y j := by
  rcases j with i | b
  · simp [successor, dualLabel]
  · cases b <;> simp [successor, dualLabel]

private theorem real_choices_iff (i : ι) (head : Position ι) (tail : List (Position ι))
    (y : ι → ℝ) :
    (∀ r ∈ choices i (.max head tail), eval y r.lhs ≤ eval y r.rhs) ↔
      (Row.max head tail).DualConstraint y i := by
  simp only [choices, List.forall_mem_map, eval_var, eval_successor_real, Row.DualConstraint]

private theorem real_maxima_iff (i : ι) (head : Position ι) (tail : List (Position ι))
    (y : ι → ℝ) :
    (∀ r ∈ maxima i (.min head tail), ∃ a ∈ r.terms, eval y r.lhs ≤ eval y a) ↔
      (Row.min head tail).DualConstraint y i := by
  simp only [maxima, List.forall_mem_singleton, eval_var, Row.DualConstraint, List.mem_map,
    exists_exists_and_eq_and, eval_successor_real]

theorem exact_base_real_iff {n : ℕ} (rows : Fin n → Row (Fin n)) (y : Fin n → ℝ) :
    Exact (base rows) y ↔ DualFeasible rows y := by
  unfold Exact Hard base DualFeasible
  simp only [List.forall_mem_flatMap, List.mem_finRange, true_implies]
  constructor
  · rintro ⟨hard, maxRows, avRows⟩
    refine ⟨box_of_hard (rows := rows) (fun r hr => ?_), ?_⟩
    · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hr
      exact hard i r hi
    · intro i
      specialize hard i
      specialize maxRows i
      specialize avRows i
      cases h : rows i with
      | max _ _ =>
        rw [h] at hard
        exact (real_choices_iff _ _ _ _).mp (List.forall_mem_append.mp hard).2
      | min _ _ =>
        rw [h] at maxRows
        exact (real_maxima_iff _ _ _ _).mp maxRows
      | chance left right =>
        rw [h] at avRows
        simpa [averages, eval_successor_real, Row.DualConstraint, h] using avRows
  · rintro ⟨cube, localRows⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi := localRows i
      rw [List.forall_mem_append]
      refine ⟨by simpa [box] using cube i, ?_⟩
      cases h : rows i with
      | max _ _ =>
        exact (real_choices_iff _ _ _ _).mpr (by rwa [h] at hi)
      | min | chance => simp [choices]
    · intro i
      have hi := localRows i
      cases h : rows i with
      | min _ _ =>
        exact (real_maxima_iff _ _ _ _).mpr (by rwa [h] at hi)
      | max | chance => simp [maxima]
    · intro i
      have hi := localRows i
      cases h : rows i with
      | chance left right =>
        simpa [averages, eval_successor_real, Row.DualConstraint, h] using hi
      | max | min => simp [averages]

theorem exact_cast_real (system : System ι) (x : ι → ℚ) :
    Exact system (fun i => (x i : ℝ)) ↔ Exact system x := by
  have cast_eval (t : Term ι) :
      eval (fun i => (x i : ℝ)) t = ((eval (K := ℚ) x t : ℚ) : ℝ) :=
    t.valueOver_ratCast x
  have cast_average (a b : ℚ) :
      (((a + b) / 2 : ℚ) : ℝ) = ((a : ℝ) + (b : ℝ)) / 2 := by
    simp
  simp only [Exact, Hard, cast_eval, ← cast_average, Rat.cast_le]

theorem tightened_bounded {n : ℕ} (rows : Fin n → Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    ∃ B : ℚ, ∀ x, (tightened rows s cutoff).HardRows x → ∀ i, |x i| ≤ B := by
  use 1
  intro x hx i
  have h : Hard (base rows) x :=
    fun r hr => hx r (List.mem_cons_of_mem _ hr)
  obtain ⟨lo, hi⟩ := box_of_hard h i
  simpa [abs_of_nonneg lo] using hi

theorem tightened_input_width_over {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n : ℕ} (rows : Fin n → Row (Fin n)) (s : Fin n)
    (cutoff : ℚ) (x : Fin n → K) (hx : Hard (tightened rows s cutoff) x)
    (r : AverageRow (Fin n)) (hr : r ∈ (tightened rows s cutoff).averages) :
    |eval x r.first - eval x r.second| ≤ 1 := by
  have hard : Hard (base rows) x := fun r hr => hx r (List.mem_cons_of_mem _ hr)
  have cube := box_of_hard hard
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hr
  cases h : rows i with
  | max | min => simp [h, averages] at hi
  | chance left right =>
    simp only [h, averages, List.mem_singleton] at hi
    subst r
    have ⟨al, ah⟩ := term_in_cube cube left
    have ⟨bl, bh⟩ := term_in_cube cube right
    change |eval x (successor left) - eval x (successor right)| ≤ 1
    rw [abs_le]
    constructor <;> linarith

theorem tightened_input_width {n : ℕ} (rows : Fin n → Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    (tightened rows s cutoff).InputsBounded 1 :=
  tightened_input_width_over rows s cutoff

end StochasticGames.SourceRows
