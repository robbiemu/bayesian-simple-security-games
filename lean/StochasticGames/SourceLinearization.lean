module

public import StochasticGames.SourceRows
public import StochasticGames.MaxAverageReduction
public import StochasticGames.RealStrictWitness
public import StochasticGames.Precision
import all StochasticGames.AverageFeasibility
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import all StochasticGames.MaxAverageReduction
import all StochasticGames.Precision
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # The two linear programs for a reachability certificate

The margin program keeps chance rows exact and adds a margin to the threshold.
The violation program keeps the tightened threshold exact and adds a common
slack to the chance rows. Their squared row lengths are at most 8 and 12,
respectively, including when several occurrences denote the same coordinate.
-/

@[expose] public section

namespace StochasticGames.SourceLinearization

open AverageFeasibility BranchLinearization BoundedLinearProgram LinearFeasibilityGap
open Precision SourceRows

variable {ι : Type*}

section Margins

variable {K : Type*} [Field K] [LinearOrder K]

def Selected (system : System ι) (branch : system.Branch) (x : ι → K) : Prop :=
  Hard system x ∧
    (∀ r : {r // r ∈ system.maxima}, eval x r.val.lhs ≤ eval x (branch r).val) ∧
    ∀ r ∈ system.averages, eval x r.lhs ≤ (eval x r.first + eval x r.second) / 2

theorem exact_iff_selected (system : System ι) (x : ι → K) :
    SourceRows.Exact system x ↔ ∃ branch : system.Branch, Selected system branch x := by
  constructor
  · rintro ⟨hard, maxima, avg⟩
    let branch : system.Branch := fun r =>
      ⟨Classical.choose (maxima _ r.property), (Classical.choose_spec (maxima _ r.property)).1⟩
    exact ⟨branch, hard, fun r => (Classical.choose_spec (maxima _ r.property)).2, avg⟩
  · rintro ⟨branch, hard, maxima, avg⟩
    refine ⟨hard, ?_, avg⟩
    intro r hr
    exact ⟨(branch ⟨r, hr⟩).val, (branch ⟨r, hr⟩).property, maxima ⟨r, hr⟩⟩

variable [DecidableEq ι]

/-- The extra row is the threshold with its margin; the original chance rows are exact. -/
def marginRow (system : System ι) (branch : system.Branch) (s : ι) (p : ℚ) :
    Option (Rows system) → LinearRow ι
  | none => ⟨fun j => -indicator (var s) j, 1, -p⟩
  | some (.inr (.inr (.inl i))) => { average (system.averages.get i) with slack := 0 }
  | some i => row system branch i

def marginMatrix (system : System ι) (branch : system.Branch) (s : ι) (p : ℚ) :
    Matrix (Option (Rows system)) (Option ι) ℤ :=
  fun i j => j.elim (marginRow system branch s p i).slack (marginRow system branch s p i).coeff

def marginRhs (system : System ι) (branch : system.Branch) (s : ι) (p : ℚ) :
    Option (Rows system) → ℚ := fun i => (marginRow system branch s p i).bound

variable [Fintype ι] [IsStrictOrderedRing K]

private def Holds (r : LinearRow ι) (y : Option ι → K) : Prop :=
  (r.slack : K) * y none + ∑ j, (r.coeff j : K) * y (some j) ≤ (r.bound : K)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem sum_indicator (a : Term ι) (x : ι → K) :
    ∑ j, (indicator a j : K) * x j = a.index.elim 0 x := by
  obtain ⟨idx, q⟩ := a
  cases idx with
  | none => simp [indicator]
  | some i => simp [indicator, ite_mul]

private theorem holds_difference (a b : Term ι) (y : Option ι → K) :
    Holds (difference a b) y ↔ eval (fun j => y (some j)) a ≤ eval (fun j => y (some j)) b := by
  simp only [Holds, difference, Int.cast_zero, zero_mul, zero_add, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib, sum_indicator, eval, Term.valueOver, Rat.cast_sub]
  constructor <;> intro hy <;> linarith

private theorem holds_exact_average (r : AverageRow ι) (y : Option ι → K) :
    Holds { average r with slack := 0 } y ↔
      eval (fun j => y (some j)) r.lhs ≤
        (eval (fun j => y (some j)) r.first + eval (fun j => y (some j)) r.second) / 2 := by
  simp only [Holds, average, Int.cast_zero, zero_mul, zero_add, Int.cast_ofNat, Int.cast_sub,
    Int.cast_mul, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, sum_indicator,
    eval, Term.valueOver, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  constructor <;> intro hy <;> linarith

private theorem holds_threshold (s : ι) (p : ℚ) (y : Option ι → K) :
    Holds ⟨fun j => -indicator (var s) j, 1, -p⟩ y ↔ (p : K) + y none ≤ y (some s) := by
  simp only [Holds, Int.cast_one, one_mul, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
    sum_indicator, var, Option.elim_some, Rat.cast_neg]
  constructor <;> intro hy <;> linarith

/-- The margin matrix imposes exactly the selected branch, the margin box,
and the single lower bound on the starting label. -/
theorem margin_feasible_iff (system : System ι) (branch : system.Branch) (s : ι)
    (p : ℚ) (y : Option ι → K) :
    Feasible ((marginMatrix system branch s p).map (fun z => (z : K)))
      (fun r => (marginRhs system branch s p r : K)) y ↔
      Selected system branch (fun j => y (some j)) ∧ 0 ≤ y none ∧ y none ≤ 1 ∧
        (p : K) + y none ≤ y (some s) := by
  have rowForm : Feasible ((marginMatrix system branch s p).map (fun z => (z : K)))
      (fun r => (marginRhs system branch s p r : K)) y ↔
      ∀ i, Holds (marginRow system branch s p i) y := by
    apply forall_congr'
    intro i
    simp [Holds, marginMatrix, marginRhs, Matrix.mulVec, dotProduct, Fintype.sum_option]
  have lower : Holds (slackBound false) y ↔ 0 ≤ y none := by simp [Holds, slackBound]
  have upper : Holds (slackBound true) y ↔ y none ≤ 1 := by simp [Holds, slackBound]
  rw [rowForm]
  constructor
  · intro allRows
    refine ⟨⟨?_, ?_, ?_⟩, lower.1 (allRows (some (.inr (.inr (.inr false))))),
      upper.1 (allRows (some (.inr (.inr (.inr true))))), (holds_threshold s p y).1 (allRows none)⟩
    · intro r hr
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (holds_difference _ _ y).1 (allRows (some (.inl i)))
    · rintro ⟨r, hr⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (holds_difference _ _ y).1 (allRows (some (.inr (.inl i))))
    · intro r hr
      obtain ⟨i, rfl⟩ := List.get_of_mem hr
      exact (holds_exact_average _ y).1 (allRows (some (.inr (.inr (.inl i)))))
  · rintro ⟨⟨hard, maxima, avg⟩, lo, hi, threshold⟩ i
    rcases i with _ | i
    · exact (holds_threshold s p y).2 threshold
    rcases i with i | i | i | b
    · exact (holds_difference _ _ y).2 (hard _ (List.get_mem _ i))
    · exact (holds_difference _ _ y).2 (maxima (atPosition system.maxima i))
    · exact (holds_exact_average _ y).2 (avg _ (List.get_mem _ i))
    · cases b with
      | false => exact lower.2 lo
      | true => exact upper.2 hi

end Margins

section RowLengths

variable [Fintype ι] [DecidableEq ι]

private theorem indicator_mass (a : Term ι) : ∑ j, indicator a j ≤ 1 := by
  obtain ⟨idx, q⟩ := a
  cases idx <;> simp [indicator]

private theorem difference_squares (a b : Term ι) : ∑ j, ((difference a b).coeff j) ^ 2 ≤ 2 := by
  have point (j : ι) : ((difference a b).coeff j) ^ 2 ≤ indicator a j + indicator b j := by
    by_cases ha : a.index = some j <;> by_cases hb : b.index = some j <;>
      norm_num [difference, indicator, ha, hb]
  calc
    _ ≤ ∑ j, (indicator a j + indicator b j) := Finset.sum_le_sum fun j _ => point j
    _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith [indicator_mass a, indicator_mass b]

private theorem average_squares (r : AverageRow ι) : ∑ j, ((average r).coeff j) ^ 2 ≤ 8 := by
  have point (j : ι) : ((average r).coeff j) ^ 2 ≤
      4 * indicator r.lhs j + 2 * indicator r.first j + 2 * indicator r.second j := by
    by_cases ha : r.lhs.index = some j <;> by_cases hb : r.first.index = some j <;>
      by_cases hc : r.second.index = some j <;> norm_num [average, indicator, ha, hb, hc]
  calc
    _ ≤ ∑ j, (4 * indicator r.lhs j + 2 * indicator r.first j + 2 * indicator r.second j) :=
      Finset.sum_le_sum fun j _ => point j
    _ ≤ 8 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      linarith [indicator_mass r.lhs, indicator_mass r.first, indicator_mass r.second]

theorem margin_row_squares (system : System ι) (branch : system.Branch) (s : ι) (p : ℚ)
    (i : Option (Rows system)) : ∑ j, (marginMatrix system branch s p i j) ^ 2 ≤ (3 : ℤ) ^ 2 := by
  have diff (a b : Term ι) : (0 : ℤ) ^ 2 + ∑ j, ((difference a b).coeff j) ^ 2 ≤ 3 ^ 2 := by
    linarith [difference_squares a b]
  have avg (r : AverageRow ι) : (0 : ℤ) ^ 2 + ∑ j, ((average r).coeff j) ^ 2 ≤ 3 ^ 2 := by
    linarith [average_squares r]
  rw [Fintype.sum_option]
  rcases i with _ | i
  · have single : ∑ j, (-indicator (var s) j) ^ 2 = (1 : ℤ) := by
      simp [indicator, var, ite_pow]
    change 1 ^ 2 + (∑ j, (-indicator (var s) j) ^ 2) ≤ (3 : ℤ) ^ 2
    rw [single]
    decide
  rcases i with i | i | i | b
  · exact diff _ _
  · exact diff _ _
  · exact avg _
  · cases b <;> norm_num [marginMatrix, marginRow, row, slackBound]

theorem slack_row_squares (system : System ι) (branch : system.Branch) (i : Rows system) :
    ∑ j, (matrix system branch i j) ^ 2 ≤ (4 : ℤ) ^ 2 := by
  have diff (a b : Term ι) : (0 : ℤ) ^ 2 + ∑ j, ((difference a b).coeff j) ^ 2 ≤ 4 ^ 2 := by
    linarith [difference_squares a b]
  have avg (r : AverageRow ι) : (-2 : ℤ) ^ 2 + ∑ j, ((average r).coeff j) ^ 2 ≤ 4 ^ 2 := by
    linarith [average_squares r]
  rw [Fintype.sum_option]
  rcases i with i | i | i | b
  · exact diff _ _
  · exact diff _ _
  · exact avg _
  · cases b <;> norm_num [matrix, row, slackBound]

end RowLengths

/-- A property of every term offset, including all unselected terms of maxima. -/
structure AllOffsets (P : ℚ → Prop) (system : System ι) : Prop where
  differences : ∀ r ∈ system.differences, P r.lhs.offset ∧ P r.rhs.offset
  maxima : ∀ r ∈ system.maxima, P r.lhs.offset ∧ ∀ t ∈ r.terms, P t.offset
  averages : ∀ r ∈ system.averages, P r.lhs.offset ∧ P r.first.offset ∧ P r.second.offset

abbrev ClearedOffsets (D : ℕ) := AllOffsets (ι := ι) (Clears D)

theorem AllOffsets.mem {P : ℚ → Prop} {system : System ι} (h : AllOffsets P system)
    (q : ℚ) (hq : q ∈ MaxAverageReduction.offsets system) : P q := by
  simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap] at hq
  rcases hq with (⟨r, hr, hq⟩ | ⟨r, hr, hq⟩) | ⟨r, hr, hq⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact (h.differences r hr).1
    · exact (h.differences r hr).2
  · rcases List.mem_cons.mp hq with rfl | hm
    · exact (h.maxima r hr).1
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
      exact (h.maxima r hr).2 t ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact (h.averages r hr).1
    · exact (h.averages r hr).2.1
    · exact (h.averages r hr).2.2

private theorem successor_has_offset {P : ℚ → Prop} (zero : P 0) (one : P 1) (j : Source.Position ι) :
    P (successor j).offset := by
  rcases j with i | b
  · exact zero
  · cases b with
    | false => exact one
    | true => exact zero

private theorem base_offsets {n : ℕ} (rows : Fin n → Source.Row (Fin n))
    {P : ℚ → Prop} (zero : P 0) (one : P 1) : AllOffsets P (base rows) := by
  constructor
  · intro r hr
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hr
    rcases List.mem_append.mp hi with boxMem | choiceMem
    · simp only [box, List.mem_cons, List.not_mem_nil, or_false] at boxMem
      rcases boxMem with rfl | rfl
      · exact ⟨zero, zero⟩
      · exact ⟨zero, one⟩
    · cases hi : rows i with
      | max head tail =>
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp (show r ∈ _ by simpa only [hi, choices] using choiceMem)
        exact ⟨zero, successor_has_offset zero one j⟩
      | min | chance => simp [hi, choices] at choiceMem
  · intro r hr
    obtain ⟨i, _, hm⟩ := List.mem_flatMap.mp hr
    cases hi : rows i with
    | min head tail =>
      simp only [hi, maxima, List.mem_singleton] at hm
      subst r
      refine ⟨zero, ?_⟩
      intro t ht
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ht
      exact successor_has_offset zero one j
    | max | chance => simp [hi, maxima] at hm
  · intro r hr
    obtain ⟨i, _, ha⟩ := List.mem_flatMap.mp hr
    cases hi : rows i with
    | chance left right =>
      simp only [hi, averages, List.mem_singleton] at ha
      subst r
      exact ⟨zero, successor_has_offset zero one left, successor_has_offset zero one right⟩
    | max | min => simp [hi, averages] at ha

private theorem tightened_offsets {n : ℕ} (rows : Fin n → Source.Row (Fin n)) (s : Fin n)
    (p : ℚ) {P : ℚ → Prop} (zero : P 0) (one : P 1) (threshold : P p) :
    AllOffsets P (tightened rows s p) := by
  have baseOffsets := base_offsets rows zero one
  refine ⟨?_, baseOffsets.maxima, baseOffsets.averages⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | member
  · exact ⟨threshold, zero⟩
  · exact baseOffsets.differences r member

theorem base_cleared {n : ℕ} (rows : Fin n → Source.Row (Fin n)) (D : ℕ) :
    ClearedOffsets D (base rows) := base_offsets rows (Clears.zero D) (Clears.one D)

theorem tightened_cleared {n : ℕ} (rows : Fin n → Source.Row (Fin n)) (s : Fin n)
    (p : ℚ) (D : ℕ) (cleared : Clears D p) : ClearedOffsets D (tightened rows s p) :=
  tightened_offsets rows s p (Clears.zero D) (Clears.one D) cleared

/-- Every literal read by the max-average compiler is zero, one, or the tightened cutoff. -/
theorem tightened_literal_offsets {n : ℕ} (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (p : ℚ) :
    ∀ q ∈ MaxAverageReduction.offsets (tightened rows s p), q = 0 ∨ q = 1 ∨ q = p :=
  (tightened_offsets rows s p (P := fun q => q = 0 ∨ q = 1 ∨ q = p)
    (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))).mem

theorem tightened_offset_clears {n : ℕ} (rows : Fin n → Source.Row (Fin n)) (s : Fin n)
    (p : ℚ) (D : ℕ) (cleared : Clears D p) :
    ∀ q ∈ MaxAverageReduction.offsets (tightened rows s p), Clears D q :=
  (tightened_cleared rows s p D cleared).mem

theorem rhs_cleared [DecidableEq ι] {D : ℕ} (system : System ι) (branch : system.Branch)
    (offsets : ClearedOffsets D system) (i : Rows system) : Clears D (rhs system branch i) := by
  rcases i with i | i | i | b
  · obtain ⟨a, b⟩ := offsets.differences _ (List.get_mem _ i)
    exact b.sub a
  · let r := atPosition system.maxima i
    obtain ⟨a, ts⟩ := offsets.maxima r.val r.property
    exact (ts _ (branch r).property).sub a
  · obtain ⟨a, b, c⟩ := offsets.averages _ (List.get_mem _ i)
    change Clears D (_ + _ - 2 * _)
    rw [two_mul]
    exact (b.add c).sub (a.add a)
  · cases b with
    | false => exact Clears.zero D
    | true => exact Clears.one D

theorem margin_rhs_cleared [DecidableEq ι] {D : ℕ} (system : System ι) (branch : system.Branch)
    (s : ι) (p : ℚ) (cleared : Clears D p) (offsets : ClearedOffsets D system)
    (i : Option (Rows system)) : Clears D (marginRhs system branch s p i) := by
  cases i with
  | none =>
    change Clears D (-p)
    simpa using (Clears.zero D).sub cleared
  | some i =>
    have h := rhs_cleared system branch offsets i
    rcases i with i | i | i | b <;> exact h

/-- A scale that clears each rational row produces the same integer right-hand
side in the real and rational versions of the program. -/
theorem cleared_rhs {κ : Type*} (p : κ → ℚ) (D : ℕ) (positive : 0 < D)
    (clears : ∀ i, Clears D (p i)) :
    ∃ b : κ → ℤ, rationalRhs b (D : ℚ) = p ∧
      RealStrictWitness.realRhs b (D : ℚ) = fun i => (p i : ℝ) := by
  choose b hb using clears
  have Dpos : (0 : ℚ) < (D : ℚ) := by exact_mod_cast positive
  have rational (i) : (b i : ℚ) / (D : ℚ) = p i := by
    apply (div_eq_iff Dpos.ne').2
    simpa [mul_comm] using (hb i).symm
  refine ⟨b, funext rational, ?_⟩
  funext i
  change (b i : ℝ) / ((D : ℚ) : ℝ) = (p i : ℝ)
  exact_mod_cast rational i

end StochasticGames.SourceLinearization
