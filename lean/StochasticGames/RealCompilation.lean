module

public import StochasticGames.ThresholdCompiler
import all StochasticGames.AtomEncoding
import all StochasticGames.AverageFeasibility
import all StochasticGames.ThresholdCompiler
import all StochasticGames.SourceRows
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Positivity

/-! # Proposition 4 over real labels

Every real exact witness extends by evaluating the gates. Conversely, every
real assignment satisfying the emitted rows gives a rational exact witness
on the same selected branch. Only the source labels have box constraints.
-/

@[expose] public section

namespace StochasticGames.RealCompilation

open AtomEncoding AverageFeasibility ShiftedComparisons ThresholdCompiler

variable {n : ℕ} (input : ThresholdInput n) (s : Fin n)

abbrev Wire := vars (system input s) (precision input)

/-- Real source coordinates, measured from the reference variable. -/
noncomputable def sourceLabels (v : Wire input s → ℝ) : Fin n → ℝ :=
  fun i => v (.source i) - v .reference

/-- Keep the given source coordinates and assign the actual comparator values. -/
noncomputable def evaluateGates (x : Fin n → ℝ) : Wire input s → ℝ :=
  let trace (i : Fin (system input s).averages.length) :=
    let row := (system input s).averages.get i
    evaluate 1 (row.first.valueOver x) (row.second.valueOver x)
  fun
  | .reference => 0
  | .source i => x i
  | .high i j => (trace i j.val).1
  | .low i j => (trace i j.val).2

/-- The forward witness claim keeps each real source coordinate verbatim. -/
theorem exact_extends_by_evaluation {x : Fin n → ℝ} (exactRows : SourceRows.Exact (system input s) x) :
    RowsHold (allAtoms (system input s) 1 (precision input)) (evaluateGates input s x) ∧
      sourceLabels input s (evaluateGates input s x) = x := by
  refine ⟨(allAtoms_hold_normalized _ _ _ _ rfl).2 ?_, by
    funext i
    simp [sourceLabels, evaluateGates]⟩
  obtain ⟨hard, maxima, averages⟩ := exactRows
  refine ⟨hard, maxima, fun i => ?_⟩
  let row := (system input s).averages.get i
  have inside := SourceRows.tightened_input_width_over input.rows.get s _ x hard row
    (List.get_mem _ i)
  have avg := averages row (List.get_mem _ i)
  let evaluation := evaluate 1 (row.first.valueOver x) (row.second.valueOver x)
  have traces : readTrace (evaluateGates input s x) i = fun j => evaluation j.val := by
    funext j
    rfl
  rw [traces, Rat.cast_one]
  change ValidTrace 1 (row.first.valueOver x) (row.second.valueOver x) (precision input)
      (fun j => evaluation j.val) ∧ row.lhs.valueOver x ≤ (evaluation (precision input)).1
  exact ⟨evaluation_is_validTrace _ _ _ _, avg.trans (upperMean_bounds inside _).1⟩

private theorem epsilon_cast :
    ((gapBound (1 : ℚ) (precision input) / 2 : ℚ) : ℝ) =
      gapBound (1 : ℝ) (precision input) / 2 := by
  simp only [gapBound_eq, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat]

/-- The reverse direction works for every supporting selection from the
original maxima. The auxiliary labels can be arbitrary reals. -/
theorem compiled_repairs_same_branch
    {raw : Wire input s → ℝ}
    (compiled : RowsHold (allAtoms (system input s) 1 (precision input)) raw)
    (branch : (system input s).Branch)
    (supports : ∀ row, row.val.lhs.valueOver (sourceLabels input s raw) ≤
      (branch row).val.valueOver (sourceLabels input s raw)) :
    ∃ q : Fin n → ℚ, (system input s).Relaxed branch q 0 := by
  let v i := raw i - raw .reference
  have normalized : v .reference = 0 := sub_self _
  obtain ⟨hard, _, gates⟩ := (allAtoms_hold_normalized (system input s) 1 (precision input) v
    normalized).1 (translated_preserves_rows _ _ _ compiled)
  let ε := gapBound (1 : ℝ) (precision input) / 2
  have nonneg : 0 ≤ ε := by
    unfold ε
    rw [gapBound_eq]
    positivity
  have smaller : ε < (SourcePrecision.gap n input.denominator : ℝ) := by
    rw [show ε = _ from (epsilon_cast input).symm]
    exact_mod_cast SourcePrecision.error_lt_gap n input.denominator input.denominator_pos
  apply SourcePrecision.tightened_real_gap input.rows.get s input.threshold input.denominator
    input.denominator_pos input.clears_threshold branch nonneg smaller
  refine ⟨hard, supports, ?_⟩
  intro row mem
  obtain ⟨i, rfl⟩ := List.get_of_mem mem
  have inside := SourceRows.tightened_input_width_over input.rows.get s _ (sourceLabels input s raw)
    hard _ (List.get_mem _ i)
  obtain ⟨valid, le⟩ := gates i
  have bound := trace_le_evaluation valid (Fin.last (precision input))
  rw [Rat.cast_one, Fin.val_last] at bound
  exact le.trans (bound.1.trans (upperMean_bounds inside (precision input)).2)

/-- The branch can be chosen by taking an attaining term in every original
right-hand maximum of the real compiled assignment. -/
theorem compiled_selects_attaining_branch
    {raw : Wire input s → ℝ}
    (compiled : RowsHold (allAtoms (system input s) 1 (precision input)) raw) :
    ∃ branch : (system input s).Branch,
      (∀ row t, t ∈ row.val.terms →
        t.valueOver (sourceLabels input s raw) ≤
          (branch row).val.valueOver (sourceLabels input s raw)) ∧
      ∃ q : Fin n → ℚ, (system input s).Relaxed branch q 0 := by
  classical
  let v i := raw i - raw .reference
  have normalized : v .reference = 0 := sub_self _
  obtain ⟨_, maxima, _⟩ := (allAtoms_hold_normalized (system input s) 1 (precision input) v
    normalized).1 (translated_preserves_rows _ _ _ compiled)
  have attaining (row : {row // row ∈ (system input s).maxima}) :
      ∃ t ∈ row.val.terms, ∀ u ∈ row.val.terms,
        u.valueOver (sourceLabels input s raw) ≤ t.valueOver (sourceLabels input s raw) := by
    obtain ⟨first, mem, _⟩ := maxima row.val row.property
    obtain ⟨t, tMem, greatest⟩ := Finset.exists_max_image row.val.terms.toFinset
      (fun u => u.valueOver (sourceLabels input s raw)) ⟨first, List.mem_toFinset.mpr mem⟩
    exact ⟨t, List.mem_toFinset.mp tMem, fun u uMem => greatest u (List.mem_toFinset.mpr uMem)⟩
  choose terms mem greatest using attaining
  let branch : (system input s).Branch := fun row => ⟨terms row, mem row⟩
  refine ⟨branch, greatest, compiled_repairs_same_branch input s compiled branch ?_⟩
  intro row
  obtain ⟨t, tMem, supported⟩ := maxima row.val row.property
  exact supported.trans (greatest row t tMem)

/-- Proposition 4 stated as an equivalence of feasibility over the reals. -/
theorem real_exact_iff_compiled :
    (∃ x : Fin n → ℝ, SourceRows.Exact (system input s) x) ↔
      ∃ v : Wire input s → ℝ, RowsHold (weightedRows input s) v := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨evaluateGates input s x, (exact_extends_by_evaluation input s hx).1⟩
  · rintro ⟨v, hv⟩
    obtain ⟨branch, _, q, repaired⟩ := compiled_selects_attaining_branch input s hv
    have exactRows := (system input s).zero_slack_is_exact repaired
    exact ⟨fun i => (q i : ℝ), (SourceRows.exact_cast_real _ q).2
      ((SourceRows.exact_rat_iff _ q).1 exactRows)⟩

/-- Scale the real atoms and floor each label. Multiples of the common
denominator are integral, so every selected inequality survives rounding. -/
theorem real_compiled_iff_integer (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) :
    (∃ v : Wire input s → ℝ, RowsHold (weightedRows input s) v) ↔
      ∃ z, IntegerAtoms.RowsHold (integerRows input s) z := by
  have scalePositive : 0 < integerScale input :=
    CompilationScale.scale_pos (SourcePrecision.D_pos n input.denominator input.denominator_pos)
  exact IntegerAtoms.feasible_over_iff_integer_at _ _ scalePositive
    (fun c hc => (weighted_offsets input s positive atMostOne c hc).1)

end StochasticGames.RealCompilation
