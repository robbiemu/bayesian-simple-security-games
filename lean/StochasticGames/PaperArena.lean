module

public import StochasticGames.ArenaRepresentation
public import StochasticGames.ThresholdReduction
import all StochasticGames.AtomEncoding
import all StochasticGames.IntegerAtoms
import all StochasticGames.SourceRows

/-! # The explicit arena of Section 5

The box and threshold rows refer to the origin. Player moves and the first
gates refer to the named Win and Lose variables. The later gate rows use the
same shared comparison circuit as the executable compiler. Pin substitution
recovers the compiler's exact row list, including term and row order.
-/

public section
namespace StochasticGames.PaperArena

open AtomEncoding AverageFeasibility ArenaRepresentation

variable {ι ν : Type*} {a r n : ℕ}

private def keepSignal (t : Signal ν) : Signal (Named ν) := (.inl t.1, t.2)

private def keepAtom (row : Atom ν) : Atom (Named ν) :=
  ⟨.inl row.lhs, row.terms.map keepSignal⟩

private theorem collapse_inl (o v : ν) (offset : ℚ) :
    collapseSignal o (.inl v, offset) = (v, offset) := by
  simp [collapseSignal, collapse]

private theorem collapse_keepSignal (o : ν) (t : Signal ν) :
    collapseSignal o (keepSignal t) = t := by
  cases t
  simp only [keepSignal, collapse_inl]

private theorem eliminate_keepAtom (o : ν) (row : Atom ν) :
    eliminate o (keepAtom row) = row := by
  cases row
  simp [eliminate, fromSignals, keepAtom, keepSignal, collapseSignal, collapse,
    List.map_map, Function.comp_def]

private theorem eliminate_keptRows (o : ν) (xs : List (Atom ν)) :
    (xs.map keepAtom).map (eliminate o) = xs := by
  simp [List.map_map, Function.comp_def, eliminate_keepAtom]

/-- A move's literal successor becomes a named terminal, with zero offset. -/
def successorSignal (t : Term ι) : Signal (Named (Var ι a r)) :=
  match t.index with
  | some i => (.inl (.source i), t.offset)
  | none =>
    if t.offset = 0 then (.inr true, 0)
    else if t.offset = 1 then (.inr false, 0)
    else (.inl .reference, t.offset)

theorem successorSignal_at_position (p : Source.Position ι) :
    successorSignal (a := a) (r := r) (SourceRows.successor p) =
      match p with
      | .inl i => (.inl (.source i), 0)
      | .inr b => (.inr b, 0) := by
  rcases p with i | (_ | _) <;> simp [successorSignal, SourceRows.successor,
    SourceRows.var, SourceRows.literal]

private theorem collapse_successorSignal (t : Term ι) :
    collapseSignal .reference (successorSignal t : Signal (Named (Var ι a r))) =
      sourceSignal t := by
  obtain ⟨idx, q⟩ := t
  cases idx with
  | some i => simp [successorSignal, sourceSignal, collapseSignal, collapse]
  | none =>
    by_cases zero : q = 0
    · simp [successorSignal, sourceSignal, collapseSignal, collapse, zero]
    by_cases one : q = 1
    · simp [successorSignal, sourceSignal, collapseSignal, collapse, one]
    · simp [successorSignal, sourceSignal, collapseSignal, collapse, zero, one]

private def difference (row : DifferenceRow ι) : Atom (Var ι a r) :=
  fromSignals (sourceSignal row.lhs) [sourceSignal row.rhs]

private def move (row : DifferenceRow ι) : Atom (Named (Var ι a r)) :=
  fromSignals (keepSignal (sourceSignal row.lhs)) [successorSignal row.rhs]

private def maximum (row : MaxRow ι) : Atom (Named (Var ι a r)) :=
  fromSignals (keepSignal (sourceSignal row.lhs)) (row.terms.map successorSignal)

private def circuit (i : Fin a) (row : AverageRow ι) : List (Atom (Named (Var ι a r))) :=
  comparison (.inl (.high i 0)) (.inl (.low i 0)) (successorSignal row.first)
    (successorSignal row.second) ++
    ((List.finRange r).flatMap (roundRows 1 i)).map keepAtom ++ [keepAtom (finalRow i row)]

private theorem move_eliminates (row : DifferenceRow ι) :
    eliminate .reference (move row : Atom (Named (Var ι a r))) = difference row := by
  simp only [move, difference, eliminate_fromSignals, collapse_keepSignal, List.map_cons,
    List.map_nil, collapse_successorSignal]

private theorem maximum_eliminates (row : MaxRow ι) :
    eliminate .reference (maximum row : Atom (Named (Var ι a r))) =
      fromSignals (sourceSignal row.lhs) (row.terms.map sourceSignal) := by
  simp only [maximum, eliminate_fromSignals, collapse_keepSignal, List.map_map,
    Function.comp_def, collapse_successorSignal]

private theorem circuit_eliminates (i : Fin a) (row : AverageRow ι) :
    (circuit (r := r) i row).map (eliminate .reference) = averageAtoms 1 i row := by
  simp only [circuit, averageAtoms, initialRows, comparison, List.map_append, List.map_cons,
    List.map_nil, eliminate_fromSignals, collapse_inl, collapse_successorSignal,
    eliminate_keepAtom, eliminate_keptRows]

/-- The named body before adjoining the four terminal pins. -/
private def body (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (cutoff : ℚ) (r : ℕ) :
    List (Atom (Named (vars (SourceRows.tightened rows s cutoff) r))) :=
  let system := SourceRows.tightened rows s cutoff
  (keepAtom (difference ⟨SourceRows.literal cutoff, SourceRows.var s⟩) ::
    (List.finRange n).flatMap (fun i =>
      (SourceRows.box i).map (fun row => keepAtom (difference row)) ++
        (SourceRows.choices i (rows i)).map move)) ++
    system.maxima.map maximum ++
    (List.finRange system.averages.length).flatMap (fun i => circuit i (system.averages.get i))

private theorem body_eliminates (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (cutoff : ℚ) (r : ℕ) :
    (body rows s cutoff r).map (eliminate .reference) =
      allAtoms (SourceRows.tightened rows s cutoff) 1 r := by
  rw [body, allAtoms]
  simp only [List.map_append, List.map_cons, List.map_flatMap, List.map_map,
    Function.comp_def, eliminate_keepAtom, move_eliminates, maximum_eliminates,
    circuit_eliminates, difference]
  simp only [SourceRows.tightened, SourceRows.base, List.map_cons, List.map_append, List.map_flatMap]
  rfl

variable (input : ThresholdInput n) (s : Fin n)

def weightedBody : List (Atom (Named (ThresholdCompiler.Variables input s))) :=
  body input.rows.get s (SourcePrecision.cutoff n input.denominator input.threshold)
    (ThresholdCompiler.precision input)

theorem weightedBody_eliminates :
    (weightedBody input s).map (eliminate .reference) = ThresholdCompiler.weightedRows input s :=
  body_eliminates _ _ _ _

theorem weighted_body_feasible (x : ThresholdCompiler.Variables input s → ℝ) :
    AtomEncoding.RowsHold (ThresholdCompiler.weightedRows input s) x ↔
      ∃ y : Named (ThresholdCompiler.Variables input s) → ℝ,
        (∀ i, y (.inl i) = x i) ∧ AtomEncoding.RowsHold (atomPins .reference ++ weightedBody input s) y := by
  rw [← weightedBody_eliminates input s]
  exact eliminate_rows_iff .reference _ x

/-- Section 5's rows with terminal pins, scaled by its (Q), and its
tautological rows at missing left sides. Both owner settings use this
arena's own vertex count. -/
def table (swap : Bool) : ArenaEncoding.Table :=
  let Q := ThresholdCompiler.integerScale input
  let listing := namedListing (ThresholdCompiler.listing input s)
  let rows := IntegerAtoms.encodeAt Q (atomPins .reference ++ weightedBody input s)
  ArenaEncoding.table listing (withIdleRows listing rows) swap

theorem table_checked (swap : Bool) :
    (table input s swap).Valid ∧ ((table input s swap).Nonnegative ↔
      (ArenaEncoding.table (ThresholdCompiler.listing input s) (ThresholdCompiler.integerRows input s)
        swap).Nonnegative) := by
  let Q := ThresholdCompiler.integerScale input
  let rows := IntegerAtoms.encodeAt Q (weightedBody input s)
  let _ : Nonempty (ThresholdCompiler.Variables input s) := ⟨.reference⟩
  have substituted : rows.map (eliminateInt .reference Q) = ThresholdCompiler.integerRows input s := by
    rw [← encode_eliminate, weightedBody_eliminates]
    rfl
  have terms : HasTerms (ThresholdCompiler.integerRows input s) := by
    intro row mem
    obtain ⟨i, rfl⟩ := List.get_of_mem mem
    exact CompilationCounts.encoded_tightened_terms_pos _ _ _ _ _ _ i
  simp only [table, encode_pinned_body]
  exact explicit_table_checked (Var.reference : ThresholdCompiler.Variables input s)
    Q (ThresholdCompiler.listing input s) rows _
    substituted terms swap

/-- Theorem 1 for the paper's arena in the nontrivial case. -/
theorem table_correct (start : input.start = .inl s) (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) :
    (table input s true).Valid ∧ ((input.threshold : ℝ) ≤ (Source.value input.rows.get (.inl s) : ℝ) ↔
      (table input s true).Nonnegative) := by
  have notAbove : ¬ (input.denominator : ℤ) < input.numerator :=
    fun above => (not_lt_of_ge atMostOne) (input.one_lt_threshold_iff.mpr above)
  have compact : (input.threshold : ℝ) ≤ (Source.value input.rows.get (.inl s) : ℝ) ↔
      (ThresholdCompiler.table input s).Nonnegative := by
    simpa only [ThresholdReduction.compile, start, ite_eq_right (not_le.mpr positive),
      ite_eq_right notAbove] using ThresholdReduction.compile_correct input
  obtain ⟨valid, same⟩ := table_checked input s true
  exact ⟨valid, compact.trans same.symm⟩

end StochasticGames.PaperArena
