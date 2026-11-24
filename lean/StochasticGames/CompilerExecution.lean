module

public import StochasticGames.CostedBinary
public import StochasticGames.CostedRows
public import StochasticGames.CostedArena
public import StochasticGames.ReductionComplexity
import all StochasticGames.ThresholdCompiler
import all StochasticGames.ThresholdInput
import Mathlib.Tactic.NormNum

/-! # Execute the binary reduction within a polynomial bit budget

The parser, comparison circuits, numeric arena, and serializer are sequenced
in the same run. The graph branch computes its own depth, scale, and vertex
count. Erasure connects this encoder to the threshold and output-size proofs.
-/

public section

namespace StochasticGames.CompilerExecution

open ArenaEncoding AtomEncoding BinaryEncoding CompilationCost CompilerRun IntegerAtoms

variable {n : ℕ}

/-! ## Graph construction and erasure -/

private def emitTyped (a r : ℕ) (rows : List (IntAtom (Var (Fin n) a r))) : Run Table := do
  let vars ← CostedArena.variableItems n a r
  let labelWidth ← CostedArena.labelWidthRun n a r
  CostedArena.emit labelWidth vars rows

private theorem emitTyped_value (a r : ℕ) (rows : List (IntAtom (Var (Fin n) a r))) :
    (emitTyped a r rows).value = ArenaEncoding.table (compilerVariables n a r) rows true := by
  rw [emitTyped, Run.bind_value, Run.bind_value, CostedArena.labelWidthRun_value,
    CostedArena.variableItems_value, CostedArena.emit_value]

private def emitIndexed (input : ThresholdInput n) (s : Fin n) (a r : ℕ)
    (ha : a = (ThresholdCompiler.system input s).averages.length)
    (hr : r = ThresholdCompiler.precision input)
    (rows : List (IntAtom (ThresholdCompiler.Variables input s))) : Run Table :=
  let varEq := congrArg₂ (Var (Fin n)) ha hr
  let typedRows := cast (congrArg (fun ν : Type => List (IntAtom ν)) varEq.symm) rows
  emitTyped a r typedRows

private theorem emitIndexed_value (input : ThresholdInput n) (s : Fin n) (a r : ℕ)
    (ha : a = (ThresholdCompiler.system input s).averages.length)
    (hr : r = ThresholdCompiler.precision input)
    (rows : List (IntAtom (ThresholdCompiler.Variables input s))) :
    (emitIndexed input s a r ha hr rows).value =
      ArenaEncoding.table (ThresholdCompiler.listing input s) rows true := by
  subst a r
  exact emitTyped_value _ _ rows

private def emitPrepared (input : ThresholdInput n) (s : Fin n)
    (p : CostedRows.Prepared input s) : Run Table :=
  emitIndexed input s p.count p.rounds p.count_eq p.rounds_eq p.rows

private theorem emitPrepared_value (input : ThresholdInput n) (s : Fin n)
    (p : CostedRows.Prepared input s) :
    (emitPrepared input s p).value = ArenaEncoding.table (ThresholdCompiler.listing input s) p.rows true :=
  emitIndexed_value input s p.count p.rounds p.count_eq p.rounds_eq p.rows

private def nonterminal (input : ThresholdInput n) (s : Fin n) : Run Table :=
  CostedRows.prepare input s >>= emitPrepared input s

private theorem nonterminal_value (input : ThresholdInput n) (s : Fin n) :
    (nonterminal input s).value = ThresholdCompiler.table input s := by
  rw [nonterminal, Run.bind_value, emitPrepared_value, CostedRows.prepare_rows]
  rfl

private def nonpositive (input : ThresholdInput n) : Run Bool :=
  step (input.numerator.natAbs.size + 1) (decide (input.numerator ≤ 0))

private def aboveOne (input : ThresholdInput n) : Run Bool :=
  step (max input.denominator.size input.numerator.natAbs.size + 1)
    (decide ((input.denominator : ℤ) < input.numerator))

private def oneLoop (b : Bool) : Run Table := step 2 (TrivialThreshold.loop b)

private def atStart (input : ThresholdInput n) : Run Table := do
  let start ← step 0 input.start
  match start with
  | .inr b => oneLoop b
  | .inl s => nonterminal input s

private def afterAbove (input : ThresholdInput n) (above : Bool) : Run Table :=
  if above then oneLoop false else atStart input

private def afterNonpositive (input : ThresholdInput n) (below : Bool) : Run Table :=
  if below then oneLoop true else aboveOne input >>= afterAbove input

def graph (input : ThresholdInput n) : Run Table :=
  nonpositive input >>= afterNonpositive input

private theorem atStart_value (input : ThresholdInput n) :
    (atStart input).value = match input.start with
      | .inr b => TrivialThreshold.loop b
      | .inl s => ThresholdCompiler.table input s := by
  rw [atStart, Run.bind_value, step_value]
  split
  · rfl
  · exact nonterminal_value input _

theorem graph_value (input : ThresholdInput n) :
    (graph input).value = ThresholdReduction.compile input := by
  rw [graph, Run.bind_value]
  by_cases low : input.numerator ≤ 0
  · simp only [nonpositive, step_value, afterNonpositive, decide_eq_true_eq, oneLoop,
      ThresholdReduction.compile, ite_eq_left low]
  by_cases high : (input.denominator : ℤ) < input.numerator
  · simp only [nonpositive, step_value, afterNonpositive, decide_eq_true_eq, Run.bind_value,
      aboveOne, afterAbove, oneLoop, ThresholdReduction.compile, ite_eq_right low, ite_eq_left high]
  · simp only [nonpositive, step_value, afterNonpositive, decide_eq_true_eq, Run.bind_value,
      aboveOne, afterAbove, atStart_value, ThresholdReduction.compile, ite_eq_right low,
      ite_eq_right high]
    cases input.start <;> rfl

/-! ## Binary execution -/

private def afterGraph (input : ThresholdInput n) : Run (Option (List Bool)) := do
  let table ← graph input
  let bits ← CostedBinary.serializeRun table
  step 0 (some bits)

private def afterDecode (source : Option (Σ n, ThresholdInput n)) : Run (Option (List Bool)) := do
  let decoded ← step 0 source
  match decoded with
  | none => pure none
  | some ⟨_, input⟩ => afterGraph input

/-- The executable parser, graph construction, and writer, with their work. -/
def run (bits : List Bool) : Run (Option (List Bool)) :=
  CostedBinary.decodeRun bits >>= afterDecode

theorem run_value (bits : List Bool) :
    (run bits).value = (decodeInput bits).map (fun ⟨_, input⟩ => ThresholdReduction.compileBits input) := by
  simp only [run, Run.bind_value, CostedBinary.decodeRun_value, afterDecode, step_value]
  cases decodeInput bits with
  | none => rfl
  | some pair =>
    rcases pair with ⟨n, input⟩
    simp [afterGraph, graph_value, CostedBinary.serializeRun_value, ThresholdReduction.compileBits]

/-! ## Bounds on the executed stages -/

/-- A common bound on row, term, and vertex counts in the graph stage. -/
def arenaBudget (L : ℕ) : ℕ := 128 * (L+1)^2

def wordWidth (L : ℕ) : ℕ := 16 * (arenaBudget L + 1)

def graphSlots (L : ℕ) : ℕ :=
  CostedRows.slots L + 100*(arenaBudget L+1)^2 + CostedArena.slotBudget (arenaBudget L) + 10

def executionSlots (L : ℕ) : ℕ :=
  100*(L+1) + graphSlots L + 20*(16000*L^3+1) + 2

/-- Bill the observed transitions at a width covering their operands and the
binary addresses of input, linked cells, scratch space, and output. -/
def bitWork (xs : List Bool) : ℕ :=
  let work := (run xs).work
  work.slots * wordCost (max work.width (addressWidth xs.length work.slots work.width))

private def allowance (L : ℕ) : ℕ :=
  (L+1) + (executionSlots L+1) + 3*(wordWidth L+1) + 8

/-- One fixed polynomial in the length of the source bit string. -/
def polynomial (L : ℕ) : ℕ := executionSlots L * wordCost (allowance L)

private theorem budget_large (L : ℕ) : 14*L + 3 ≤ arenaBudget L := by
  unfold arenaBudget
  nlinarith [Nat.zero_le (L^2)]

private theorem budget_graph {L K : ℕ} (h : K ≤ L) : 128 * K^2 ≤ arenaBudget L := by
  unfold arenaBudget
  gcongr
  omega

private theorem emitIndexed_bound (input : ThresholdInput n) (s : Fin n) (a r L : ℕ)
    (ha : a = (ThresholdCompiler.system input s).averages.length)
    (hr : r = ThresholdCompiler.precision input)
    (rows : List (IntAtom (ThresholdCompiler.Variables input s)))
    (rowsEq : rows = ThresholdCompiler.integerRows input s)
    (pos : 0 < input.numerator) (inside : input.numerator ≤ (input.denominator : ℤ))
    (len : inputLength input ≤ L) :
    (emitIndexed input s a r ha hr rows).Bound
      (100*(arenaBudget L+1)^2 + (7 + CostedArena.slotBudget (arenaBudget L))) (wordWidth L) := by
  subst a r rows
  let B := arenaBudget L
  let Q := inputLength input
  let a := (ThresholdCompiler.system input s).averages.length
  let r := ThresholdCompiler.precision input
  let listing := ThresholdCompiler.listing input s
  let rows := ThresholdCompiler.integerRows input s
  let w := CostedArena.labelWidth n a r
  have large : 14*L + 3 ≤ B := budget_large L
  have n_le : n ≤ Q := by dsimp [Q, inputLength]; omega
  have a_le : a ≤ n := CompilationCounts.average_count_le _ _ _
  have r_le : r ≤ 4*Q := CompilationCost.depth_le input
  have nB : n ≤ B := by omega
  have aB : a ≤ B := by omega
  have rB : r+1 ≤ B := by omega
  have wB : w ≤ 3*B+2 := by
    have := (BinarySize.size_le_self n).trans nB
    have := (BinarySize.size_le_self a).trans aB
    have := (BinarySize.size_le_self (r+1)).trans rB
    dsimp [w, CostedArena.labelWidth]
    omega
  have graphB : vertexCount input s + edgeCount input s ≤ B :=
    (graph_size_le input s).trans (budget_graph len)
  have vertices := ArenaEncoding.vertices_length listing rows
  change (ArenaEncoding.vertices listing rows).items.length = _ at vertices
  have vl : (ArenaEncoding.vertices listing rows).items.length = vertexCount input s := rfl
  have ls : listing.items.length ≤ B := by omega
  have rs : rows.length ≤ B := by omega
  have terms (row : IntAtom (ThresholdCompiler.Variables input s)) (mem : row ∈ rows) :
      row.terms.length ≤ B :=
    (member_terms_le rows row mem).trans ((integerTerms_le input s).trans (budget_graph len))
  have t_le : input.threshold ≤ 1 :=
    le_of_not_gt (fun gt => (not_lt_of_ge inside) (input.one_lt_threshold_iff.mp gt))
  have mag (row : IntAtom (ThresholdCompiler.Variables input s)) (mem : row ∈ rows)
      (t : ThresholdCompiler.Variables input s × ℤ) (tm : t ∈ row.terms) :
      t.2.natAbs.size ≤ B := by
    have ab := CompilationScale.integer_offsets_bounded _ _
      (ThresholdCompiler.weighted_offsets input s pos t_le) row mem t tm
    have nb : t.2.natAbs ≤ ThresholdCompiler.integerScale input := by
      rw [← Int.natCast_natAbs] at ab
      exact_mod_cast ab
    have qb : (ThresholdCompiler.integerScale input).size ≤ 7*Q := scale_size_le input
    exact (Nat.size_le_size nb).trans (qb.trans (by omega))
  have labels := CostedArena.variableItems_bound n a r B nB aB rB
  have word : (CostedArena.labelWidthRun n a r).Bound 7 (wordWidth L) :=
    (CostedArena.labelWidthRun_bound n a r).weaken le_rfl (by change n+a+r+4 ≤ 16*(B+1); omega)
  have arena : (CostedArena.emit w (CostedArena.variableItems n a r).value rows).Bound
      (CostedArena.slotBudget B) (wordWidth L) := by
    rw [CostedArena.variableItems_value]
    exact (CostedArena.emit_bound w listing.items rows B B ls rs terms mag).weaken le_rfl
      (by change w + 4*(B+1) + B + 10 ≤ 16*(B+1); omega)
  have rest := bound_bind (f := fun width =>
    CostedArena.emit width (CostedArena.variableItems n a r).value rows) word
    (by simpa only [CostedArena.labelWidthRun_value] using arena)
  exact bound_bind (labels.weaken le_rfl (by change B+1 ≤ 16*(B+1); omega)) rest

private theorem nonterminal_bound (input : ThresholdInput n) (s : Fin n) (L : ℕ)
    (pos : 0 < input.numerator) (inside : input.numerator ≤ (input.denominator : ℤ))
    (len : inputLength input ≤ L) :
    (nonterminal input s).Bound (CostedRows.slots L + 100*(arenaBudget L+1)^2 +
      (7 + CostedArena.slotBudget (arenaBudget L))) (wordWidth L) := by
  let p := CostedRows.prepare input s
  have prep : p.Bound (CostedRows.slots L) (wordWidth L) := by
    have big := budget_large L
    refine (CostedRows.prepare_bound input s pos inside).weaken ?_ ?_
    · unfold CostedRows.slots
      gcongr
    · change 64*(inputLength input+1) ≤ 16*(arenaBudget L+1)
      have wide : 4*(L+1) ≤ arenaBudget L+1 := by unfold arenaBudget; nlinarith
      omega
  have emitted := emitIndexed_bound input s p.value.count p.value.rounds L
    p.value.count_eq p.value.rounds_eq p.value.rows (CostedRows.prepare_rows input s) pos inside len
  have composed := bound_bind (f := emitPrepared input s) prep emitted
  simpa only [nonterminal, Nat.add_assoc] using composed

theorem graph_bound (input : ThresholdInput n) (L : ℕ) (len : inputLength input ≤ L) :
    (graph input).Bound (graphSlots L) (wordWidth L) := by
  let B := arenaBudget L
  let K := CostedRows.slots L + 100*(B+1)^2 + (7 + CostedArena.slotBudget B)
  let W := wordWidth L
  have big := budget_large L
  have num : input.numerator.natAbs.size ≤ L := by unfold inputLength at len; omega
  have den : input.denominator.size ≤ L := by unfold inputLength at len; omega
  have cmp₁ : (nonpositive input).Bound 1 W :=
    (bound_step _ _).weaken le_rfl (by change input.numerator.natAbs.size + 1 ≤ 16*(B+1); omega)
  have cmp₂ : (aboveOne input).Bound 1 W :=
    (bound_step _ _).weaken le_rfl (by
      change max input.denominator.size input.numerator.natAbs.size + 1 ≤ 16*(B+1)
      omega)
  have loopOk (b : Bool) : (oneLoop b).Bound K W :=
    (bound_step 2 _).weaken (by dsimp [K]; omega) (by dsimp [W, wordWidth]; omega)
  have startOk (pos : 0 < input.numerator) (le : input.numerator ≤ (input.denominator : ℤ)) :
      (atStart input).Bound (1+K) W := by
    apply bound_bind ((bound_step 0 input.start).weaken le_rfl (Nat.zero_le W))
    change (match input.start with
      | .inr b => oneLoop b
      | .inl s => nonterminal input s).Bound K W
    split
    · exact loopOk _
    · exact nonterminal_bound input _ L pos le len
  have total : (graph input).Bound (1+(1+(1+K))) W := by
    unfold graph
    apply bound_bind cmp₁
    simp only [afterNonpositive, nonpositive, step_value, decide_eq_true_eq]
    split
    · exact (loopOk _).weaken (by omega) le_rfl
    · rename_i notNonpositive
      apply bound_bind cmp₂
      simp only [afterAbove, aboveOne, step_value, decide_eq_true_eq]
      split
      · exact (loopOk _).weaken (by omega) le_rfl
      · rename_i notAbove
        exact startOk (lt_of_not_ge notNonpositive) (le_of_not_gt notAbove)
  exact total.weaken (show 1+(1+(1+K)) ≤ graphSlots L by unfold graphSlots; dsimp [K,B]; omega) le_rfl

private theorem fields_fit (input : ThresholdInput n) (L : ℕ) (len : inputLength input ≤ L) :
    let t := ThresholdReduction.compile input
    let B := arenaBudget L
    t.start.size ≤ B ∧ t.owners.length.size ≤ B ∧ t.arcs.length.size ≤ B ∧
      ∀ e ∈ t.arcs, e.src.size ≤ B ∧ e.dst.size ≤ B ∧ e.weight.natAbs.size ≤ B := by
  let B := arenaBudget L
  have large := budget_large L
  change _ ∧ _ ∧ _ ∧ _
  have loopFits (b : Bool) :
      let t := TrivialThreshold.loop b
      t.start.size ≤ B ∧ t.owners.length.size ≤ B ∧ t.arcs.length.size ≤ B ∧
        ∀ e ∈ t.arcs, e.src.size ≤ B ∧ e.dst.size ≤ B ∧ e.weight.natAbs.size ≤ B := by
    cases b <;> simp [TrivialThreshold.loop, show 1 ≤ B by omega]
  unfold ThresholdReduction.compile
  split
  · exact loopFits true
  · rename_i notNonpositive
    split
    · exact loopFits false
    · rename_i notAbove
      cases input.start with
      | inr b => exact loopFits b
      | inl s =>
        change let t := mainTable input s
          t.start.size ≤ B ∧ t.owners.length.size ≤ B ∧ t.arcs.length.size ≤ B ∧
            ∀ e ∈ t.arcs, e.src.size ≤ B ∧ e.dst.size ≤ B ∧ e.weight.natAbs.size ≤ B
        have graphB : vertexCount input s + edgeCount input s ≤ B :=
          (graph_size_le input s).trans (budget_graph len)
        have vB : vertexCount input s ≤ B := by omega
        have eB : edgeCount input s ≤ B := by omega
        have ⟨hv, he⟩ := table_lengths input s
        have ⟨hs, ha⟩ := table_indices input s
        refine ⟨(BinarySize.size_le_self _).trans (hs.le.trans vB),
          (BinarySize.size_le_self _).trans (hv ▸ vB),
          (BinarySize.size_le_self _).trans (he ▸ eB), ?_⟩
        intro arc mem
        have ⟨src, dst⟩ := ha arc mem
        have pos := lt_of_not_ge notNonpositive
        have threshold : input.threshold ≤ 1 :=
          le_of_not_gt fun h => notAbove (input.one_lt_threshold_iff.mp h)
        have magnitude := ThresholdCompiler.table_weight_le input s pos threshold arc mem
        change arc.weight.natAbs ≤ (mainTable input s).owners.length * scale input + 1 at magnitude
        rw [hv] at magnitude
        exact ⟨(BinarySize.size_le_self _).trans (src.le.trans vB),
          (BinarySize.size_le_self _).trans (dst.le.trans vB),
          (weight_bits_le input s arc.weight magnitude).trans (by omega)⟩

private theorem afterGraph_bound (input : ThresholdInput n) (L : ℕ)
    (len : inputLength input ≤ L) (bits : (inputBits input).length ≤ L) :
    (afterGraph input).Bound (graphSlots L + (20*(16000*L^3+1) + 1)) (wordWidth L) := by
  let t := ThresholdReduction.compile input
  let B := arenaBudget L
  have ⟨start, owners, arcs, fields⟩ := fields_fit input L len
  have size : (tableBits t).length ≤ 16000*L^3 :=
    (ThresholdReduction.compileBits_le input).trans (by gcongr)
  have writer : (CostedBinary.serializeRun t).Bound (20*(16000*L^3+1)) (wordWidth L) := by
    refine (CostedBinary.serializeRun_bound t B start owners arcs fields).weaken (by omega) ?_
    change B+3 ≤ 16*(B+1)
    omega
  have done := bound_bind (f := fun bits : List Bool => step 0 (some bits)) writer
    ((bound_step 0 _).weaken le_rfl (Nat.zero_le (wordWidth L)))
  apply bound_bind (graph_bound input L len)
  simpa only [graph_value, t] using done

/-- The bound applies to the actual run on every bit string the parser accepts. -/
theorem run_bound {xs : List Bool} {input : ThresholdInput n}
    (accepted : decodeInput xs = some ⟨n,input⟩) :
    (run xs).Bound (executionSlots xs.length) (wordWidth xs.length) := by
  let L := xs.length
  have hlen : inputLength input ≤ L := CostedBinary.inputLength_le_of_decode accepted
  have canonical : xs = inputBits input := CostedBinary.inputBits_of_decode accepted
  have hbits : (inputBits input).length ≤ L := by rw [← canonical]
  have read := (CostedBinary.decodeRun_bound_of_success accepted).weaken le_rfl
    (show L+3 ≤ wordWidth L by have := budget_large L; unfold wordWidth; omega)
  have rest : (afterDecode (CostedBinary.decodeRun xs).value).Bound
      (1 + (graphSlots L + (20*(16000*L^3+1) + 1))) (wordWidth L) := by
    rw [CostedBinary.decodeRun_value, accepted]
    exact bound_bind ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))
      (afterGraph_bound input L hlen hbits)
  refine (bound_bind read rest).weaken ?_ le_rfl
  change _ ≤ executionSlots L
  unfold executionSlots
  dsimp only [L]
  omega

/-- The polynomial bounds the billed cost of the measured execution. -/
theorem bitWork_le {xs : List Bool} {input : ThresholdInput n}
    (accepted : decodeInput xs = some ⟨n,input⟩) :
    bitWork xs ≤ polynomial xs.length := by
  let L := xs.length
  let w := (run xs).work
  obtain ⟨slots, width⟩ := run_bound accepted
  change w.slots ≤ executionSlots L at slots
  change w.width ≤ wordWidth L at width
  have addr : addressWidth L w.slots w.width ≤ allowance L := by
    have il := BinarySize.size_le_self (L+1)
    have sl := BinarySize.size_le_self (w.slots+1)
    have wl := BinarySize.size_le_self (w.width+1)
    unfold addressWidth allowance
    omega
  have data : w.width ≤ allowance L := width.trans (by unfold allowance; omega)
  exact Nat.mul_le_mul slots (wordCost_mono (max_le data addr))

end StochasticGames.CompilerExecution
