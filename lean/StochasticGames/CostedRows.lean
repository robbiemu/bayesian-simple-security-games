module

public import StochasticGames.CompilationCost
public import StochasticGames.CompilerRun
public import StochasticGames.ThresholdCompiler
import all StochasticGames.AtomEncoding
import all StochasticGames.IntegerAtoms
import all StochasticGames.MaxAverageReduction
import all StochasticGames.ThresholdInput
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Executing the integer-row translation

The implementation builds the three blocks of rows in their original order.
It uses integers throughout: the complemented terminal literals become zero
and the common scale, and a shifted wire uses a power of two times the
threshold denominator. The rational compiler is used in the erasure proof.
-/

@[expose] public section
namespace StochasticGames.CostedRows

open AverageFeasibility AtomEncoding IntegerAtoms SourceRows ThresholdCompiler

variable {ι ν : Type*} {n a r : ℕ}

private def intSignal (Q : ℕ) (x : Term ι) : Var ι a r × ℤ :=
  (x.index.elim .reference .source, if x.offset = 0 then 0 else Q)

private def intFrom (x : ν × ℤ) (ts : List (ν × ℤ)) : IntAtom ν :=
  ⟨x.1, ts.map fun t => (t.1, t.2 - x.2)⟩

private def intComparison (hi lo : ν) (u v : ν × ℤ) : List (IntAtom ν) :=
  [⟨hi, [u,v]⟩, ⟨lo, [u]⟩, ⟨lo, [v]⟩]

private def shiftInteger (d r j : ℕ) : ℕ := d * 2 ^ (r - (j + 1))

def cutoffInteger (input : ThresholdInput n) : ℤ :=
  (((input.denominator : ℤ) - input.numerator) * 3 ^ (n + 1) + 1) *
    2 ^ (precision input + 1)

private theorem scaled_cutoff (input : ThresholdInput n) :
    (integerScale input : ℚ) * SourcePrecision.cutoff n input.denominator input.threshold =
      (cutoffInteger input : ℚ) := by
  have bpos : (0 : ℚ) < input.denominator := by exact_mod_cast input.denominator_pos
  simp only [integerScale, CompilationScale.scale, SourcePrecision.cutoff,
    SourcePrecision.D, ThresholdInput.threshold, cutoffInteger, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_one, Int.cast_ofNat,
    Int.cast_sub, Int.cast_natCast]
  field_simp

private theorem scaled_shift (d : ℕ) (j : Fin r) :
    (CompilationScale.scale d r : ℚ) * (ShiftedComparisons.gapBound 1 j.val / 4) =
      (shiftInteger d r j : ℚ) := by
  have ij : r + 1 = r - (j.val + 1) + (j.val + 2) := by have := j.isLt; omega
  simp only [shiftInteger, CompilationScale.scale, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, ShiftedComparisons.gapBound_eq]
  rw [ij, pow_add, pow_add (2 : ℚ) j.val 2]
  field_simp
  ring

private def Matches (Q : ℕ) (x : ν × ℤ) (y : Signal ν) : Prop :=
  x.1 = y.1 ∧ (Q : ℚ) * y.2 = (x.2 : ℚ)

private theorem signal_matches (Q : ℕ) (x : Term ι) (hx : x.offset = 0 ∨ x.offset = 1) :
    Matches Q (intSignal (a := a) (r := r) Q x) (sourceSignal x) := by
  obtain h | h := hx <;> simp [Matches, intSignal, sourceSignal, h]

private theorem from_matches (Q : ℕ) {x : ν × ℤ} {y : Signal ν}
    (hx : Matches Q x y) (xs : List (ν × ℤ)) (ys : List (Signal ν))
    (hs : List.Forall₂ (Matches Q) xs ys) :
    intFrom x xs = integerAtom Q (fromSignals y ys) := by
  unfold intFrom integerAtom fromSignals
  simp only [List.map_map, Function.comp_def]
  congr 1
  · exact hx.1
  · induction hs with
    | nil => rfl
    | cons h hs ih =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq]
      refine ⟨⟨h.1, ?_⟩, ih⟩
      rw [mul_sub, h.2, hx.2, ← Int.cast_sub, Int.floor_intCast]

private theorem comparison_matches (Q : ℕ) (hi lo : ν) {x y : ν × ℤ} {u v : Signal ν}
    (hu : Matches Q x u) (hv : Matches Q y v) :
    intComparison hi lo x y = encodeAt Q (comparison hi lo u v) := by
  have castU : ⌊(Q : ℚ) * u.2⌋ = x.2 := by rw [hu.2, Int.floor_intCast]
  have castV : ⌊(Q : ℚ) * v.2⌋ = y.2 := by rw [hv.2, Int.floor_intCast]
  simp [intComparison, encodeAt, comparison, integerAtom, fromSignals, castU, castV, ← hu.1, ← hv.1]

private def intRound (d : ℕ) (i : Fin a) (j : Fin r) : List (IntAtom (Var ι a r)) :=
  let w : ℤ := shiftInteger d r j
  intComparison (.high i j.succ) (.low i j.succ) (.high i j.castSucc, -w) (.low i j.castSucc, w)

private theorem round_matches (d : ℕ) (i : Fin a) (j : Fin r) :
    intRound (ι := ι) d i j = encodeAt (CompilationScale.scale d r) (roundRows 1 i j) := by
  apply comparison_matches
  · exact ⟨rfl, by simp [mul_neg, scaled_shift]⟩
  · exact ⟨rfl, by simpa using scaled_shift d j⟩

private def intAverage (d : ℕ) (i : Fin a) (ar : AverageRow ι) : List (IntAtom (Var ι a r)) :=
  let Q := CompilationScale.scale d r
  intComparison (.high i 0) (.low i 0) (intSignal Q ar.first) (intSignal Q ar.second) ++
    (List.finRange r).flatMap (intRound d i) ++
    [intFrom (intSignal Q ar.lhs) [(.high i (Fin.last r), 0)]]

private theorem average_matches (d : ℕ) (i : Fin a) (ar : AverageRow ι)
    (hs : ∀ x ∈ [ar.lhs, ar.first, ar.second], x.offset = 0 ∨ x.offset = 1) :
    intAverage (r := r) d i ar = encodeAt (CompilationScale.scale d r) (averageAtoms 1 i ar) := by
  let Q := CompilationScale.scale d r
  have hinitial := comparison_matches Q (Var.high (ι := ι) (rounds := r) i 0) (.low i 0)
    (signal_matches Q ar.first (hs _ (by simp))) (signal_matches Q ar.second (hs _ (by simp)))
  have hfinal := from_matches Q (signal_matches (a := a) (r := r) Q ar.lhs (hs _ (by simp)))
    [(.high i (Fin.last r), 0)] [(.high i (Fin.last r), 0)] (.cons ⟨rfl, by simp⟩ .nil)
  simp only [intAverage, averageAtoms, encodeAt, List.map_append, List.map_flatMap,
    List.map_cons, List.map_nil, initialRows, finalRow] at *
  rw [hinitial, hfinal]
  congr 2
  exact List.flatMap_congr fun j _ => round_matches d i j

private def intDiff (Q : ℕ) (d : DifferenceRow ι) : IntAtom (Var ι a r) :=
  intFrom (intSignal Q d.lhs) [intSignal Q d.rhs]

private def intMax (Q : ℕ) (m : MaxRow ι) : IntAtom (Var ι a r) :=
  intFrom (intSignal Q m.lhs) (m.terms.map (intSignal Q))

private def intBlock (baseSystem : System ι) (s : ι) (d r : ℕ) (h : ℤ) :
    List (IntAtom (vars baseSystem r)) :=
  let Q := CompilationScale.scale d r
  ⟨.reference, [(.source s, -h)]⟩ ::
    (baseSystem.differences.map (intDiff Q) ++ baseSystem.maxima.map (intMax Q) ++
      (List.finRange baseSystem.averages.length).flatMap fun i =>
        intAverage d i (baseSystem.averages.get i))

private theorem base_zero_one (input : ThresholdInput n) (s : Fin n) :
    SourceLinearization.AllOffsets (fun q => q = 0 ∨ q = 1) (base input.rows.get) := by
  let S := tightened input.rows.get s 0
  have good (q : ℚ) (hm : q ∈ MaxAverageReduction.offsets S) : q = 0 ∨ q = 1 := by
    rcases SourceLinearization.tightened_literal_offsets input.rows.get s 0 q hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  constructor
  · intro row hr
    have mem : row ∈ S.differences := List.mem_cons_of_mem _ hr
    constructor <;> apply good <;>
      simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap] <;>
      exact Or.inl (Or.inl ⟨row, mem, by simp⟩)
  · intro row hr
    constructor
    · apply good
      simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨row, hr, List.mem_cons_self⟩)
    · intro t ht
      apply good
      simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨row, hr, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t, ht, rfl⟩)⟩)
  · intro row hr
    refine ⟨?_, ?_, ?_⟩ <;> apply good <;>
      simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap] <;>
      exact Or.inr ⟨row, hr, by simp⟩

private theorem block_matches (input : ThresholdInput n) (s : Fin n) :
    intBlock (base input.rows.get) s (SourcePrecision.D n input.denominator) (precision input)
      (cutoffInteger input) = integerRows input s := by
  let S := base input.rows.get
  let d := SourcePrecision.D n input.denominator
  let r := precision input
  let Q := integerScale input
  let p := SourcePrecision.cutoff n input.denominator input.threshold
  have offsets := base_zero_one input s
  have first : (⟨.reference, [(.source s, -cutoffInteger input)]⟩ : IntAtom (vars S r)) =
      integerAtom Q (fromSignals (sourceSignal (literal p)) [sourceSignal (var s)]) := by
    change _ = (⟨.reference, [(.source s, ⌊(Q : ℚ) * (0 - p)⌋)]⟩ : IntAtom (vars S r))
    rw [zero_sub, mul_neg, (show (Q : ℚ) * p = (cutoffInteger input : ℚ) from scaled_cutoff input),
      ← Int.cast_neg, Int.floor_intCast]
  have hd : S.differences.map (intDiff (a := S.averages.length) (r := r) Q) =
      S.differences.map fun row => integerAtom Q
        (fromSignals (sourceSignal row.lhs) [sourceSignal row.rhs]) := by
    refine List.map_congr_left fun row hr => ?_
    have hs := offsets.differences row hr
    exact from_matches Q (signal_matches Q _ hs.1) _ _ (.cons (signal_matches Q _ hs.2) .nil)
  have hm : S.maxima.map (intMax (a := S.averages.length) (r := r) Q) =
      S.maxima.map fun row => integerAtom Q
        (fromSignals (sourceSignal row.lhs) (row.terms.map sourceSignal)) := by
    refine List.map_congr_left fun row hr => ?_
    have hs := offsets.maxima row hr
    apply from_matches Q (signal_matches Q _ hs.1)
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact fun t ht => signal_matches Q t (hs.2 t ht)
  have ha (i : Fin S.averages.length) : intAverage (r := r) d i (S.averages.get i) =
      encodeAt Q (averageAtoms 1 i (S.averages.get i)) := by
    apply average_matches
    have hs := offsets.averages _ (List.get_mem _ i)
    simpa using hs
  change _ = ([fromSignals (sourceSignal (literal p)) [sourceSignal (var s)]] ++
    S.differences.map (fun row : DifferenceRow (Fin n) => fromSignals (sourceSignal row.lhs) [sourceSignal row.rhs]) ++
    S.maxima.map (fun row : MaxRow (Fin n) => fromSignals (sourceSignal row.lhs) (row.terms.map sourceSignal)) ++
    (List.finRange S.averages.length).flatMap (fun i => averageAtoms 1 i (S.averages.get i))).map
      (integerAtom (ν := vars S r) Q)
  simp only [List.map_append, List.map_flatMap, List.map_cons, List.map_map,
    Function.comp_def, List.cons_append, List.nil_append]
  exact congrArg₂ List.cons first (congrArg₂ List.append (congrArg₂ List.append hd hm)
    (List.flatMap_congr fun i _ => ha i))

open CompilerRun

def smallPower (c : ℕ) : ℕ → Run ℕ
  | 0 => step 0 1
  | k + 1 => do
    let _ ← step (k+1).size ()
    let p ← smallPower c k
    natMul p c

@[simp] private theorem power_value (c k : ℕ) : (smallPower c k).value = c ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [smallPower, natMul, ih, pow_succ]

@[simp] private theorem power_slots (c k : ℕ) : (smallPower c k).work.slots = 2*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [smallPower, natMul, ih]; omega

private theorem power_width (c k w : ℕ) (hc : 0 < c) (hcw : c.size ≤ w) (hkw : k.size ≤ w)
    (hpw : (c ^ k).size ≤ w) : (smallPower c k).work.width ≤ w := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk := (Nat.size_le_size (Nat.le_succ k)).trans hkw
    have hp := (Nat.size_le_size (Nat.pow_le_pow_right hc (Nat.le_succ k))).trans hpw
    simp [smallPower, natMul, max_le_iff, hkw, ih hk hp, hp, hcw]

structure Parameters where
  denominator : ℕ
  rounds : ℕ
  scale : ℕ
  cutoff : ℤ

/-- Compute all scalar parameters once. The constructor contains no rationals. -/
def parameters (input : ThresholdInput n) : Run Parameters := do
  let dim ← natAdd n 1
  let factor ← smallPower 3 dim
  let d ← natMul input.denominator factor
  let bits ← step d.size d.size
  let extra ← natMul 2 dim
  let depth ← natAdd bits extra
  let exponent ← natAdd depth 1
  let dyadic ← smallPower 2 exponent
  let scale ← natMul d dyadic
  let difference ← intSub input.denominator input.numerator
  let product ← intMul difference factor
  let incremented ← intAdd product 1
  let threshold ← intMul incremented dyadic
  step 0 ⟨d, depth, scale, threshold⟩

@[simp] theorem parameters_value (input : ThresholdInput n) :
    (parameters input).value = ⟨SourcePrecision.D n input.denominator, precision input,
      integerScale input, cutoffInteger input⟩ := by
  simp [parameters, natAdd, natMul, intAdd, intSub, intMul, precision, integerScale,
    SourcePrecision.depth, SourcePrecision.D, CompilationScale.scale, cutoffInteger]

/-- The bit width allowed for source indices and the signed integer compiler words. -/
def width (L : ℕ) : ℕ := 64 * (L + 1)

private theorem input_bounds (input : ThresholdInput n) :
    n ≤ CompilationCost.inputLength input ∧
    CompilationCounts.moveCount input.rows.get ≤ CompilationCost.inputLength input ∧
    input.denominator.size ≤ CompilationCost.inputLength input ∧
    input.numerator.natAbs.size ≤ CompilationCost.inputLength input := by
  unfold CompilationCost.inputLength
  omega

/-- Read one row of the input vector using its binary index. -/
def readRow (input : ThresholdInput n) (i : Fin n) : Run (Source.Row (Fin n)) :=
  step i.val.size (input.rows.get i)

def sourceDiff (i : Fin n) (row : Source.Row (Fin n)) : Run (List (DifferenceRow (Fin n))) := do
  let menu ← match row with
    | .max h ts => CompilerRun.mapM (fun t => do
      let v ← step 1 (successor t)
      step 0 (⟨var i, v⟩ : DifferenceRow (Fin n))) (h :: ts)
    | _ => step 0 []
  let upper ← step 0 (⟨var i, literal 1⟩ :: menu)
  step 0 (⟨literal 0, var i⟩ :: upper)

def sourceMax (i : Fin n) : Source.Row (Fin n) → Run (List (MaxRow (Fin n)))
  | .min h ts => do
    let menu ← CompilerRun.mapM (fun t => step 1 (successor t)) (h :: ts)
    step 0 [⟨var i, menu⟩]
  | _ => step 0 []

def sourceAvg (i : Fin n) : Source.Row (Fin n) → Run (List (AverageRow (Fin n)))
  | .chance l r => do
    let left ← step 1 (successor l)
    let right ← step 1 (successor r)
    step 0 [⟨var i, left, right⟩]
  | _ => step 0 []

@[simp] private theorem sourceDiff_value (i : Fin n) (row) :
    (sourceDiff i row).value = box i ++ choices i row := by
  cases row <;> simp [sourceDiff, box, choices]

@[simp] private theorem sourceMax_value (i : Fin n) (row) :
    (sourceMax i row).value = maxima i row := by
  cases row <;> simp [sourceMax, maxima]

@[simp] private theorem sourceAvg_value (i : Fin n) (row) :
    (sourceAvg i row).value = averages i row := by
  cases row <;> rfl

def collect (input : ThresholdInput n) (indices : List (Fin n)) {α : Type}
    (f : Fin n → Source.Row (Fin n) → Run (List α)) : Run (List α) :=
  CompilerRun.flatMapM (fun i => readRow input i >>= f i) indices

def readSystem (input : ThresholdInput n) : Run (System (Fin n)) := do
  let indices ← CompilerRun.finRange n
  let diffs ← collect input indices sourceDiff
  let maxs ← collect input indices sourceMax
  let avgs ← collect input indices sourceAvg
  step 0 ⟨diffs, maxs, avgs⟩

@[simp] theorem readSystem_value (input : ThresholdInput n) :
    (readSystem input).value = base input.rows.get := by
  simp [readSystem, collect, readRow, base]

private theorem source_piece_bound (i : Fin n) (row : Source.Row (Fin n)) (K w : ℕ)
    (hv : CompilationCounts.listedSuccessors row ≤ K) (hw : 1 ≤ w) :
    (sourceDiff i row).Bound (5*K+6) w ∧ (sourceMax i row).Bound (5*K+6) w ∧
      (sourceAvg i row).Bound (5*K+6) w := by
  cases row with
  | max h ts =>
    let f (t : Source.Position (Fin n)) := do
      let v ← step 1 (successor t)
      step 0 (⟨var i, v⟩ : DifferenceRow (Fin n))
    have hm := mapM_bound f (h::ts) 2 w (fun _ _ =>
      bound_bind ((bound_step 1 _).weaken le_rfl hw) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))
    obtain ⟨count, wide⟩ := hm
    simp only [CompilationCounts.listedSuccessors] at hv
    simp only [sourceDiff, sourceMax, sourceAvg, Run.Bound, Run.bind_slots, Run.bind_width,
      step_slots, step_width, step_value, max_le_iff, Nat.zero_le, and_true]
    dsimp only [f, List.length_cons] at count wide
    omega
  | min h ts =>
    have hm := mapM_bound (fun t : Source.Position (Fin n) => step 1 (successor t))
      (h::ts) 1 w (fun _ _ => (bound_step 1 _).weaken le_rfl hw)
    obtain ⟨count, wide⟩ := hm
    simp only [CompilationCounts.listedSuccessors] at hv
    simp only [sourceDiff, sourceMax, sourceAvg, Run.Bound, Run.bind_slots, Run.bind_width,
      step_slots, step_width, step_value, max_le_iff, Nat.zero_le, and_true]
    simp only [List.length_cons] at count
    omega
  | chance l r =>
    simp [sourceDiff, sourceMax, sourceAvg, Run.Bound, hw]

private theorem source_piece_length (i : Fin n) (row : Source.Row (Fin n)) :
    (sourceDiff i row).value.length ≤ CompilationCounts.listedSuccessors row + 2 ∧
    (sourceMax i row).value.length ≤ 1 ∧ (sourceAvg i row).value.length ≤ 1 := by
  cases row <;> simp [sourceDiff_value, sourceMax_value, sourceAvg_value, CompilationCounts.listedSuccessors,
    choices, maxima, averages, box]

private theorem move_le (input : ThresholdInput n) (i : Fin n) :
    CompilationCounts.listedSuccessors (input.rows.get i) ≤ CompilationCounts.moveCount input.rows.get := by
  apply List.le_sum_of_mem
  exact List.mem_map_of_mem (List.mem_finRange i)

private theorem collect_bound (input : ThresholdInput n) {α : Type}
    (f : Fin n → Source.Row (Fin n) → Run (List α)) (k len w : ℕ)
    (hw : n.size ≤ w) (hf : ∀ i, (f i (input.rows.get i)).Bound k w)
    (hlen : ∀ i, (f i (input.rows.get i)).value.length ≤ len) :
    (collect input (List.finRange n) f).Bound (n*(1+k+len+2)+1) w := by
  apply (flatMapM_bound _ _ (1+k) len w _ _).weaken (by simp) le_rfl
  · intro i _
    apply bound_bind
    · exact (bound_step _ _).weaken le_rfl ((Nat.size_le_size i.isLt.le).trans hw)
    · exact hf i
  · exact fun i _ => hlen i

private theorem readSystem_bound (input : ThresholdInput n) :
    (readSystem input).Bound (40*(CompilationCost.inputLength input + 1)^2)
      (width (CompilationCost.inputLength input)) := by
  let L := CompilationCost.inputLength input
  let w := width L
  obtain ⟨hn, hm, _, _⟩ := input_bounds input
  change n ≤ L at hn
  change CompilationCounts.moveCount _ ≤ L at hm
  have hw : n.size ≤ w := (BinarySize.size_le_self _).trans (by dsimp [w, width]; omega)
  have one : 1 ≤ w := by dsimp [w,width]; omega
  have rowbound (i : Fin n) := source_piece_bound i (input.rows.get i) L w ((move_le _ i).trans hm) one
  have lens (i : Fin n) := source_piece_length i (input.rows.get i)
  have hd := collect_bound input sourceDiff (5*L+6) (L+2) w hw (fun i => (rowbound i).1)
    (fun i => (lens i).1.trans (Nat.add_le_add_right ((move_le _ i).trans hm) 2))
  have hm := collect_bound input sourceMax (5*L+6) 1 w hw (fun i => (rowbound i).2.1)
    (fun i => (lens i).2.1)
  have ha := collect_bound input sourceAvg (5*L+6) 1 w hw (fun i => (rowbound i).2.2)
    (fun i => (lens i).2.2)
  have ir := (finRange_bound n).weaken le_rfl hw
  obtain ⟨hdc, hdw⟩ := hd
  obtain ⟨hmc, hmw⟩ := hm
  obtain ⟨hac, haw⟩ := ha
  obtain ⟨irc, irw⟩ := ir
  change (readSystem input).Bound (40*(L+1)^2) w
  simp only [readSystem, Run.Bound, Run.bind_slots, Run.bind_width, finRange_value, step_slots,
    step_width, max_le_iff, Nat.zero_le, and_true]
  refine ⟨?_, irw, hdw, hmw, haw⟩
  have mul := Nat.mul_le_mul_right L hn
  nlinarith

def readSignal (Q : ℕ) (t : Term (Fin n)) : Run (Var (Fin n) a r × ℤ) := do
  let zero ← step t.offset.num.natAbs.size (decide (t.offset.num = 0))
  let v ← step 1 (t.index.elim .reference .source : Var (Fin n) a r)
  step Q.size (v, if zero then 0 else (Q : ℤ))

@[simp] private theorem readSignal_value (Q : ℕ) (t : Term (Fin n)) :
    (readSignal (a := a) (r := r) Q t).value = intSignal Q t := by
  simp [readSignal, intSignal]

def translate (x t : ν × ℤ) : Run (ν × ℤ) :=
  let z := intSub t.2 x.2
  ⟨(t.1, z.value), z.work.seq (Work.one 0)⟩

def emitFrom {ν : Type} (x : ν × ℤ) (ts : List (ν × ℤ)) : Run (IntAtom ν) := do
  let v ← CompilerRun.mapM (translate x) ts
  step 0 ⟨x.1, v⟩

@[simp] private theorem emitFrom_value {ν : Type} (x : ν × ℤ) (ts : List (ν × ℤ)) :
    (emitFrom x ts).value = intFrom x ts := by
  simp [emitFrom, intFrom, translate, intSub]

def emitDiff (Q : ℕ) (row : DifferenceRow (Fin n)) : Run (IntAtom (Var (Fin n) a r)) := do
  let x ← readSignal Q row.lhs
  let y ← readSignal Q row.rhs
  let ts ← step 0 [y]
  emitFrom x ts

def emitMax (Q : ℕ) (row : MaxRow (Fin n)) : Run (IntAtom (Var (Fin n) a r)) := do
  let x ← readSignal Q row.lhs
  let ts ← CompilerRun.mapM (readSignal Q) row.terms
  emitFrom x ts

@[simp] private theorem emitDiff_value (Q : ℕ) (row : DifferenceRow (Fin n)) :
    (emitDiff (a := a) (r := r) Q row).value = intDiff Q row := by simp [emitDiff, intDiff]

@[simp] private theorem emitMax_value (Q : ℕ) (row : MaxRow (Fin n)) :
    (emitMax (a := a) (r := r) Q row).value = intMax Q row := by simp [emitMax, intMax]

private theorem signal_bound (Q : ℕ) (t : Term (Fin n)) {w : ℕ}
    (hx : t.offset = 0 ∨ t.offset = 1) (one : 1 ≤ w) (hq : Q.size ≤ w) :
    (readSignal (a := a) (r := r) Q t).Bound 3 w := by
  rcases hx with h | h <;>
    simp [readSignal, Run.Bound, h, max_le_iff, one, hq]

private theorem signal_weight (Q : ℕ) (t : Term (Fin n)) :
    (intSignal (a := a) (r := r) Q t).2.natAbs.size ≤ Q.size := by
  by_cases hx : t.offset = 0 <;> simp [intSignal, hx]

private theorem emitFrom_bound {ν : Type} (x : ν × ℤ) (ts : List (ν × ℤ)) (w : ℕ)
    (hx : x.2.natAbs.size + 1 ≤ w) (ht : ∀ t ∈ ts, t.2.natAbs.size + 1 ≤ w) :
    (emitFrom x ts).Bound (4*ts.length+2) w := by
  have piece (t) (hm : t ∈ ts) : (translate x t).Bound 2 w := by
    obtain tw := ht t hm
    simp only [translate, intSub, Run.Bound, Work.seq, Work.one, step, Nat.max_zero]
    omega
  have hm := mapM_bound (translate x) ts 2 w piece
  exact (bound_bind hm ((bound_step 0 _).weaken le_rfl (Nat.zero_le w))).weaken
    (by omega) le_rfl

private theorem emitDiff_bound (Q : ℕ) (row : DifferenceRow (Fin n)) (w : ℕ)
    (hl : row.lhs.offset = 0 ∨ row.lhs.offset = 1) (hr : row.rhs.offset = 0 ∨ row.rhs.offset = 1)
    (hq : Q.size + 1 ≤ w) : (emitDiff (a := a) (r := r) Q row).Bound 13 w := by
  have enough : Q.size ≤ w := by omega
  have one : 1 ≤ w := by omega
  have hx := signal_bound (a := a) (r := r) Q _ hl one enough
  have hy := signal_bound (a := a) (r := r) Q _ hr one enough
  have weight (t : Term (Fin n)) :
      (intSignal (a := a) (r := r) Q t).2.natAbs.size + 1 ≤ w :=
    (Nat.add_le_add_right (signal_weight Q t) 1).trans hq
  have last := emitFrom_bound (intSignal (a := a) (r := r) Q row.lhs) [intSignal Q row.rhs] w
    (weight _) (by simpa using weight row.rhs)
  simp only [emitDiff, Run.Bound, Run.bind_slots, Run.bind_width, readSignal_value,
    step_value, step_slots, step_width, max_le_iff, Nat.zero_le, true_and]
  exact ⟨by have := hx.1; have := hy.1; have := last.1; simp only [List.length_cons,
    List.length_nil] at *; omega, hx.2, hy.2, last.2⟩

private theorem emitMax_bound (Q : ℕ) (row : MaxRow (Fin n)) (w : ℕ)
    (hl : row.lhs.offset = 0 ∨ row.lhs.offset = 1)
    (hr : ∀ t ∈ row.terms, t.offset = 0 ∨ t.offset = 1)
    (hq : Q.size + 1 ≤ w) :
    (emitMax (a := a) (r := r) Q row).Bound (9*row.terms.length+6) w := by
  have enough : Q.size ≤ w := by omega
  have one : 1 ≤ w := by omega
  have hx := signal_bound (a := a) (r := r) Q _ hl one enough
  have ht := mapM_bound (readSignal (a := a) (r := r) Q) row.terms 3 w
    (fun t hm => signal_bound Q t (hr t hm) one enough)
  have weight (t : Term (Fin n)) :
      (intSignal (a := a) (r := r) Q t).2.natAbs.size + 1 ≤ w :=
    (Nat.add_le_add_right (signal_weight Q t) 1).trans hq
  have last := emitFrom_bound (intSignal (a := a) (r := r) Q row.lhs)
    (row.terms.map (intSignal Q)) w (weight _) (by simpa using fun t _ => weight t)
  simp only [emitMax, Run.Bound, Run.bind_slots, Run.bind_width, readSignal_value, mapM_value, max_le_iff]
  refine ⟨?_, hx.2, ht.2, last.2⟩
  have hxs := hx.1
  have hts := ht.1
  have hls : (emitFrom (intSignal (a := a) (r := r) Q row.lhs) (row.terms.map (fun t => intSignal Q t))).work.slots ≤ 4*row.terms.length+2 := by
    simpa only [List.length_map] using last.1
  omega

def emitComparison {ν : Type} (hi lo : ν) (x y : ν × ℤ) : Run (List (IntAtom ν)) := do
  let a ← step 0 [x]
  let b ← step 0 [y]
  let ab ← step 0 (x :: b)
  let high ← step 0 (⟨hi, ab⟩ : IntAtom ν)
  let lowA ← step 0 (⟨lo, a⟩ : IntAtom ν)
  let lowB ← step 0 (⟨lo, b⟩ : IntAtom ν)
  let last ← step 0 [lowB]
  let tail ← step 0 (lowA :: last)
  step 0 (high :: tail)

@[simp] private theorem emitComparison_value {ν : Type} (hi lo : ν) (x y : ν × ℤ) :
    (emitComparison hi lo x y).value = intComparison hi lo x y := rfl

def emitRound (r d : ℕ) (i : Fin a) (j : Fin r) : Run (List (IntAtom (Var (Fin n) a r))) := do
  let next ← step j.val.size j.succ
  let exponent ← natSub r next.val
  let p ← smallPower 2 exponent
  let z ← natMul d p
  let w ← intSub 0 (z : ℤ)
  let u ← step 0 (Var.high i j.castSucc, w)
  let v ← step 0 (Var.low i j.castSucc, (z : ℤ))
  emitComparison (.high i next) (.low i next) u v

@[simp] private theorem emitRound_value (d : ℕ) (i : Fin a) (j : Fin r) :
    (emitRound (n := n) r d i j).value = intRound d i j := by
  simp [emitRound, intRound, shiftInteger, natSub, natMul, intSub]

def emitAverage (r d Q : ℕ) (i : Fin a) (row : AverageRow (Fin n)) :
    Run (List (IntAtom (Var (Fin n) a r))) := do
  let u ← readSignal Q row.first
  let v ← readSignal Q row.second
  let initial ← emitComparison (.high i 0) (.low i 0) u v
  let js ← CompilerRun.finRange r
  let middle ← CompilerRun.flatMapM (emitRound r d i) js
  let lhs ← readSignal Q row.lhs
  let signal ← step 0 [(Var.high i (Fin.last r), (0 : ℤ))]
  let last ← emitFrom lhs signal
  let lastRows ← step 0 [last]
  let tail ← CompilerRun.append middle lastRows
  CompilerRun.append initial tail

@[simp] private theorem emitAverage_value (d : ℕ) (i : Fin a) (row : AverageRow (Fin n)) :
    (emitAverage r d (CompilationScale.scale d r) i row).value = intAverage d i row := by
  simp [emitAverage, intAverage, List.append_assoc]

private theorem emitComparison_bound {ν : Type} (hi lo : ν) (x y : ν × ℤ) (w : ℕ) :
    (emitComparison hi lo x y).Bound 9 w := ⟨le_rfl, Nat.zero_le _⟩

private theorem emitRound_bound (r d : ℕ) (i : Fin a) (j : Fin r) (w : ℕ)
    (hr : r + 2 ≤ w) (hd : d.size + r + 2 ≤ w) :
    (emitRound (n := n) r d i j).Bound (2*r+18) w := by
  let e := r - (j.val + 1)
  have ej : e ≤ r := Nat.sub_le _ _
  have js : j.val.size ≤ r := (BinarySize.size_le_self _).trans j.isLt.le
  have ns : (j.val + 1).size ≤ r := (BinarySize.size_le_self _).trans j.isLt
  have rs := BinarySize.size_le_self r
  have es := BinarySize.size_le_self e
  have ps : (2^e).size ≤ 1 + e := by
    simpa using BinarySize.size_mul_pow_two_le 1 e
  have zs := BinarySize.size_mul_pow_two_le d e
  have pw := power_width 2 e w (by decide) (by change 2 ≤ w; omega) (by omega) (by omega)
  simp only [emitRound, Run.Bound, Run.bind_slots, Run.bind_width, step_slots, step_value,
    step_width, natSub, natMul, intSub, power_slots, power_value,
    Int.natAbs_natCast, Fin.val_succ, max_le_iff, Int.natAbs_zero, Nat.size_zero, Nat.zero_max]
  change 1 + (1 + (2*e+1 + (1 + (1 + (1 + (1 + 9)))))) ≤ _ ∧ _
  refine ⟨by omega, ?_⟩
  refine ⟨by omega, ⟨by omega, by omega⟩, pw, ⟨by omega, by change (2^e).size ≤ w; omega⟩, ?_, ?_⟩
  · change (d*2^e).size+1 ≤ w
    omega
  · exact Nat.zero_le _

private theorem middle_length (d : ℕ) (i : Fin a) :
    ((List.finRange r).flatMap (intRound (ι := Fin n) d i)).length = 3*r := by
  simp [List.length_flatMap, intRound, intComparison, List.map_const', Nat.mul_comm]

private theorem average_length (d : ℕ) (i : Fin a) (row : AverageRow (Fin n)) :
    (intAverage (r := r) d i row).length = 3*r+4 := by
  simp only [intAverage, List.length_append, middle_length]
  change 3 + 3*r + 1 = _
  omega

private theorem emitAverage_bound (r d Q : ℕ) (i : Fin a) (row : AverageRow (Fin n)) (w : ℕ)
    (hs : row.lhs.offset = 0 ∨ row.lhs.offset = 1)
    (hu : row.first.offset = 0 ∨ row.first.offset = 1)
    (hv : row.second.offset = 0 ∨ row.second.offset = 1)
    (hr : r + 2 ≤ w) (hd : d.size + r + 2 ≤ w) (hq : Q.size + 1 ≤ w) :
    (emitAverage r d Q i row).Bound (40*(r+1)^2) w := by
  let src := intSignal (ι := Fin n) (a := a) (r := r) Q
  let initial := intComparison (.high i 0) (.low i 0) (src row.first) (src row.second)
  let middle := (List.finRange r).flatMap (intRound (ι := Fin n) d i)
  let signal : List (Var (Fin n) a r × ℤ) := [(.high i (Fin.last r), 0)]
  let last := intFrom (src row.lhs) signal
  have ss (t : Term (Fin n)) (ht : t.offset = 0 ∨ t.offset = 1) :=
    signal_bound (a := a) (r := r) Q t ht (by omega : 1 ≤ w) (by omega : Q.size ≤ w)
  have ⟨lus, luw⟩ := ss _ hu
  have ⟨lvs, lvw⟩ := ss _ hv
  have ⟨lls, llw⟩ := ss _ hs
  have ⟨cs, cw⟩ := emitComparison_bound (.high i 0) (.low i 0) (src row.first) (src row.second) w
  have ⟨fs, fw⟩ := (finRange_bound r).weaken le_rfl ((BinarySize.size_le_self _).trans (by omega : r ≤ w))
  have ⟨ms, mw⟩ := flatMapM_bound (emitRound (n := n) r d i) (List.finRange r) (2*r+18) 3 w
    (fun j _ => emitRound_bound r d i j w hr hd) (fun j _ => by rw [emitRound_value]; rfl)
  have ⟨es, ew⟩ := emitFrom_bound (src row.lhs) signal w
    ((Nat.add_le_add_right (signal_weight Q row.lhs) 1).trans hq)
    (by simp [signal]; omega)
  have ⟨as, aw⟩ := append_bound middle [last] w
  have ⟨bs, bw⟩ := append_bound initial (middle ++ [last]) w
  have midLen : middle.length = 3*r := middle_length d i
  have initLen : initial.length = 3 := rfl
  have sigLen : signal.length = 1 := rfl
  rw [List.length_finRange] at ms
  rw [midLen] at as
  rw [initLen] at bs
  rw [sigLen] at es
  simp only [emitAverage, Run.Bound, Run.bind_slots, Run.bind_width,
    step_slots, step_width, step_value, emitComparison_value, readSignal_value,
    flatMapM_value, emitRound_value, finRange_value, emitFrom_value, append_value,
    max_le_iff, Nat.zero_le, true_and]
  refine ⟨?_, luw, lvw, cw, fw, mw, llw, ew, aw, bw⟩
  dsimp only [initial, src, middle, signal, last] at cs ms es as bs
  nlinarith

/-- Pass the measured count to every row constructor. The final cast restores the
public wire type through an erased proof, so one length traversal suffices. -/
def emit (S : System (Fin n)) (count : ℕ) (countEq : count = S.averages.length)
    (s : Fin n) (r d Q : ℕ) (threshold : ℤ) : Run (List (IntAtom (vars S r))) := do
  let ds ← CompilerRun.mapM (emitDiff (a := count) Q) S.differences
  let ms ← CompilerRun.mapM (emitMax (a := count) Q) S.maxima
  let ids ← CompilerRun.finRange count
  let av ← CompilerRun.flatMapM (fun i => do
    let row ← CompilerRun.get S.averages (i.cast countEq)
    emitAverage r d Q i row) ids
  let tail ← CompilerRun.append ms av
  let body ← CompilerRun.append ds tail
  let neg ← intSub 0 threshold
  let ts ← step 0 [(Var.source s, neg)]
  let first ← step 0 (⟨Var.reference, ts⟩ : IntAtom (Var (Fin n) count r))
  step 0 (cast (congrArg (fun k => List (IntAtom (Var (Fin n) k r))) countEq) (first :: body))

private theorem emit_value (S : System (Fin n)) (s : Fin n) (r d count : ℕ)
    (eq : count = S.averages.length) (h : ℤ) :
    (emit S count eq s r d (CompilationScale.scale d r) h).value = intBlock S s d r h := by
  subst count
  simp [emit, intBlock, intSub, List.append_assoc]

private theorem emit_bound (S : System (Fin n)) (s : Fin n) (r d L : ℕ) (h : ℤ)
    (hs : SourceLinearization.AllOffsets (fun q => q = 0 ∨ q = 1) S)
    (nd : S.differences.length ≤ 3*L) (nm : S.maxima.length ≤ L) (na : S.averages.length ≤ L)
    (terms : ∀ row ∈ S.maxima, row.terms.length ≤ L)
    (rd : r ≤ 4*L) (dd : d.size ≤ 2*L) (qq : (CompilationScale.scale d r).size ≤ 7*L)
    (hh : h.natAbs.size ≤ 7*L) :
    (emit S S.averages.length rfl s r d (CompilationScale.scale d r) h).Bound
      (3000*(L+1)^3) (width L) := by
  let Q := CompilationScale.scale d r
  let w := width L
  let ds := S.differences.map (intDiff (a := S.averages.length) (r := r) Q)
  let ms := S.maxima.map (intMax (a := S.averages.length) (r := r) Q)
  let emitOne (i : Fin S.averages.length) := do
    let row ← CompilerRun.get S.averages i
    emitAverage r d Q i row
  let av := (List.finRange S.averages.length).flatMap fun i => intAverage (r := r) d i (S.averages.get i)
  have wq : Q.size + 1 ≤ w := by change (CompilationScale.scale d r).size + 1 ≤ 64*(L+1); omega
  have wr : r + 2 ≤ w := by dsimp [w,width]; omega
  have wd : d.size + r + 2 ≤ w := by dsimp [w,width]; omega
  have hc : S.averages.length.size ≤ w := (BinarySize.size_le_self _).trans (by dsimp [w,width]; omega)
  have hdif := mapM_bound (emitDiff (a := S.averages.length) (r := r) Q) S.differences 13 w
    (fun row mem => emitDiff_bound Q row w (hs.differences row mem).1 (hs.differences row mem).2 wq)
  have hmax := mapM_bound (emitMax (a := S.averages.length) (r := r) Q) S.maxima (9*L+6) w
    (fun row mem => (emitMax_bound Q row w (hs.maxima row mem).1 (hs.maxima row mem).2 wq).weaken
      (by have := terms row mem; omega) le_rfl)
  have hids := (finRange_bound S.averages.length).weaken le_rfl hc
  have hstep (i : Fin S.averages.length) : (emitOne i).Bound (L+1+40*(r+1)^2) w := by
    have mem := hs.averages (S.averages.get i) (List.get_mem _ i)
    apply bound_bind
    · exact (get_bound _ i).weaken (by have := i.isLt; omega) ((Nat.size_le_size i.isLt.le).trans hc)
    · rw [get_value]
      exact emitAverage_bound _ d Q i _ w mem.1 mem.2.1 mem.2.2 wr wd wq
  have hlen (i : Fin S.averages.length) : (emitOne i).value.length ≤ 3*r+4 := by
    simp [emitOne, Q, average_length]
  have hav := flatMapM_bound emitOne (List.finRange S.averages.length) (L+1+40*(r+1)^2) (3*r+4) w
    (fun i _ => hstep i) (fun i _ => hlen i)
  have ham := append_bound ms av w
  have had := append_bound ds (ms ++ av) w
  have neg := (bound_step (max (0 : ℤ).natAbs.size h.natAbs.size + 1) ((0 : ℤ)-h)).weaken
    le_rfl (by dsimp [w,width]; simp; omega : _ ≤ w)
  obtain ⟨dcs, dcw⟩ := hdif
  obtain ⟨mcs, mcw⟩ := hmax
  obtain ⟨ics, icw⟩ := hids
  obtain ⟨acs, acw⟩ := hav
  obtain ⟨ams, amw⟩ := ham
  obtain ⟨ads, adw⟩ := had
  obtain ⟨ncs, ncw⟩ := neg
  simp only [ds, ms, List.length_map] at ams ads
  simp only [List.length_finRange] at acs
  simp only [emit, Run.Bound, Run.bind_slots, Run.bind_width, Run.bind_value, step_slots,
    step_value, step_width, mapM_value, flatMapM_value, finRange_value, get_value,
    emitDiff_value, emitMax_value, emitAverage_value, append_value,
    max_le_iff, Nat.zero_le, and_true, Fin.cast_refl]
  refine ⟨?_, dcw, mcw, icw, acw, amw, adw, ncw⟩
  have m_le := Nat.mul_le_mul_right (9*L+6+2) nm
  have a_le := Nat.mul_le_mul_right (L+1+40*(r+1)^2+(3*r+4)+2) na
  have rp : (r+1)^2 ≤ (4*L+1)^2 := Nat.pow_le_pow_left (by omega) _
  have aq := Nat.mul_le_mul_left L rp
  have ar := Nat.mul_le_mul_left L rd
  apply (Nat.add_le_add dcs (Nat.add_le_add mcs (Nat.add_le_add ics
    (Nat.add_le_add acs (Nat.add_le_add ams (Nat.add_le_add ads
      (Nat.add_le_add ncs (le_refl (1+(1+1)))))))))).trans
  nlinarith only [nd, nm, na, m_le, a_le, aq, ar]

/-- Actual loop bounds used to print the rows and subsequently allocate the wire vertices. -/
structure Prepared (input : ThresholdInput n) (s : Fin n) where
  rounds : ℕ
  count : ℕ
  rows : List (IntAtom (Variables input s))
  rounds_eq : rounds = precision input
  count_eq : count = (system input s).averages.length

/-- The dependent indices of the typed API are certified using erased equations.
The computations supplying their numeric values are sequenced and shared. -/
def prepare (input : ThresholdInput n) (s : Fin n) : Run (Prepared input s) :=
  let p := parameters input
  let sys := readSystem input
  let len := CompilerRun.length sys.value.averages
  have hlen : len.value = sys.value.averages.length := length_value _
  let main := emit sys.value len.value hlen s p.value.rounds p.value.denominator p.value.scale p.value.cutoff
  have hr : p.value.rounds = precision input := congrArg Parameters.rounds (parameters_value input)
  have hc : len.value = (system input s).averages.length :=
    hlen.trans (congrArg (fun S => S.averages.length) (readSystem_value input))
  have heq : vars sys.value p.value.rounds = Variables input s := by
    rw [hr, readSystem_value]
    rfl
  ⟨⟨p.value.rounds, len.value, cast (congrArg (fun α : Type => List (IntAtom α)) heq) main.value,
      hr, hc⟩,
    p.work.seq (sys.work.seq (len.work.seq (main.work.seq (Work.one 0))))⟩

private theorem emit_at_parameters (input : ThresholdInput n) (s : Fin n)
    (p : Parameters) (hp : p = ⟨SourcePrecision.D n input.denominator, precision input,
      integerScale input, cutoffInteger input⟩)
    (S : System (Fin n)) (hs : S = base input.rows.get) (count : ℕ) (hc : count = S.averages.length) :
    HEq (emit S count hc s p.rounds p.denominator p.scale p.cutoff).value (integerRows input s) := by
  subst p S count
  apply heq_of_eq
  exact (emit_value _ s _ _ _ rfl _).trans (block_matches input s)

private theorem emit_work_at_parameters (input : ThresholdInput n) (s : Fin n)
    (p : Parameters) (hp : p = ⟨SourcePrecision.D n input.denominator, precision input,
      integerScale input, cutoffInteger input⟩)
    (S : System (Fin n)) (hs : S = base input.rows.get) (count : ℕ) (hc : count = S.averages.length) :
    (emit S count hc s p.rounds p.denominator p.scale p.cutoff).work =
    (emit (base input.rows.get) (base input.rows.get).averages.length rfl s (precision input)
      (SourcePrecision.D n input.denominator) (integerScale input) (cutoffInteger input)).work := by
  subst p S count
  rfl

@[simp] theorem prepare_rows (input : ThresholdInput n) (s : Fin n) :
    (prepare input s).value.rows = integerRows input s := by
  apply eq_of_heq
  exact (cast_heq _ _).trans (emit_at_parameters input s _ (parameters_value input)
    _ (readSystem_value input) _ (length_value _))

theorem parameters_bound (input : ThresholdInput n) (pos : 0 < input.numerator)
    (interior : input.numerator ≤ input.denominator) :
    (parameters input).Bound (64 * (CompilationCost.inputLength input + 1))
      (width (CompilationCost.inputLength input)) := by
  let L := CompilationCost.inputLength input
  let P := 3 ^ (n+1)
  let d := input.denominator * P
  let r := d.size + 2 * (n+1)
  let v := 2 ^ (r+1)
  let Q := d * v
  obtain ⟨hn, _, hb, ha⟩ := input_bounds input
  change n ≤ L at hn
  change input.denominator.size ≤ L at hb
  change input.numerator.natAbs.size ≤ L at ha
  have bd : d.size ≤ 2*L := CompilationCost.D_size_le input
  have br : r ≤ 4*L := CompilationCost.depth_le input
  have bQ : Q.size ≤ 7*L := CompilationCost.scale_size_le input
  have Ppos : 0 < P := pow_pos (by decide) _
  have dpos : 0 < d := Nat.mul_pos input.denominator_pos Ppos
  have P_le : P ≤ d := Nat.le_mul_of_pos_left P input.denominator_pos
  have v_le : v ≤ Q := Nat.le_mul_of_pos_left v dpos
  have bP := (Nat.size_le_size P_le).trans bd
  have bv := (Nat.size_le_size v_le).trans bQ
  have hdiff : 0 ≤ (input.denominator : ℤ) - input.numerator := by omega
  have hsmall : (input.denominator : ℤ) - input.numerator < input.denominator := by omega
  have hprod : 0 ≤ ((input.denominator : ℤ) - input.numerator) * (P : ℤ) :=
    mul_nonneg hdiff (Int.natCast_nonneg _)
  have prodlt : ((input.denominator : ℤ) - input.numerator) * (P : ℤ) < (d : ℤ) := by
    dsimp only [d]
    rw [Nat.cast_mul]
    exact mul_lt_mul_of_pos_right hsmall (by exact_mod_cast Ppos)
  have incrsize : (((input.denominator : ℤ) - input.numerator) * (P : ℤ) + 1).natAbs.size ≤ d.size := by
    apply Nat.size_le_size
    omega
  have prodsize : (((input.denominator : ℤ) - input.numerator) * (P : ℤ)).natAbs.size ≤ d.size := by
    apply Nat.size_le_size
    omega
  have diffsize : ((input.denominator : ℤ) - input.numerator).natAbs.size ≤ input.denominator.size := by
    apply Nat.size_le_size
    omega
  have wt (k : ℕ) (hk : k ≤ 7*L+10) : k ≤ width L := by unfold width; omega
  have wn := BinarySize.size_le_self n
  have wn1 := BinarySize.size_le_self (n+1)
  have wdim := BinarySize.size_le_self (2*(n+1))
  have wd := BinarySize.size_le_self d.size
  have wr := BinarySize.size_le_self r
  have wr1 := BinarySize.size_le_self (r+1)
  have pow3width := power_width 3 (n+1) (width L) (by decide) (wt _ (by change 2 ≤ 7*L+10; omega))
    (wt _ (by omega)) (wt _ (by change P.size ≤ _; omega))
  have pow2width := power_width 2 (r+1) (width L) (by decide) (wt _ (by change 2 ≤ 7*L+10; omega))
    (wt _ (by omega)) (wt _ (by change v.size ≤ _; omega))
  constructor
  · simp only [parameters, natAdd, natMul, intAdd, intSub, intMul, Run.bind_slots,
      power_slots, power_value, step_value, step_slots]
    change 1 + (2*(n+1)+1 + (1 + (1 + (1 + (1 + (1 + (2*(r+1)+1 + _))))))) ≤ _
    omega
  · simp only [parameters, natAdd, natMul, intAdd, intSub, intMul, Run.bind_width,
      step_width, step_value, power_value, max_le_iff, Int.natAbs_natCast]
    change (n.size ≤ width L ∧ (1 : ℕ).size ≤ width L) ∧
      (smallPower 3 (n+1)).work.width ≤ width L ∧
      (input.denominator.size ≤ width L ∧ P.size ≤ width L) ∧ d.size ≤ width L ∧
      ((2 : ℕ).size ≤ width L ∧ (n+1).size ≤ width L) ∧
      (d.size.size ≤ width L ∧ (2*(n+1)).size ≤ width L) ∧
      (r.size ≤ width L ∧ (1 : ℕ).size ≤ width L) ∧
      (smallPower 2 (r+1)).work.width ≤ width L ∧
      (d.size ≤ width L ∧ v.size ≤ width L) ∧
      max input.denominator.size input.numerator.natAbs.size + 1 ≤ width L ∧
      max ((input.denominator : ℤ) - input.numerator).natAbs.size P.size + 1 ≤ width L ∧
      max (((input.denominator : ℤ) - input.numerator) * (P : ℤ)).natAbs.size 1 + 1 ≤ width L ∧
      max (((input.denominator : ℤ) - input.numerator) * (P : ℤ) + 1).natAbs.size v.size + 1 ≤ width L ∧
      0 ≤ width L
    change (n.size ≤ width L ∧ 1 ≤ width L) ∧ _
    have two : (2 : ℕ).size ≤ width L := wt _ (by change 2 ≤ _; omega)
    have one : (1 : ℕ).size ≤ width L := wt _ (by change 1 ≤ _; omega)
    unfold width at *
    omega

/-- An explicit polynomial for the full row generation, including all source and wire traversals. -/
def slots (L : ℕ) : ℕ := 100000 * (L+1)^4

theorem prepare_bound (input : ThresholdInput n) (s : Fin n) (pos : 0 < input.numerator)
    (interior : input.numerator ≤ input.denominator) :
    (prepare input s).Bound (slots (CompilationCost.inputLength input))
      (width (CompilationCost.inputLength input)) := by
  let L := CompilationCost.inputLength input
  let S := base input.rows.get
  let d := SourcePrecision.D n input.denominator
  let r := precision input
  have ⟨hn, hm, _, _⟩ := input_bounds input
  change n ≤ L at hn
  change CompilationCounts.moveCount input.rows.get ≤ L at hm
  have nd := CompilationCounts.difference_count_le input.rows.get s 0
  change S.differences.length + 1 ≤ 2*n+1+CompilationCounts.moveCount input.rows.get at nd
  have nm : S.maxima.length ≤ n := CompilationCounts.maxima_count_le input.rows.get s 0
  have na : S.averages.length ≤ n := CompilationCounts.average_count_le input.rows.get s 0
  have nt : CompilationCounts.maxTerms S ≤ CompilationCounts.moveCount input.rows.get :=
    CompilationCounts.maxTerms_le input.rows.get s 0
  have terms (row) (hr : row ∈ S.maxima) : row.terms.length ≤ L :=
    (List.le_sum_of_mem (List.mem_map_of_mem (f := fun m : MaxRow (Fin n) => m.terms.length) hr)).trans (nt.trans hm)
  have wA : S.averages.length.size ≤ width L :=
    (BinarySize.size_le_self _).trans (by dsimp [width]; omega)
  have hu := cutoff_in_unit input pos (le_of_not_gt fun ht =>
    (not_lt_of_ge interior) (input.one_lt_threshold_iff.mp ht))
  have hne : (0 : ℚ) ≤ (cutoffInteger input : ℚ) := by
    rw [← scaled_cutoff]
    exact mul_nonneg (Nat.cast_nonneg _) hu.1
  have hle : (cutoffInteger input : ℚ) ≤ (integerScale input : ℚ) := by
    rw [← scaled_cutoff]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) hu.2
  have hne' : 0 ≤ cutoffInteger input := by exact_mod_cast hne
  have hle' : cutoffInteger input ≤ (integerScale input : ℤ) := by exact_mod_cast hle
  have hsize : (cutoffInteger input).natAbs.size ≤ (integerScale input).size := by
    apply Nat.size_le_size
    omega
  have sq : (integerScale input).size ≤ 7*L := CompilationCost.scale_size_le _
  have main := emit_bound S s r d L (cutoffInteger input) (base_zero_one input s)
    (by omega) (nm.trans hn) (na.trans hn) terms (CompilationCost.depth_le input)
    (CompilationCost.D_size_le input) sq (hsize.trans sq)
  have ⟨pc, pw⟩ := parameters_bound input pos interior
  have ⟨sc, sw⟩ := readSystem_bound input
  have ⟨lc, lw⟩ := (length_bound S.averages).weaken le_rfl wA
  obtain ⟨ec, ew⟩ := main
  have he := emit_work_at_parameters input s (parameters input).value (parameters_value input)
    (readSystem input).value (readSystem_value input)
    (CompilerRun.length (readSystem input).value.averages).value (length_value _)
  have hlen : (CompilerRun.length (readSystem input).value.averages).work =
      (CompilerRun.length S.averages).work := by rw [readSystem_value]
  simp only [prepare, Run.Bound, Work.seq, Work.one, he, hlen, max_le_iff, Nat.zero_le, and_true]
  refine ⟨?_, pw, sw, lw, ew⟩
  change (parameters input).work.slots + ((readSystem input).work.slots +
    ((CompilerRun.length S.averages).work.slots +
    ((emit S S.averages.length rfl s r d (integerScale input) (cutoffInteger input)).work.slots + 1))) ≤ slots L
  change (parameters input).work.slots ≤ 64*(L+1) at pc
  change (readSystem input).work.slots ≤ 40*(L+1)^2 at sc
  apply (Nat.add_le_add pc (Nat.add_le_add sc (Nat.add_le_add lc (Nat.add_le_add ec (le_refl 1))))).trans
  unfold slots
  have powBound (j : ℕ) (hj : j ≤ 4) : (L+1)^j ≤ (L+1)^4 :=
    Nat.pow_le_pow_right (by omega) hj
  have p1 : L+1 ≤ (L+1)^4 := by simpa using powBound 1 (by decide)
  have p2 := powBound 2 (by decide)
  have p3 := powBound 3 (by decide)
  omega

end StochasticGames.CostedRows
