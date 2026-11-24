module

public import StochasticGames.ArenaEncoding
public import StochasticGames.BinarySize
public import StochasticGames.CompilationCounts
public import StochasticGames.CompilationScale
public import StochasticGames.SourcePrecision
public import StochasticGames.ThresholdInput
import all StochasticGames.Precision
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Input length, explicit output size and a binary cost model for H4

The main branch uses the source table, the tightened rows, the dyadic scale and the same
indexed vertex and edge listings as the decision reduction. The bit strings below give
self-delimiting representations of the input and the output table. Natural numbers use a
unary length header followed by their binary digits, and integers have an additional sign bit.
-/

@[expose] public section

namespace StochasticGames.CompilationCost

open CompilationCounts

variable {n : ℕ}

/-- One unit per state and per move, both integer magnitudes in binary, and two delimiters. -/
def inputLength (input : ThresholdInput n) : ℕ :=
  n + moveCount input.rows.get + input.numerator.natAbs.size + input.denominator.size + 2

def natBits (a : ℕ) : List Bool := List.replicate a.size true ++ false :: a.bits

def intBits (z : ℤ) : List Bool := decide (z < 0) :: natBits z.natAbs

def positionBits : Source.Position (Fin n) → List Bool
  | .inl i => false :: natBits i.val
  | .inr b => [true, b]

def sourceRowBits : Source.Row (Fin n) → List Bool
  | .max a l => [false, false] ++ natBits (l.length+1) ++ (a::l).flatMap positionBits
  | .min a l => [false, true] ++ natBits (l.length+1) ++ (a::l).flatMap positionBits
  | .chance a b => [true] ++ positionBits a ++ positionBits b

def inputBits (input : ThresholdInput n) : List Bool :=
  natBits n ++ (List.finRange n).flatMap (fun i => sourceRowBits (input.rows.get i)) ++
    positionBits input.start ++ intBits input.numerator ++ natBits input.denominator

@[simp] theorem natBits_length (a : ℕ) : (natBits a).length = 2*a.size + 1 := by
  simp [natBits, Nat.size_eq_bits_len]
  omega

private theorem positionBits_pos (p : Source.Position (Fin n)) : 0 < (positionBits p).length := by
  cases p <;> simp [positionBits]

private theorem list_length_le_flatMap {α β : Type*} (f : α → List β) (hf : ∀ a, 0 < (f a).length)
    (xs : List α) : xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := hf a
    omega

private theorem row_bits_lower (row : Source.Row (Fin n)) :
    1 + listedSuccessors row ≤ (sourceRowBits row).length := by
  cases row with
  | max a l | min a l =>
    have := list_length_le_flatMap positionBits positionBits_pos (a::l)
    simp only [listedSuccessors, sourceRowBits, List.length_cons, List.length_append,
      List.length_nil, natBits_length] at *
    omega
  | chance a b =>
    have ha := positionBits_pos a
    have hb := positionBits_pos b
    simp only [listedSuccessors, sourceRowBits, List.length_append, List.length_cons, List.length_nil]
    omega

theorem inputLength_le_bits (input : ThresholdInput n) : inputLength input ≤ (inputBits input).length := by
  have hs (xs : List (Fin n)) :
      xs.length + (xs.map fun i => listedSuccessors (input.rows.get i)).sum ≤
        (xs.flatMap fun i => sourceRowBits (input.rows.get i)).length := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      have hrow := row_bits_lower (input.rows.get i)
      simp only [List.length_cons, List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
      omega
  have h := hs (List.finRange n)
  simp only [List.length_finRange] at h
  simp only [inputLength, moveCount, inputBits, intBits, List.length_append, List.length_cons,
    natBits_length]
  omega

theorem D_size_le (input : ThresholdInput n) :
    (SourcePrecision.D n input.denominator).size ≤ 2 * inputLength input := by
  have h := BinarySize.size_mul_pow_three_le input.denominator (n+1)
  unfold SourcePrecision.D inputLength
  omega

theorem depth_le (input : ThresholdInput n) :
    SourcePrecision.depth n input.denominator ≤ 4 * inputLength input := by
  have h := D_size_le input
  unfold SourcePrecision.depth inputLength at *
  omega

abbrev rounds (input : ThresholdInput n) := SourcePrecision.depth n input.denominator
abbrev scale (input : ThresholdInput n) :=
  CompilationScale.scale (SourcePrecision.D n input.denominator) (rounds input)

theorem scale_size_le (input : ThresholdInput n) : (scale input).size ≤ 7 * inputLength input := by
  have hd := D_size_le input
  have hr := depth_le input
  have h := BinarySize.size_mul_pow_two_le (SourcePrecision.D n input.denominator) (rounds input + 1)
  change _ ≤ _ at h
  change ((SourcePrecision.D n input.denominator) * 2 ^ (rounds input + 1)).size ≤ _
  unfold rounds inputLength at *
  omega

abbrev sourceSystem (input : ThresholdInput n) (s : Fin n) :=
  SourceRows.tightened input.rows.get s (SourcePrecision.cutoff n input.denominator input.threshold)

abbrev atomList (input : ThresholdInput n) (s : Fin n) :=
  IntegerAtoms.encodeAt (scale input) (AtomEncoding.allAtoms (sourceSystem input s) 1 (rounds input))

abbrev variableList (input : ThresholdInput n) (s : Fin n) :=
  ArenaEncoding.compilerVariables n (sourceSystem input s).averages.length (rounds input)

def vertexCount (input : ThresholdInput n) (s : Fin n) : ℕ :=
  (ArenaEncoding.vertices (variableList input s) (atomList input s)).items.length

def edgeCount (input : ThresholdInput n) (s : Fin n) : ℕ :=
  (ArenaEncoding.edges (variableList input s) (atomList input s)).items.length

abbrev mainTable (input : ThresholdInput n) (s : Fin n) : ArenaEncoding.Table :=
  ArenaEncoding.table (variableList input s) (atomList input s) true

theorem graph_size_le (input : ThresholdInput n) (s : Fin n) :
    vertexCount input s + edgeCount input s ≤ 128 * inputLength input ^ 2 := by
  rw [vertexCount, edgeCount, ArenaEncoding.Listing.length_eq_card, ArenaEncoding.Listing.length_eq_card]
  have h := tightened_graph_size input.rows.get s (SourcePrecision.cutoff n input.denominator input.threshold)
    1 (rounds input) (scale input)
  refine h.trans ?_
  have ha := average_count_le input.rows.get s (SourcePrecision.cutoff n input.denominator input.threshold)
  have hr := depth_le input
  have hn : n ≤ inputLength input := by unfold inputLength; omega
  have hm : moveCount input.rows.get ≤ inputLength input := by unfold inputLength; omega
  have hp : 1 ≤ inputLength input := by unfold inputLength; omega
  calc
    _ ≤ 7 + 11*inputLength input + 4*inputLength input +
        inputLength input * (16 * (4*inputLength input) + 19) := by
      gcongr
      exact ha.trans hn
    _ ≤ 128 * inputLength input ^ 2 := by nlinarith [Nat.mul_le_mul_right (inputLength input) hp]

private theorem card_size_le {k l : ℕ} (h : k ≤ 128 * l ^ 2) : k.size ≤ 8 + 2*l := by
  have bits := (Nat.size_le_size h).trans (BinarySize.size_mul_le 128 (l^2))
  have sq := BinarySize.size_mul_le l l
  have lx := BinarySize.size_le_self l
  have h128 : Nat.size 128 = 8 := by decide
  norm_num [pow_two] at bits
  omega

theorem weight_bits_le (input : ThresholdInput n) (s : Fin n) (w : ℤ)
    (hw : w.natAbs ≤ vertexCount input s * scale input + 1) :
    w.natAbs.size ≤ 14 * inputLength input := by
  have hg := graph_size_le input s
  have hn := card_size_le (show vertexCount input s ≤ 128 * inputLength input ^ 2 by omega)
  have hq := scale_size_le input
  have ha := (Nat.size_le_size hw).trans (BinarySize.size_succ_le _)
  have hm := BinarySize.size_mul_le (vertexCount input s) (scale input)
  have hp : 2 ≤ inputLength input := by unfold inputLength; omega
  omega

def arcBits (e : ArenaEncoding.ArcRecord) : List Bool :=
  natBits e.src ++ natBits e.dst ++ intBits e.weight

/-- The two list lengths precede their contents, so boundaries are unambiguous. -/
def tableBits (t : ArenaEncoding.Table) : List Bool :=
  natBits t.start ++ natBits t.owners.length ++ t.owners ++ natBits t.arcs.length ++ t.arcs.flatMap arcBits

theorem table_indices (input : ThresholdInput n) (s : Fin n) :
    (mainTable input s).start < vertexCount input s ∧
    ∀ e ∈ (mainTable input s).arcs, e.src < vertexCount input s ∧ e.dst < vertexCount input s := by
  let vs := ArenaEncoding.vertices (variableList input s) (atomList input s)
  refine ⟨(vs.index none).isLt, ?_⟩
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(vs.index (AtomArena.src a)).isLt, (vs.index (AtomArena.dst a)).isLt⟩

theorem table_lengths (input : ThresholdInput n) (s : Fin n) :
    (mainTable input s).owners.length = vertexCount input s ∧
    (mainTable input s).arcs.length = edgeCount input s := by
  exact ⟨List.length_map _, List.length_map _⟩

private theorem flatMap_length_le {α β : Type*} (f : α → List β) (K : ℕ) (xs : List α)
    (h : ∀ x ∈ xs, (f x).length ≤ K) : (xs.flatMap f).length ≤ xs.length * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, one_mul]
    omega

theorem table_bits_le (input : ThresholdInput n) (s : Fin n)
    (hw : ∀ e ∈ (mainTable input s).arcs,
      e.weight.natAbs ≤ vertexCount input s * scale input + 1) :
    (tableBits (mainTable input s)).length ≤ 16000 * inputLength input ^ 3 := by
  let L := inputLength input
  have hp : 2 ≤ L := by dsimp [L, inputLength]; omega
  have hgraph : vertexCount input s + edgeCount input s ≤ 128 * L^2 := graph_size_le input s
  have hv := card_size_le (show vertexCount input s ≤ 128*L^2 by omega)
  have he := card_size_le (show edgeCount input s ≤ 128*L^2 by omega)
  obtain ⟨hstart, hind⟩ := table_indices input s
  have hs := (Nat.size_le_size hstart.le).trans hv
  have harcs := flatMap_length_le arcBits (64*L) (mainTable input s).arcs (by
    intro e em
    have ha := (Nat.size_le_size (hind e em).1.le).trans hv
    have hb := (Nat.size_le_size (hind e em).2.le).trans hv
    have hc := weight_bits_le input s e.weight (hw e em)
    simp only [arcBits, intBits, List.length_append, List.length_cons, natBits_length]
    dsimp only [L] at *
    omega)
  obtain ⟨howners, hedges⟩ := table_lengths input s
  rw [hedges] at harcs
  simp only [tableBits, List.length_append, natBits_length, howners, hedges]
  change _ ≤ 16000 * L ^ 3
  calc
    _ ≤ 3*(2*(8 + 2*L)+1) + vertexCount input s + edgeCount input s * (64*L) := by omega
    _ ≤ 3*(2*(8 + 2*L)+1) + 128*L^2 + (128*L^2) * (64*L) := by
      gcongr <;> omega
    _ ≤ _ := by
      have h2 : L ≤ L*L := by nlinarith [Nat.mul_le_mul_right L (show 1 ≤ L by omega)]
      have h3 := Nat.mul_le_mul_right L h2
      nlinarith

private theorem position_bits_le (p : Source.Position (Fin n)) :
    (positionBits p).length ≤ 2*n+2 := by
  cases p with
  | inr b => simp [positionBits]
  | inl i =>
    have := BinarySize.size_le_self i.val
    have := i.isLt
    simp [positionBits]
    omega

private theorem row_bits_le (row : Source.Row (Fin n)) :
    (sourceRowBits row).length ≤ (1 + listedSuccessors row) * (2*n + 8) := by
  cases row with
  | max a l | min a l =>
    have h := flatMap_length_le positionBits (2*n+2) (a::l) (fun x _ => position_bits_le x)
    have sz := BinarySize.size_le_self (l.length+1)
    simp only [sourceRowBits, List.length_append, List.length_cons, List.length_nil, natBits_length,
      listedSuccessors] at *
    nlinarith
  | chance a b =>
    have ha := position_bits_le a
    have hb := position_bits_le b
    simp only [sourceRowBits, List.length_append, List.length_cons, List.length_nil, listedSuccessors]
    omega

theorem input_bits_le (input : ThresholdInput n) : (inputBits input).length ≤ 30 * inputLength input ^ 2 := by
  have hs (xs : List (Fin n)) :
      (xs.flatMap fun i => sourceRowBits (input.rows.get i)).length ≤
        (xs.length + (xs.map fun i => listedSuccessors (input.rows.get i)).sum) * (2*n+8) := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      have hrow := row_bits_le (input.rows.get i)
      simp only [List.length_cons, List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
      nlinarith
  have h := hs (List.finRange n)
  simp only [List.length_finRange] at h
  have hstart := position_bits_le input.start
  have hns := BinarySize.size_le_self n
  have hr : n + moveCount input.rows.get ≤ inputLength input := by unfold inputLength; omega
  have hn : n ≤ inputLength input := by omega
  have hi : input.numerator.natAbs.size + input.denominator.size ≤ inputLength input := by
    unfold inputLength; omega
  have hl : 1 ≤ inputLength input := by unfold inputLength; omega
  change _ ≤ (n + moveCount input.rows.get) * (2*n+8) at h
  simp only [inputBits, intBits, List.length_append, List.length_cons, natBits_length]
  calc
    _ ≤ 4*n + 2*(input.numerator.natAbs.size + input.denominator.size) + 6 +
        (n + moveCount input.rows.get) * (2*n+8) := by omega
    _ ≤ 4*inputLength input + 2*inputLength input + 6 + inputLength input * (2*inputLength input+8) := by
      gcongr
    _ ≤ 30*inputLength input^2 := by nlinarith [Nat.mul_le_mul_right (inputLength input) hl]

/-! ## Term counts used by the measured arena -/

theorem member_terms_le {ν : Type*} (rows : List (IntegerAtoms.IntAtom ν)) :
    ∀ a ∈ rows, a.terms.length ≤ integerTerms rows := by
  intro a ha
  exact List.le_sum_of_mem (List.mem_map_of_mem ha)

theorem integerTerms_le (input : ThresholdInput n) (s : Fin n) :
    integerTerms (atomList input s) ≤ 128*inputLength input^2 := by
  let L := inputLength input
  have hd := difference_count_le input.rows.get s (SourcePrecision.cutoff n input.denominator input.threshold)
  have hm := maxTerms_le input.rows.get s (SourcePrecision.cutoff n input.denominator input.threshold)
  have hc := average_count_le input.rows.get s (SourcePrecision.cutoff n input.denominator input.threshold)
  have hn : n ≤ L := by dsimp [L, inputLength]; omega
  have hmove : moveCount input.rows.get ≤ L := by dsimp [L, inputLength]; omega
  have hpos : 1 ≤ L := by dsimp [L, inputLength]; omega
  have hr : rounds input ≤ 4*L := depth_le input
  rw [atomList, encoded_termCount]
  calc
    _ ≤ 2*L+1+L + L + L*(4*(4*L)+5) := by
      gcongr
      · exact hd.trans (by omega)
      · exact hm.trans hmove
      · exact hc.trans hn
    _ ≤ _ := by change 2*L+1+L + L + L*(4*(4*L)+5) ≤ 128*L^2
                nlinarith [Nat.mul_le_mul_right L hpos]

/-!
## Reference traversal counts

The earlier size-based estimate accounts for generating and scanning explicit lists. A lookup of the
`k`-th cell charges `k+1` visits. Looking up a vertex identifier uses `List.idxOf`
on the unique complete vertex listing, hence exactly its identifier plus one comparisons.
The row and term lookup charges below apply separately to the destination and the weight.
The isolated-variable test allows a full row scan for each variable, with a fresh list
lookup for every tested row. It makes no assumption of constant-time list indexing.
-/

private theorem sum_map_le_length_mul {α : Type*} (xs : List α) (f : α → ℕ) (K : ℕ)
    (h : ∀ x ∈ xs, f x ≤ K) : (xs.map f).sum ≤ xs.length * K := by
  simpa only [List.length_map, nsmul_eq_mul, Nat.cast_id] using
    List.sum_le_length_nsmul (xs.map f) K (by simpa using h)

/-- Each of the two shifted arguments may recompute all `j` halvings of `gapBound`.
Eight additional visits cover constructing the three comparison rows and four terms. -/
def roundVisits (r : ℕ) : ℕ :=
  ((List.finRange r).map fun j => 2 * (j.val+2) + 8).sum

theorem roundVisits_le (r : ℕ) : roundVisits r ≤ r * (2*r+12) := by
  have h := sum_map_le_length_mul (List.finRange r) (fun j => 2*(j.val+2)+8) (2*r+12)
    (fun j _ => by have := j.isLt; omega)
  simpa [roundVisits] using h

/-- The two identifier scans, the cardinality used in reversal and the row/term lookups
for an actual edge. The final fixed charge covers the signed multiply, subtraction and
record construction. -/
def arcVisits {ν : Type*} [DecidableEq ν] (vs : ArenaEncoding.Listing ν)
    (rows : List (IntegerAtoms.IntAtom ν)) (e : AtomArena.Edge rows) : ℕ :=
  let nodes := ArenaEncoding.vertices vs rows
  let loads := match e with
    | .inl _ => 0
    | .inr (.inl i) => i.val + 1
    | .inr (.inr (.inl ⟨i,j⟩)) => 2*(i.val+1) + 2*(j.val+1)
    | .inr (.inr (.inr _)) => 0
  (nodes.index (AtomArena.src e)).val + 1 + (nodes.index (AtomArena.dst e)).val + 1 +
    nodes.items.length + loads + 16

theorem arcVisits_le {ν : Type*} [DecidableEq ν] (vs : ArenaEncoding.Listing ν)
    (rows : List (IntegerAtoms.IntAtom ν)) (e : AtomArena.Edge rows) :
    arcVisits vs rows e ≤ 3*(ArenaEncoding.vertices vs rows).items.length +
      2*rows.length + 2*integerTerms rows + 16 := by
  let nodes := ArenaEncoding.vertices vs rows
  have hi := (nodes.index (AtomArena.src e)).isLt
  have hj := (nodes.index (AtomArena.dst e)).isLt
  unfold arcVisits
  change _ ≤ 3*nodes.items.length + 2*rows.length + 2*integerTerms rows + 16
  dsimp only [nodes] at *
  rcases e with v | i | ⟨i,j⟩ | v
  · dsimp only; omega
  · have := i.isLt
    dsimp only
    omega
  · have hir := i.isLt
    have hjt := j.isLt
    have hb := member_terms_le rows (rows.get i) (List.get_mem rows i)
    dsimp only
    omega
  · dsimp only; omega

/-- Charges for building the vertex/edge listings and writing every indexed arc.
The `P*R*(R+1)` term covers testing each of `P` variables against each of `R` rows.
The `R*(R+1)` term allows a fresh scan to get each row's reply-list length. -/
def arenaVisits {ν : Type*} [DecidableEq ν] (vs : ArenaEncoding.Listing ν)
    (rows : List (IntegerAtoms.IntAtom ν)) : ℕ :=
  let nodes := ArenaEncoding.vertices vs rows
  let edges := ArenaEncoding.edges vs rows
  let P := vs.items.length
  let R := rows.length
  16*(P + R + integerTerms rows + nodes.items.length + edges.items.length + 1) +
    P * R * (R+1) + R*(R+1) + (edges.items.map (arcVisits vs rows)).sum

private theorem arenaVisits_bound {ν : Type*} [DecidableEq ν] (vs : ArenaEncoding.Listing ν)
    (rows : List (IntegerAtoms.IntAtom ν)) (B : ℕ) (hpos : 1 ≤ B)
    (hp : vs.items.length ≤ B) (hr : rows.length ≤ B) (ht : integerTerms rows ≤ B)
    (hv : (ArenaEncoding.vertices vs rows).items.length ≤ B)
    (he : (ArenaEncoding.edges vs rows).items.length ≤ B) :
    arenaVisits vs rows ≤ 180*(B+1)^3 := by
  let es := (ArenaEncoding.edges vs rows).items
  have arcs : (es.map (arcVisits vs rows)).sum ≤ es.length * (7*B+16) :=
    sum_map_le_length_mul es _ _ fun e _ => (arcVisits_le _ _ _).trans (by omega)
  change es.length ≤ B at he
  unfold arenaVisits
  calc
    _ ≤ 16*(B+B+B+B+B+1) + B*B*(B+1) + B*(B+1) + B*(7*B+16) := by
      dsimp only
      gcongr
      exact arcs.trans (Nat.mul_le_mul_right _ he)
    _ ≤ 180*(B+1)^3 := by nlinarith [Nat.mul_le_mul_right B hpos]

/-- The source passes allow a scan of the input vertex table for every listed occurrence.
The precision stage includes repeated multiplication by three, binary-length reads and
the one-bit shifts constructing the final scale. The circuit stage charges all repeated
gap computations, all indexed average-row reads, and the creation and scaling of each term. -/
def stageVisits (input : ThresholdInput n) (s : Fin n) : ℕ :=
  let sys := sourceSystem input s
  let rs := atomList input s
  let r := rounds input
  let c := sys.averages.length
  let source := 8 * (n + moveCount input.rows.get + 1) * (n+1)
  let precision := 16 * (n + r + input.denominator.size + input.numerator.natAbs.size + 4)
  let circuit := c * (roundVisits r + 2*(c+1) + 12) + 16*(rs.length + integerTerms rs + 1)
  source + precision + circuit + arenaVisits (variableList input s) rs

theorem stageVisits_le (input : ThresholdInput n) (s : Fin n) :
    stageVisits input s ≤ 500 * (128 * inputLength input^2 + 1)^3 := by
  let L := inputLength input
  let B := 128*L^2
  let sys := sourceSystem input s
  let rs := atomList input s
  let vs := variableList input s
  have hL : 2 ≤ L := by dsimp [L, inputLength]; omega
  have hB : 4*L ≤ B := by dsimp [B]; nlinarith [Nat.mul_le_mul_right L hL]
  have hin : n + moveCount input.rows.get + input.denominator.size + input.numerator.natAbs.size ≤ L := by
    dsimp [L, inputLength]; omega
  have hr : rounds input ≤ 4*L := depth_le input
  have hround : rounds input ≤ B := hr.trans hB
  have ha : sys.averages.length ≤ n := average_count_le _ _ _
  have hc : sys.averages.length ≤ B := by omega
  have hV : vertexCount input s + edgeCount input s ≤ B := graph_size_le input s
  have hv : (ArenaEncoding.vertices vs rs).items.length ≤ B := show vertexCount input s ≤ B by omega
  have he : (ArenaEncoding.edges vs rs).items.length ≤ B := show edgeCount input s ≤ B by omega
  have pv := ArenaEncoding.vertices_length vs rs
  have hp : vs.items.length ≤ B := by omega
  have hrows : rs.length ≤ B := by omega
  have ht : integerTerms rs ≤ B := integerTerms_le input s
  have hpos : 1 ≤ B := by omega
  have harena := arenaVisits_bound vs rs B hpos hp hrows ht hv he
  have hfold : roundVisits (rounds input) ≤ B*(2*B+12) := by
    apply (roundVisits_le _).trans
    gcongr
  unfold stageVisits
  calc
    _ ≤ 8*(B+1)*(B+1) + 16*(3*B+4) +
        (B*(B*(2*B+12)+2*(B+1)+12) + 16*(B+B+1)) + 180*(B+1)^3 := by
      dsimp only
      gcongr <;> omega
    _ ≤ 500*(B+1)^3 := by nlinarith

/-- A reduced rational offset uses at most as many bits in either component as the
positive common scale clearing it. This applies to every rational term before flooring. -/
theorem cleared_fields_le {Q : ℕ} {q : ℚ} (hQ : 0 < Q) (hclear : Precision.Clears Q q)
    (habs : |q| ≤ 1) : q.num.natAbs ≤ Q ∧ q.den ≤ Q := by
  obtain ⟨z, hz⟩ := hclear
  have hrepr : q = Rat.divInt z (Q : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, eq_div_iff (by exact_mod_cast hQ.ne')]
    simpa [mul_comm] using hz
  have hd : q.den ≤ Q := Nat.le_of_dvd hQ (Int.natCast_dvd_natCast.mp (by
    rw [hrepr]
    exact Rat.den_dvd _ _))
  have hnum : (q.num.natAbs : ℚ) ≤ q.den := by
    calc
      (q.num.natAbs : ℚ) = ((q.num.natAbs : ℤ) : ℚ) := by simp
      _ = |(q.num : ℚ)| := by rw [Int.natCast_natAbs, Int.cast_abs]
      _ = |q| * (q.den : ℚ) := by
        rw [← q.mul_den_eq_num, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ q.den)]
      _ ≤ 1 * (q.den : ℚ) := mul_le_mul_of_nonneg_right habs (by positivity)
      _ = _ := one_mul _
  exact ⟨(show q.num.natAbs ≤ q.den by exact_mod_cast hnum).trans hd, hd⟩

theorem compiled_offset_bits (input : ThresholdInput n) (s : Fin n)
    (h : ∀ q ∈ MaxAverageReduction.offsets (sourceSystem input s),
      Precision.Clears (SourcePrecision.D n input.denominator) q ∧ (0 ≤ q ∧ q ≤ 1)) :
    ∀ q ∈ IntegerAtoms.atomOffsets (AtomEncoding.allAtoms (sourceSystem input s) 1 (rounds input)),
      q.num.natAbs.size ≤ 7*inputLength input ∧ q.den.size ≤ 7*inputLength input := by
  intro q hq
  obtain ⟨hc, ha⟩ := CompilationScale.offsets_bounded _ _ (rounds input) h q hq
  obtain ⟨hn, hd⟩ := cleared_fields_le
    (CompilationScale.scale_pos (SourcePrecision.D_pos n input.denominator input.denominator_pos)) hc ha
  exact ⟨(Nat.size_le_size hn).trans (scale_size_le input), (Nat.size_le_size hd).trans (scale_size_le input)⟩

private theorem size_add_le (a b : ℕ) : (a+b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have ha := (Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right a.size b.size))
  omega

/-- The unsigned magnitudes of rational cross-products and their sum fit in the
working width before gcd normalization. The triangle inequality applies the same
bound to a signed sum or difference of these products. -/
theorem raw_rational_fields_le (L a b c d : ℕ) (ha : a.size ≤ 14*L) (hb : b.size ≤ 14*L)
    (hc : c.size ≤ 14*L) (hd : d.size ≤ 14*L) :
    (a*d+c*b).size ≤ 64*(L+1) ∧ (b*d).size ≤ 64*(L+1) := by
  have had := BinarySize.size_mul_le a d
  have hcb := BinarySize.size_mul_le c b
  have hbd := BinarySize.size_mul_le b d
  have hs := size_add_le (a*d) (c*b)
  omega

/-- An explicit count for the ordinary Euclidean normalization loop. -/
def euclidDivisions (a b : ℕ) : ℕ :=
  if hz : b = 0 then 0 else 1 + euclidDivisions b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hz)

private theorem twice_second_remainder_lt {a b : ℕ} (hb : 0 < b) (hr : 0 < a%b) :
    2 * (b % (a%b)) < b := by
  let r := a%b
  have hlt : r < b := Nat.mod_lt _ hb
  have hrem : b%r < r := Nat.mod_lt _ hr
  change 2 * (b%r) < b
  by_cases h : 2*r ≤ b
  · omega
  · rw [Nat.mod_eq_sub_mod hlt.le, Nat.mod_eq_of_lt (by omega : b-r < r)]
    omega

private theorem size_lt_of_twice_lt {a b : ℕ} (h : 2*a < b) : a.size < b.size := by
  by_cases ha : a = 0
  · subst a
    simpa using (Nat.size_pos.mpr (show 0 < b by omega))
  · have hs := Nat.size_shiftLeft ha 1
    rw [Nat.shiftLeft_eq_mul_pow] at hs
    simp only [pow_one] at hs
    have hmono := Nat.size_le_size h.le
    rw [Nat.mul_comm 2 a, hs] at hmono
    omega

/-- Within two ordinary divisions the remaining nonzero divisor loses a binary digit. -/
theorem euclidDivisions_le (a b : ℕ) : euclidDivisions a b ≤ 2*b.size := by
  induction b using Nat.strong_induction_on generalizing a with
  | ind b ih =>
    by_cases hb : b = 0
    · simp [euclidDivisions, hb]
    · have hp : 0 < b := Nat.pos_of_ne_zero hb
      rw [euclidDivisions, dite_eq_right hb]
      by_cases hr : a%b = 0
      · rw [hr, euclidDivisions, dite_eq_left rfl]
        have := Nat.size_pos.mpr hp
        omega
      · rw [euclidDivisions, dite_eq_right hr]
        have hg := twice_second_remainder_lt hp (Nat.pos_of_ne_zero hr)
        have hs := size_lt_of_twice_lt hg
        have hh := ih (b%(a%b)) (by omega) (a%b)
        omega

/-- The model charges four bit operations per cell of a width-`W` schoolbook
multiplication or long-division table. Eight such tables cover fixed rational arithmetic
and conversion steps, plus one per Euclidean remainder for normalization. -/
def rationalBitCost (W a b : ℕ) : ℕ := (8 + euclidDivisions a b) * (4 * W^2)

theorem rationalBitCost_le {W a b : ℕ} (hW : 1 ≤ W) (hb : b.size ≤ W) :
    rationalBitCost W a b ≤ 64*W^3 := by
  have hd := euclidDivisions_le a b
  unfold rationalBitCost
  calc
    _ ≤ (8 + 2*W)*(4*W^2) := by gcongr; omega
    _ ≤ 64*W^3 := by nlinarith [Nat.mul_le_mul_right (W^2) hW]

/-- A word slot allows signed indices, threshold and scale operands, products of pairs
of rational numerator/denominator fields, and the signed weight reversal. For the
elementary binary arithmetic model, charge 64 cubic bit operations per slot: two
schoolbook products or long divisions use quadratic work, and Euclidean normalization
can use a linear number of divisions. This cost convention measures the binary
arithmetic algorithm independently of the runtime used to evaluate Lean. -/
def slotBitCost (L : ℕ) : ℕ := 64 * (64*(L+1))^3

theorem rationalBitCost_le_slot (L a b : ℕ) (hb : b.size ≤ 64*(L+1)) :
    rationalBitCost (64*(L+1)) a b ≤ slotBitCost L :=
  rationalBitCost_le (by omega) hb

def bitWork (input : ThresholdInput n) (s : Fin n) : ℕ :=
  (inputBits input).length + stageVisits input s * slotBitCost (inputLength input) +
    (tableBits (mainTable input s)).length

/-- A fixed degree-nine polynomial for the charged encoder, with input parsing and output
serialization charged per bit. -/
def polynomial (L : ℕ) : ℕ :=
  30*L^2 + 500*(128*L^2+1)^3 * slotBitCost L + 16000*L^3

theorem bitWork_polynomial (input : ThresholdInput n) (s : Fin n)
    (hw : ∀ e ∈ (mainTable input s).arcs,
      e.weight.natAbs ≤ vertexCount input s * scale input + 1) :
    bitWork input s ≤ polynomial (inputLength input) := by
  unfold bitWork polynomial
  gcongr
  · exact input_bits_le input
  · exact stageVisits_le input s
  · exact table_bits_le input s hw

theorem bitWork_le_serialized_input (input : ThresholdInput n) (s : Fin n)
    (hw : ∀ e ∈ (mainTable input s).arcs,
      e.weight.natAbs ≤ vertexCount input s * scale input + 1) :
    bitWork input s ≤ polynomial (inputBits input).length := by
  apply (bitWork_polynomial input s hw).trans
  unfold polynomial slotBitCost
  gcongr <;> exact inputLength_le_bits input

end StochasticGames.CompilationCost
