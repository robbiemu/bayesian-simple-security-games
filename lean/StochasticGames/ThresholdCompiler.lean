module

public import StochasticGames.ThresholdInput
public import StochasticGames.SourcePrecision
public import StochasticGames.CompilationScale
public import StochasticGames.CompilationCounts
public import StochasticGames.ArenaEncoding
import all StochasticGames.AtomArena
import all StochasticGames.ArenaEncoding
import all StochasticGames.CompilationScale
import all StochasticGames.MeanPayoffGame
import all StochasticGames.ThresholdInput
import Mathlib.Tactic.Linarith

/-! # The encoder at a nonterminal start

These are the actual rows, arena, and output table. The two precision arguments
prove correctness of the constants computed here.
-/

@[expose] public section
namespace StochasticGames.ThresholdCompiler

open AtomEncoding CompilationCounts CompilationScale IntegerAtoms MeanPayoff SourcePrecision

variable {n : ℕ} (input : ThresholdInput n) (s : Fin n)

def precision : ℕ := depth n input.denominator

def integerScale : ℕ := scale (D n input.denominator) (precision input)

def system : AverageFeasibility.System (Fin n) :=
  SourceRows.tightened input.rows.get s (cutoff n input.denominator input.threshold)

abbrev Variables := vars (system input s) (precision input)

def weightedRows : List (Atom (Variables input s)) :=
  allAtoms (system input s) 1 (precision input)

def integerRows : List (IntAtom (Variables input s)) :=
  encodeAt (integerScale input) (weightedRows input s)

abbrev Vertices := AtomArena.Vertex (integerRows input s)
abbrev Arcs := AtomArena.Edge (integerRows input s)

def intermediate : Game (Vertices input s) (Arcs input s) := by
  letI : Nonempty (Variables input s) := ⟨.reference⟩
  exact AtomArena.game (integerRows input s)
    (encoded_tightened_terms_pos _ _ _ _ _ _)

def final : Game (Vertices input s) (Arcs input s) :=
  (intermediate input s).Swap

def listing : ArenaEncoding.Listing (Variables input s) :=
  ArenaEncoding.compilerVariables n (system input s).averages.length (precision input)

def table : ArenaEncoding.Table :=
  ArenaEncoding.table (listing input s) (integerRows input s) true

theorem table_represents : (table input s).Represents (final input s) none := by
  let _ : Nonempty (Variables input s) := ⟨.reference⟩
  simpa [table, final, intermediate] using
    ArenaEncoding.table_represents (listing input s) (integerRows input s)
      (encoded_tightened_terms_pos _ _ _ _ _ _) true

theorem cutoff_in_unit (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) :
    0 ≤ cutoff n input.denominator input.threshold ∧
      cutoff n input.denominator input.threshold ≤ 1 := by
  have bpos : (0 : ℚ) < input.denominator := by exact_mod_cast input.denominator_pos
  have grows : input.denominator ≤ D n input.denominator := by
    unfold D
    have power : 0 < (3 : ℕ) ^ (n + 1) := by positivity
    calc
      input.denominator = input.denominator * 1 := (Nat.mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have margin_small :
      1 / (D n input.denominator : ℚ) ≤ 1 / (input.denominator : ℚ) :=
    one_div_le_one_div_of_le bpos (by exact_mod_cast grows)
  have threshold_lower := input.threshold_ge_reciprocal positive
  have margin_nonneg : 0 ≤ 1 / (D n input.denominator : ℚ) := by positivity
  unfold cutoff
  constructor <;> linarith

theorem weighted_offsets (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) :
    ∀ q ∈ atomOffsets (weightedRows input s), Precision.Clears (integerScale input) q ∧ |q| ≤ 1 := by
  let p := cutoff n input.denominator input.threshold
  have pc : Precision.Clears (D n input.denominator) p :=
    cutoff_clears n input.denominator input.threshold input.denominator_pos input.clears_threshold
  apply offsets_bounded
  intro q hq
  refine ⟨SourceLinearization.tightened_offset_clears input.rows.get s p _ pc q hq, ?_⟩
  rcases SourceLinearization.tightened_literal_offsets input.rows.get s p q hq with eq | eq | eq
  · simp [eq]
  · simp [eq]
  · rw [eq]
    exact cutoff_in_unit input positive atMostOne

theorem exact_iff_integer_rows (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) :
    (∃ y, (system input s).Exact y) ↔ ∃ h, RowsHold (integerRows input s) h := by
  have scalePositive : 0 < integerScale input := by
    apply scale_pos
    unfold D
    exact Nat.mul_pos input.denominator_pos (by positivity)
  exact (SourcePrecision.exact_iff_compiled input.rows.get s input.threshold input.denominator
      input.denominator_pos input.clears_threshold).trans
    ((compiled_iff_atoms (system input s) 1 (precision input)).trans
      (feasible_iff_integer_at _ _ scalePositive fun q hq =>
        (weighted_offsets input s positive atMostOne q hq).1))

theorem integer_rows_iff_certificate :
    (∃ h, RowsHold (integerRows input s) h) ↔ (intermediate input s).Certificate none := by
  let _ : Nonempty (Variables input s) := ⟨.reference⟩
  exact AtomArena.rows_iff_certificate _

theorem intermediate_weight_le (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) (arc : Arcs input s) :
    |(intermediate input s).weight arc| ≤ (integerScale input : ℤ) := by
  rcases arc with v | row | ⟨row, j⟩ | v
  · change |(0 : ℤ)| ≤ _
    simp
  · change |(0 : ℤ)| ≤ _
    simp
  · exact integer_offsets_bounded (weightedRows input s) (integerScale input)
      (weighted_offsets input s positive atMostOne) _ (List.get_mem _ row) _ (List.get_mem _ j)
  · change |(0 : ℤ)| ≤ _
    simp

theorem final_weight_le (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) (arc : Arcs input s) :
    |(final input s).weight arc| ≤
      (Fintype.card (Vertices input s) : ℤ) * (integerScale input : ℤ) + 1 := by
  let N := (Fintype.card (Vertices input s) : ℤ)
  let w := (intermediate input s).weight arc
  have Nnonneg : 0 ≤ N := Int.natCast_nonneg _
  change |(-N) * w - 1| ≤ N * (integerScale input : ℤ) + 1
  calc
    |(-N) * w - 1| ≤ |(-N) * w| + 1 := by
      simpa [sub_eq_add_neg] using (abs_add_le ((-N) * w) (-1))
    _ = N * |w| + 1 := by rw [abs_mul, abs_neg, abs_of_nonneg Nnonneg]
    _ ≤ N * (integerScale input : ℤ) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left
        (intermediate_weight_le input s positive atMostOne arc) Nnonneg) le_rfl

theorem table_weight_le (positive : 0 < input.numerator)
    (atMostOne : input.threshold ≤ 1) (a : ArenaEncoding.ArcRecord)
    (member : a ∈ (table input s).arcs) :
    a.weight.natAbs ≤ (table input s).owners.length * integerScale input + 1 := by
  obtain ⟨vertices, arcs, _, _, records⟩ := table_represents input s
  obtain ⟨i, rfl⟩ := List.get_of_mem member
  obtain ⟨e, rfl⟩ := arcs.surjective i
  rw [records e]
  have card : Fintype.card (Vertices input s) = (table input s).owners.length := by
    simpa using Fintype.card_congr vertices
  have bound := final_weight_le input s positive atMostOne e
  rw [card, ← Int.natCast_natAbs] at bound
  exact_mod_cast bound

end StochasticGames.ThresholdCompiler
