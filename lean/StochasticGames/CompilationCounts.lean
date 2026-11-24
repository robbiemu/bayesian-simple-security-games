module

public import StochasticGames.SourceRows
public import StochasticGames.AtomArena
import all StochasticGames.AtomEncoding
import all StochasticGames.IntegerAtoms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-! Counts of move occurrences, generated rows, terms, wires and graph edges in the H4 encoder. -/

@[expose] public section

namespace StochasticGames.CompilationCounts

open AverageFeasibility AtomEncoding IntegerAtoms

variable {ι ν : Type*} {n : ℕ}

/-- Occurrences are counted separately even when they have the same destination. -/
def listedSuccessors : Source.Row ι → ℕ
  | .max _ tail | .min _ tail => 1 + tail.length
  | .chance _ _ => 2

def moveCount (rows : Fin n → Source.Row (Fin n)) : ℕ :=
  ((List.finRange n).map fun i => listedSuccessors (rows i)).sum

def maxTerms (system : System ι) : ℕ :=
  (system.maxima.map fun row => row.terms.length).sum

def rationalTerms (rows : List (Atom ν)) : ℕ := (rows.map fun row => row.terms.length).sum

def integerTerms (rows : List (IntAtom ν)) : ℕ := (rows.map fun row => row.terms.length).sum

private theorem sum_map_mono {α : Type*} (l : List α) {f g : α → ℕ} (h : ∀ a, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact Nat.add_le_add (h a) ih

private theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem sum_map_const_add {α : Type*} (l : List α) (c : ℕ) (f : α → ℕ) :
    (l.map (fun a => c + f a)).sum = c * l.length + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.mul_succ]; omega

theorem difference_count_le (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    (SourceRows.tightened rows s cutoff).differences.length ≤ 2*n + 1 + moveCount rows := by
  have hlocal (i : Fin n) : (SourceRows.choices i (rows i)).length ≤ listedSuccessors (rows i) := by
    cases rows i <;> simp [SourceRows.choices, listedSuccessors, Nat.add_comm]
  have hsum := sum_map_mono (List.finRange n) hlocal
  simp only [SourceRows.tightened, SourceRows.base, List.length_cons, List.length_flatMap,
    List.length_append, SourceRows.box, List.length_nil, sum_map_const_add,
    List.length_finRange, moveCount] at *
  omega

theorem maxima_count_le (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    (SourceRows.tightened rows s cutoff).maxima.length ≤ n := by
  have hlocal (i : Fin n) : (SourceRows.maxima i (rows i)).length ≤ 1 := by
    cases rows i <;> simp [SourceRows.maxima]
  simpa [SourceRows.tightened, SourceRows.base, List.length_flatMap, List.map_const'] using
    sum_map_mono (List.finRange n) hlocal

theorem average_count_le (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    (SourceRows.tightened rows s cutoff).averages.length ≤ n := by
  have hlocal (i : Fin n) : (SourceRows.averages i (rows i)).length ≤ 1 := by
    cases rows i <;> simp [SourceRows.averages]
  simpa [SourceRows.tightened, SourceRows.base, List.length_flatMap, List.map_const'] using
    sum_map_mono (List.finRange n) hlocal

theorem maxTerms_le (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    maxTerms (SourceRows.tightened rows s cutoff) ≤ moveCount rows := by
  have hlocal (i : Fin n) :
      ((SourceRows.maxima i (rows i)).map fun a => a.terms.length).sum ≤ listedSuccessors (rows i) := by
    cases rows i <;> simp [SourceRows.maxima, listedSuccessors, Nat.add_comm]
  simpa [SourceRows.tightened, SourceRows.base, maxTerms, moveCount, sum_map_flatMap] using
    sum_map_mono (List.finRange n) hlocal

theorem tightened_max_terms_pos (rows : Fin n → Source.Row (Fin n)) (s : Fin n) (cutoff : ℚ) :
    ∀ a ∈ (SourceRows.tightened rows s cutoff).maxima, 0 < a.terms.length := by
  change ∀ a ∈ (List.finRange n).flatMap (fun i => SourceRows.maxima i (rows i)), _
  rw [List.forall_mem_flatMap]
  intro i _
  cases rows i <;> simp [SourceRows.maxima]

private theorem average_terms_pos {r : ℕ} (width : ℚ) (i : Fin n) (a : AverageRow ι) :
    ∀ b ∈ averageAtoms (rounds := r) width i a, 0 < b.terms.length := by
  rw [averageAtoms, List.forall_mem_append, List.forall_mem_append, List.forall_mem_flatMap]
  simp [initialRows, roundRows, finalRow, comparison, fromSignals]

theorem allAtoms_terms_pos (sys : System ι) (width : ℚ) (r : ℕ)
    (hm : ∀ a ∈ sys.maxima, 0 < a.terms.length) :
    ∀ a ∈ allAtoms sys width r, 0 < a.terms.length := by
  rw [allAtoms, List.forall_mem_append, List.forall_mem_append, List.forall_mem_flatMap,
    List.forall_mem_map, List.forall_mem_map]
  refine ⟨⟨fun _ _ => by simp [fromSignals], ?_⟩, fun i _ => average_terms_pos width i _⟩
  intro a ha
  simpa [fromSignals] using hm a ha

theorem encodeAt_term_lengths (D : ℕ) (rows : List (Atom ν)) :
    ((encodeAt D rows).map fun a => a.terms.length) = (rows.map fun a => a.terms.length) := by
  simp [encodeAt, integerAtom, List.map_map, Function.comp_def]

@[simp] theorem encodeAt_termCount (D : ℕ) (rows : List (Atom ν)) :
    integerTerms (encodeAt D rows) = rationalTerms rows :=
  congrArg List.sum (encodeAt_term_lengths D rows)

@[simp] theorem encodeAt_rowCount (D : ℕ) (rows : List (Atom ν)) :
    (encodeAt D rows).length = rows.length := by simp [encodeAt]

theorem encoded_tightened_terms_pos (rows : Fin n → Source.Row (Fin n)) (s : Fin n)
    (cutoff width : ℚ) (r D : ℕ) :
    ∀ i : AtomArena.Row (encodeAt D (allAtoms (SourceRows.tightened rows s cutoff) width r)),
      0 < ((encodeAt D (allAtoms (SourceRows.tightened rows s cutoff) width r)).get i).terms.length := by
  intro i
  let atoms := allAtoms (SourceRows.tightened rows s cutoff) width r
  have h := List.get_mem (encodeAt D atoms) i
  obtain ⟨a, ha, heq⟩ := List.mem_map.mp h
  change 0 < ((encodeAt D atoms).get i).terms.length
  rw [← heq]
  simpa [integerAtom] using
    allAtoms_terms_pos _ width r (tightened_max_terms_pos rows s cutoff) a ha

private theorem averageAtoms_terms {r : ℕ} (width : ℚ) (i : Fin n) (a : AverageRow ι) :
    rationalTerms (averageAtoms (rounds := r) width i a) = 4*r + 5 := by
  simp [rationalTerms, averageAtoms, initialRows, roundRows, finalRow, comparison, fromSignals,
    sum_map_flatMap, List.map_const']
  omega

/-- The three comparator rows have 2, 1 and 1 terms. The final tie contributes one. -/
theorem allAtoms_termCount (sys : System ι) (width : ℚ) (r : ℕ) :
    rationalTerms (allAtoms sys width r) =
      sys.differences.length + maxTerms sys + sys.averages.length * (4*r + 5) := by
  have ha (i : Fin sys.averages.length) :
      ((averageAtoms (rounds := r) width i sys.averages[i.val]).map fun a => a.terms.length).sum =
        4*r + 5 := averageAtoms_terms _ _ _
  simp [allAtoms, rationalTerms, maxTerms, sum_map_flatMap, ha, List.map_map,
    Function.comp_def, fromSignals, List.map_const', Nat.add_assoc]

theorem encoded_rowCount (sys : System ι) (width : ℚ) (r D : ℕ) :
    (encodeAt D (allAtoms sys width r)).length =
      sys.differences.length + sys.maxima.length + sys.averages.length * (3*r + 4) := by
  rw [encodeAt_rowCount, allAtoms_length]

theorem encoded_termCount (sys : System ι) (width : ℚ) (r D : ℕ) :
    integerTerms (encodeAt D (allAtoms sys width r)) =
      sys.differences.length + maxTerms sys + sys.averages.length * (4*r + 5) := by
  rw [encodeAt_termCount, allAtoms_termCount]

private def variableEquiv (ι : Type*) (a r : ℕ) :
    Var ι a r ≃ Option (ι ⊕ (Bool × Fin a × Fin (r+1))) where
  toFun
    | .reference => none
    | .source i => some (.inl i)
    | .high i j => some (.inr (true,i,j))
    | .low i j => some (.inr (false,i,j))
  invFun
    | none => .reference
    | some (.inl i) => .source i
    | some (.inr (true,i,j)) => .high i j
    | some (.inr (false,i,j)) => .low i j
  left_inv v := by cases v <;> rfl
  right_inv v := by
    rcases v with _ | (i | ⟨b,i,j⟩)
    · rfl
    · rfl
    · cases b <;> rfl

theorem vars_card [Fintype ι] (sys : System ι) (r : ℕ) :
    Fintype.card (vars sys r) = 1 + Fintype.card ι + 2 * sys.averages.length * (r+1) := by
  rw [Fintype.card_congr (variableEquiv ι sys.averages.length r)]
  simp
  ring

theorem vertex_card [Fintype ν] (rows : List (IntAtom ν)) :
    Fintype.card (AtomArena.Vertex rows) = 1 + Fintype.card ν + rows.length := by
  simp [AtomArena.Vertex, AtomArena.Row]
  omega

private theorem sum_get_term_lengths (rows : List (IntAtom ν)) :
    (∑ r : Fin rows.length, (rows.get r).terms.length) = integerTerms rows := by
  rw [Fin.sum_univ_def]
  change ((List.finRange rows.length).map ((fun a : IntAtom ν => a.terms.length) ∘ rows.get)).sum = _
  rw [← List.map_map, List.map_get_finRange]
  rfl

theorem edge_card_le [Fintype ν] (rows : List (IntAtom ν)) :
    Fintype.card (AtomArena.Edge rows) ≤ 2 * Fintype.card ν + rows.length + integerTerms rows := by
  classical
  have hi : Fintype.card (AtomArena.Isolated rows) ≤ Fintype.card ν := Fintype.card_subtype_le _
  simp only [AtomArena.Edge, AtomArena.Row, AtomArena.Term, Fintype.card_sum,
    Fintype.card_sigma, Fintype.card_fin, sum_get_term_lengths]
  omega

/-- The number of vertices plus edges is linear in the input moves and the comparator
rounds at the chance states. The formula counts every repeated move occurrence. -/
theorem tightened_graph_size (rows : Fin n → Source.Row (Fin n)) (s : Fin n)
    (cutoff width : ℚ) (r D : ℕ) :
    let sys := SourceRows.tightened rows s cutoff
    let atoms := encodeAt D (allAtoms sys width r)
    Fintype.card (AtomArena.Vertex atoms) + Fintype.card (AtomArena.Edge atoms) ≤
      7 + 11*n + 4*moveCount rows + sys.averages.length * (16*r + 19) := by
  let sys := SourceRows.tightened rows s cutoff
  let atoms := encodeAt D (allAtoms sys width r)
  change Fintype.card (AtomArena.Vertex atoms) + Fintype.card (AtomArena.Edge atoms) ≤ _
  have hd : sys.differences.length ≤ 2*n + 1 + moveCount rows := difference_count_le rows s cutoff
  have hm : sys.maxima.length ≤ n := maxima_count_le rows s cutoff
  have ht : maxTerms sys ≤ moveCount rows := maxTerms_le rows s cutoff
  calc
    _ ≤ 1 + 3 * Fintype.card (vars sys r) + 2 * atoms.length + integerTerms atoms := by
      rw [vertex_card]
      have he := edge_card_le atoms
      omega
    _ = 4 + 3*n + 3*sys.differences.length + 2*sys.maxima.length + maxTerms sys +
        sys.averages.length * (16*r + 19) := by
      dsimp only [atoms]
      rw [vars_card, Fintype.card_fin, encoded_rowCount, encoded_termCount]
      ring
    _ ≤ 7 + 11*n + 4*moveCount rows + sys.averages.length * (16*r + 19) := by omega

end StochasticGames.CompilationCounts
