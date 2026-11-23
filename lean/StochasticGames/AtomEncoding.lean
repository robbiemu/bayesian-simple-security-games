module

public import StochasticGames.MaxAverageReduction
import all StochasticGames.AverageFeasibility
import all StochasticGames.ShiftedComparisons
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith

/-! ## The explicit list of weighted max-atoms

Original variables keep their names. A reference variable supplies literal
values. Every average gets fresh wires indexed by its row and its comparison
round. A max gate gives one row and a min gate gives two difference rows.
-/

public section

namespace StochasticGames.AtomEncoding

open AverageFeasibility ShiftedComparisons

variable {ι ν : Type*}

abbrev Signal (ν : Type*) := ν × ℚ

def Signal.value (signal : Signal ν) (v : ν → ℚ) : ℚ :=
  v signal.1 + signal.2

structure Atom (ν : Type*) where
  lhs : ν
  terms : List (Signal ν)

def Atom.Holds (atom : Atom ν) (v : ν → ℚ) : Prop :=
  ∃ term ∈ atom.terms, v atom.lhs ≤ Signal.value term v

def RowsHold (rows : List (Atom ν)) (v : ν → ℚ) : Prop :=
  ∀ atom ∈ rows, atom.Holds v

def fromSignals (lhs : Signal ν) (terms : List (Signal ν)) : Atom ν :=
  ⟨lhs.1, terms.map fun term => (term.1, term.2 - lhs.2)⟩

private theorem fromSignals_holds (lhs : Signal ν) (terms : List (Signal ν)) (v : ν → ℚ) :
    (fromSignals lhs terms).Holds v ↔
      ∃ term ∈ terms, Signal.value lhs v ≤ Signal.value term v := by
  constructor
  · rintro ⟨_, mem, inequality⟩
    obtain ⟨term, termMem, rfl⟩ := List.mem_map.mp mem
    exact ⟨term, termMem, by
      dsimp [fromSignals, Signal.value] at inequality ⊢
      linarith⟩
  · rintro ⟨term, termMem, inequality⟩
    refine ⟨(term.1, term.2 - lhs.2), List.mem_map.mpr ⟨term, termMem, rfl⟩, ?_⟩
    dsimp [fromSignals, Signal.value] at inequality ⊢
    linarith

private theorem one_term_holds (lhs rhs : Signal ν) (v : ν → ℚ) :
    (fromSignals lhs [rhs]).Holds v ↔ Signal.value lhs v ≤ Signal.value rhs v := by
  rw [fromSignals_holds]
  simp

private theorem translated_preserves_rows (rows : List (Atom ν)) (v : ν → ℚ) (c : ℚ)
    (holds : RowsHold rows v) : RowsHold rows (fun i => v i - c) := by
  intro row mem
  obtain ⟨term, termMem, le⟩ := holds row mem
  refine ⟨term, termMem, ?_⟩
  dsimp [Signal.value] at le ⊢
  linarith

/-- Wire names are private to an occurrence of an average row. -/
inductive Var (ι : Type*) (averages rounds : ℕ) where
  | reference
  | source : ι → Var ι averages rounds
  | high : Fin averages → Fin (rounds + 1) → Var ι averages rounds
  | low : Fin averages → Fin (rounds + 1) → Var ι averages rounds
  deriving DecidableEq, Fintype

variable {n rounds : ℕ}

def sourceSignal (t : Term ι) : Signal (Var ι n rounds) :=
  (t.index.elim .reference .source, t.offset)

private theorem sourceSignal_value (t : Term ι) (v : Var ι n rounds → ℚ)
    (normalized : v .reference = 0) :
    Signal.value (sourceSignal t) v = t.value (fun i => v (.source i)) := by
  obtain ⟨idx, offset⟩ := t
  cases idx <;> simp [Signal.value, sourceSignal, Term.value, normalized]

def comparison (high low : ν) (a b : Signal ν) : List (Atom ν) :=
  [fromSignals (high, 0) [a, b], fromSignals (low, 0) [a], fromSignals (low, 0) [b]]

private theorem comparison_holds (high low : ν) (a b : Signal ν) (v : ν → ℚ) :
    RowsHold (comparison high low a b) v ↔
      (v high, v low) ≤ sortPair (Signal.value a v) (Signal.value b v) := by
  unfold RowsHold comparison
  rw [List.forall_mem_cons, List.forall_mem_cons, List.forall_mem_cons,
    fromSignals_holds (high, 0), one_term_holds, one_term_holds]
  simp [Prod.le_def, sortPair, le_min_iff, le_max_iff, Signal.value]

def initialRows (i : Fin n) (row : AverageRow ι) : List (Atom (Var ι n rounds)) :=
  comparison (.high i 0) (.low i 0) (sourceSignal row.first) (sourceSignal row.second)

def roundRows (width : ℚ) (i : Fin n) (j : Fin rounds) : List (Atom (Var ι n rounds)) :=
  comparison (.high i j.succ) (.low i j.succ)
    (.high i j.castSucc, -(gapBound width j.val / 4))
    (.low i j.castSucc, gapBound width j.val / 4)

def finalRow (i : Fin n) (row : AverageRow ι) : Atom (Var ι n rounds) :=
  fromSignals (sourceSignal row.lhs) [(.high i (Fin.last rounds), 0)]

def averageAtoms (width : ℚ) (i : Fin n) (row : AverageRow ι) :
    List (Atom (Var ι n rounds)) :=
  initialRows i row ++ (List.finRange rounds).flatMap (roundRows width i) ++ [finalRow i row]

def readTrace (v : Var ι n rounds → ℚ) (i : Fin n) (j : Fin (rounds + 1)) : ℚ × ℚ :=
  (v (.high i j), v (.low i j))

private theorem averageAtoms_hold (width : ℚ) (i : Fin n) (row : AverageRow ι)
    (v : Var ι n rounds → ℚ) (normalized : v .reference = 0) :
    RowsHold (averageAtoms width i row) v ↔
      ValidTrace width (row.first.value (fun j => v (.source j)))
        (row.second.value (fun j => v (.source j))) rounds (readTrace v i) ∧
      row.lhs.value (fun j => v (.source j)) ≤ (readTrace v i (Fin.last rounds)).1 := by
  rw [averageAtoms, RowsHold, List.forall_mem_append, List.forall_mem_append,
    List.forall_mem_flatMap]
  change (RowsHold (initialRows i row) v ∧
    (∀ j ∈ List.finRange rounds, RowsHold (roundRows width i j) v)) ∧
      (∀ atom ∈ [finalRow i row], atom.Holds v) ↔ _
  rw [List.forall_mem_singleton]
  simp only [initialRows, roundRows, finalRow, comparison_holds, one_term_holds,
    sourceSignal_value _ _ normalized, List.mem_finRange, true_implies]
  simp only [ValidTrace, readTrace, shiftAndSort, Signal.value, sub_eq_add_neg, add_zero]

abbrev vars (system : System ι) (rounds : ℕ) := Var ι system.averages.length rounds

def allAtoms (system : System ι) (width : ℚ) (rounds : ℕ) :
    List (Atom (vars system rounds)) :=
  (system.differences.map fun r => fromSignals (sourceSignal r.lhs) [sourceSignal r.rhs]) ++
  (system.maxima.map fun r => fromSignals (sourceSignal r.lhs) (r.terms.map sourceSignal)) ++
  (List.finRange system.averages.length).flatMap fun i =>
    averageAtoms width i (system.averages.get i)

private theorem averageAtoms_length (width : ℚ) (i : Fin n) (row : AverageRow ι) :
    (averageAtoms (rounds := rounds) width i row).length = 3 * rounds + 4 := by
  simp [averageAtoms, initialRows, roundRows, comparison, List.length_flatMap,
    List.map_const']
  omega

/-- Three gate rows per round, plus the initial comparator and output tie. -/
theorem allAtoms_length (system : System ι) (width : ℚ) (rounds : ℕ) :
    (allAtoms system width rounds).length =
      system.differences.length + system.maxima.length + system.averages.length * (3 * rounds + 4) := by
  simp [allAtoms, List.length_flatMap, averageAtoms_length, List.map_const', Nat.add_assoc]

private theorem sourceMaximum_holds (row : MaxRow ι) (v : Var ι n rounds → ℚ)
    (normalized : v .reference = 0) :
    (fromSignals (sourceSignal row.lhs) (row.terms.map sourceSignal)).Holds v ↔
      ∃ t ∈ row.terms, row.lhs.value (fun j => v (.source j)) ≤ t.value (fun j => v (.source j)) := by
  rw [fromSignals_holds]
  constructor
  · rintro ⟨signal, mem, inequality⟩
    obtain ⟨t, tMem, rfl⟩ := List.mem_map.mp mem
    exact ⟨t, tMem, by simpa only [sourceSignal_value _ _ normalized] using inequality⟩
  · rintro ⟨t, mem, inequality⟩
    exact ⟨sourceSignal t, List.mem_map.mpr ⟨t, mem, rfl⟩, by
      simpa only [sourceSignal_value _ _ normalized] using inequality⟩

private theorem allAtoms_hold_normalized (system : System ι) (width : ℚ) (rounds : ℕ)
    (v : vars system rounds → ℚ) (normalized : v .reference = 0) :
    RowsHold (allAtoms system width rounds) v ↔
      system.HardRows (fun j => v (.source j)) ∧ system.MaxRows (fun j => v (.source j)) ∧
      ∀ i : Fin system.averages.length,
        let row := system.averages.get i
        ValidTrace width (row.first.value (fun j => v (.source j)))
          (row.second.value (fun j => v (.source j))) rounds (readTrace v i) ∧
        row.lhs.value (fun j => v (.source j)) ≤ (readTrace v i (Fin.last rounds)).1 := by
  rw [allAtoms, RowsHold, List.forall_mem_append, List.forall_mem_append,
    List.forall_mem_map, List.forall_mem_map, List.forall_mem_flatMap]
  change (_ ∧ _) ∧
    (∀ i ∈ List.finRange system.averages.length,
      RowsHold (averageAtoms width i (system.averages.get i)) v) ↔ _
  simp only [one_term_holds, sourceMaximum_holds _ _ normalized,
    sourceSignal_value _ _ normalized, averageAtoms_hold _ _ _ _ normalized,
    List.mem_finRange, true_implies, System.HardRows, System.MaxRows, and_assoc]

/-- The projection of the explicit max-atoms implements the one-sided compiler. -/
theorem compiled_iff_atoms (system : System ι) (width : ℚ) (rounds : ℕ) :
    (∃ x, system.Compiled width rounds x) ↔
      ∃ v : vars system rounds → ℚ, RowsHold (allAtoms system width rounds) v := by
  constructor
  · rintro ⟨x, hard, maxima, means⟩
    have hasTrace (i : Fin system.averages.length) :=
      means (system.averages.get i) (List.get_mem _ i)
    let traces := fun i => Classical.choose (hasTrace i)
    let v : vars system rounds → ℚ := fun k =>
      match k with
      | .reference => 0
      | .source i => x i
      | .high i j => (traces i j).1
      | .low i j => (traces i j).2
    refine ⟨v, (allAtoms_hold_normalized system width rounds v rfl).2 ?_⟩
    exact ⟨hard, maxima, fun i => Classical.choose_spec (hasTrace i)⟩
  · rintro ⟨raw, holds⟩
    let v : vars system rounds → ℚ := fun i => raw i - raw .reference
    have refZero : v .reference = 0 := sub_self _
    have normalized := translated_preserves_rows _ _ (raw .reference) holds
    obtain ⟨hard, maxima, means⟩ :=
      (allAtoms_hold_normalized system width rounds v refZero).1 normalized
    refine ⟨fun j => v (.source j), hard, maxima, ?_⟩
    intro row member
    obtain ⟨i, rfl⟩ := List.get_of_mem member
    exact ⟨readTrace v i, means i⟩

/-- Exact max-average feasibility reduces to the constructed weighted max-atoms
on any bounded input system. -/
theorem exact_iff_atoms [Fintype ι] [DecidableEq ι] (system : System ι) {width : ℚ}
    (widthNonneg : 0 ≤ width) (inputWidths : system.InputsBounded width)
    (bounded : ∃ B : ℚ, ∀ x, system.HardRows x → ∀ i, |x i| ≤ B) :
    (∃ x, system.Exact x) ↔
      ∃ v, RowsHold
        (allAtoms system width (Precision.rounds width (MaxAverageReduction.gap system))) v :=
  (MaxAverageReduction.exact_compilation system widthNonneg inputWidths bounded).trans
    (compiled_iff_atoms system width _)

end StochasticGames.AtomEncoding
