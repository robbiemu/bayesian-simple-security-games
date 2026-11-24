module

public import StochasticGames.AtomEncoding
import all StochasticGames.AtomEncoding
import all StochasticGames.Precision
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! ## Integer weighted max-atoms

Clear all printed offsets with one positive scale. Rounding each scaled
variable down preserves the selected term of every max row.
-/

public section

namespace StochasticGames.IntegerAtoms

open AtomEncoding Precision

variable {ν : Type*}

structure IntAtom (ν : Type*) where
  lhs : ν
  terms : List (ν × ℤ)

def IntAtom.Holds (atom : IntAtom ν) (v : ν → ℤ) : Prop :=
  ∃ term ∈ atom.terms, v atom.lhs ≤ v term.1 + term.2

def RowsHold (rows : List (IntAtom ν)) (v : ν → ℤ) : Prop :=
  ∀ atom ∈ rows, atom.Holds v

def atomOffsets (rows : List (Atom ν)) : List ℚ :=
  rows.flatMap fun atom => atom.terms.map Prod.snd

def integerAtom (D : ℕ) (atom : Atom ν) : IntAtom ν :=
  ⟨atom.lhs, atom.terms.map fun term => (term.1, ⌊(D : ℚ) * term.2⌋)⟩

def encodeAt (D : ℕ) (rows : List (Atom ν)) : List (IntAtom ν) :=
  rows.map (integerAtom D)

def encode (rows : List (Atom ν)) : List (IntAtom ν) :=
  encodeAt (denominator (atomOffsets rows)) rows

private theorem exact_offset {D : ℕ} {rows : List (Atom ν)} {atom : Atom ν} {term : Signal ν}
    (clears : ∀ c ∈ atomOffsets rows, Clears D c)
    (rowMem : atom ∈ rows) (termMem : term ∈ atom.terms) :
    (⌊(D : ℚ) * term.2⌋ : ℚ) = (D : ℚ) * term.2 := by
  have offsetMem : term.2 ∈ atomOffsets rows :=
    List.mem_flatMap.mpr ⟨atom, rowMem, List.mem_map.mpr ⟨term, termMem, rfl⟩⟩
  obtain ⟨k, hk⟩ := clears _ offsetMem
  simp only [hk, Int.floor_intCast]

theorem feasible_iff_integer_at (rows : List (Atom ν)) (D : ℕ) (positive : 0 < D)
    (clears : ∀ c ∈ atomOffsets rows, Clears D c) :
    (∃ v : ν → ℚ, AtomEncoding.RowsHold rows v) ↔
      ∃ v : ν → ℤ, RowsHold (encodeAt D rows) v := by
  have Dpos : 0 < (D : ℚ) := by exact_mod_cast positive
  constructor
  · rintro ⟨v, holds⟩
    refine ⟨fun i => ⌊(D : ℚ) * v i⌋, ?_⟩
    intro row rowMem
    obtain ⟨atom, atomMem, rfl⟩ := List.mem_map.mp rowMem
    obtain ⟨term, termMem, inequality⟩ := holds atom atomMem
    refine ⟨(term.1, ⌊(D : ℚ) * term.2⌋), List.mem_map.mpr ⟨term, termMem, rfl⟩, ?_⟩
    have scaled := mul_le_mul_of_nonneg_left inequality Dpos.le
    change ⌊(D : ℚ) * v atom.lhs⌋ ≤ ⌊(D : ℚ) * v term.1⌋ + ⌊(D : ℚ) * term.2⌋
    have rounded := Int.floor_mono scaled
    change _ ≤ ⌊(D : ℚ) * (v term.1 + term.2)⌋ at rounded
    rw [mul_add, ← exact_offset clears atomMem termMem, Int.floor_add_intCast] at rounded
    exact rounded
  · rintro ⟨v, holds⟩
    refine ⟨fun i => (v i : ℚ) / (D : ℚ), ?_⟩
    intro atom atomMem
    have encodedMem : integerAtom D atom ∈ encodeAt D rows :=
      List.mem_map.mpr ⟨atom, atomMem, rfl⟩
    obtain ⟨_, mem, inequality⟩ := holds _ encodedMem
    obtain ⟨term, termMem, rfl⟩ := List.mem_map.mp mem
    refine ⟨term, termMem, ?_⟩
    change (v atom.lhs : ℚ) / (D : ℚ) ≤ (v term.1 : ℚ) / (D : ℚ) + term.2
    apply (mul_le_mul_iff_of_pos_left Dpos).1
    have cancel (z : ℤ) : (D : ℚ) * ((z : ℚ) / (D : ℚ)) = (z : ℚ) := by
      rw [mul_comm, div_mul_cancel₀ _ Dpos.ne']
    rw [mul_add, cancel, cancel, ← exact_offset clears atomMem termMem]
    exact_mod_cast inequality

theorem feasible_iff_integer (rows : List (Atom ν)) :
    (∃ v : ν → ℚ, AtomEncoding.RowsHold rows v) ↔ ∃ v : ν → ℤ, RowsHold (encode rows) v :=
  feasible_iff_integer_at rows _ (denominator_pos _) (fun _ => denominator_clears)

/-- The bounded compiler yields explicit integer rows with the same feasibility answer. -/
theorem exact_iff_integer [Fintype ν] [DecidableEq ν] (system : AverageFeasibility.System ν)
    {width : ℚ} (widthNonneg : 0 ≤ width) (inputWidths : system.InputsBounded width)
    (bounded : ∃ B : ℚ, ∀ x, system.HardRows x → ∀ i, |x i| ≤ B) :
    (∃ x, system.Exact x) ↔
      ∃ v, RowsHold
        (encode (allAtoms system width (rounds width (MaxAverageReduction.gap system)))) v :=
  (AtomEncoding.exact_iff_atoms system widthNonneg inputWidths bounded).trans
    (feasible_iff_integer _)

end StochasticGames.IntegerAtoms
