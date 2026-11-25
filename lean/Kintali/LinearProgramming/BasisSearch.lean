module

public import Kintali.LinearProgramming.System
public import Kintali.LinearProgramming.Bird
public import StochasticGames.DeterminantGap
public import StochasticGames.TightRows
import all StochasticGames.BoundedLinearProgram
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact solution by basis enumeration

A bounded nonempty system has a point determined by independent tight rows.
The executable solver visits all row selections and tests each nonsingular
Cramer solution. The list has `m ^ n` entries for `m` rows and `n` unknowns.
This is a total exact reference implementation for the LP call in §3 of
Kintali's paper. Polynomial-time decision requires another algorithm.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open scoped BigOperators
open StochasticGames

def rowSelections (m : ℕ) : (n : ℕ) → List (Fin n → Fin m)
  | 0 => [fun i => i.elim0]
  | n + 1 => (List.finRange m).flatMap fun i =>
    (rowSelections m n).map (Fin.cons i)

theorem mem_rowSelections {m n : ℕ} (rows : Fin n → Fin m) : rows ∈ rowSelections m n := by
  induction n with
  | zero =>
    rw [rowSelections, List.mem_singleton]
    funext i
    exact i.elim0
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨rows 0, List.mem_finRange _, List.mem_map.mpr ⟨Fin.tail rows, ih _, ?_⟩⟩
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem length_rowSelections (m n : ℕ) : (rowSelections m n).length = m ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [rowSelections, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

namespace System

variable {m n : ℕ} (P : System (Fin m) (Fin n))

def basisMatrix (rows : Fin n → Fin m) : Matrix (Fin n) (Fin n) ℤ :=
  P.coeff.submatrix rows id

def basisPoint (rows : Fin n → Fin m) (den : ℤ) : Fin n → ℚ :=
  fun j => Rat.divInt (determinant ((P.basisMatrix rows).updateCol j (P.rhs ∘ rows))) den

def checkedBasis (rows : Fin n → Fin m) : Option (Fin n → ℚ) :=
  let den := determinant (P.basisMatrix rows)
  if den = 0 then none else
    let x := P.basisPoint rows den
    if P.Feasible x then some x else none

/-- Enumerate the row selections until one supplies a feasible point. -/
def solve : Option (Fin n → ℚ) :=
  (rowSelections m n).findSome? P.checkedBasis

theorem checkedBasis_spec {rows : Fin n → Fin m} {x : Fin n → ℚ}
    (hit : P.checkedBasis rows = some x) :
    determinant (P.basisMatrix rows) ≠ 0 ∧ P.Feasible x ∧
      x = P.basisPoint rows (determinant (P.basisMatrix rows)) := by
  unfold checkedBasis at hit
  dsimp only at hit
  split at hit
  · contradiction
  · rename_i den
    split at hit
    · rename_i feasible
      cases hit
      exact ⟨den, feasible, rfl⟩
    · contradiction

theorem solve_sound {x : Fin n → ℚ} (hit : P.solve = some x) : P.Feasible x := by
  obtain ⟨rows, _, h⟩ := List.exists_of_findSome?_eq_some hit
  exact (P.checkedBasis_spec h).2.1

private theorem exists_checkedBasis (bounded : P.Bounded) {x : Fin n → ℚ}
    (feasible : P.Feasible x) : ∃ rows y, P.checkedBasis rows = some y := by
  obtain ⟨y, hy, _, kernel⟩ := BoundedLinearProgram.exists_tight_point
    P.matrix (fun i => (P.rhs i : ℚ)) bounded 0 feasible
  obtain ⟨rows, active, regular⟩ := TightRows.exists_active_nonsingular_submatrix _ _ kernel
  let M := P.basisMatrix rows
  let b := P.rhs ∘ rows
  have den : M.det ≠ 0 := by
    intro zero
    apply regular
    change ((Int.castRingHom ℚ).mapMatrix M).det = 0
    rw [← (Int.castRingHom ℚ).map_det, zero, map_zero]
  have tight : ((Int.castRingHom ℚ).mapMatrix M).mulVec (fun j => (1 : ℚ) * y j) =
      (fun i => (b i : ℚ)) := by
    simp only [one_mul]
    funext i
    exact (BoundedLinearProgram.mem_tightRows _ _ _ _).mp (active i)
  have point : P.basisPoint rows (determinant M) = y := by
    funext j
    have idn := DeterminantGap.cramer_scaled_coordinate M b (1 : ℚ) y tight j
    simp only [one_mul] at idn
    change Rat.divInt (determinant (M.updateCol j b)) (determinant M) = _
    rw [determinant_eq, determinant_eq, Rat.divInt_eq_div, div_eq_iff (Int.cast_ne_zero.mpr den)]
    rw [mul_comm, idn, Matrix.cramer_apply]
  refine ⟨rows, y, ?_⟩
  change (if determinant M = 0 then none else
    if P.Feasible (P.basisPoint rows (determinant M)) then some _ else none) = some y
  have feasibleY : P.Feasible y := hy
  rw [ite_eq_right (by simpa using den), point, ite_eq_left feasibleY]

/-- On bounded systems the negative answer certifies infeasibility. -/
theorem solve_eq_none_iff (bounded : P.Bounded) : P.solve = none ↔ ¬ ∃ x, P.Feasible x := by
  constructor
  · intro miss feasible
    obtain ⟨x, hx⟩ := feasible
    obtain ⟨rows, y, hit⟩ := P.exists_checkedBasis bounded hx
    have failure := List.findSome?_eq_none_iff.mp miss rows (mem_rowSelections _)
    rw [hit] at failure
    contradiction
  · intro empty
    cases h : P.solve with
    | none => rfl
    | some x => exact (empty ⟨x, P.solve_sound h⟩).elim

theorem solve_isSome_iff (bounded : P.Bounded) : P.solve.isSome ↔ ∃ x, P.Feasible x := by
  rw [Option.isSome_iff_ne_none, ne_eq, P.solve_eq_none_iff bounded]
  exact Classical.not_not

end System

end Kintali.LinearProgramming
