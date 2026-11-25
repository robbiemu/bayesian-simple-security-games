module

public import Kintali.ExactRecovery.Grid
public import Kintali.ExactRecovery.Matrix
public import Kintali.ExactRecovery.Rows
public import Kintali.LinearProgramming.RationalInput
public import Kintali.LinearProgramming.SlackWindow
public import Kintali.LinearProgramming.System
public import Kintali.Preprocessing
import Kintali.LinearProgramming.Rounding
import all StochasticGames.BoundedLinearProgram
import all StochasticGames.LinearFeasibilityGap
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Recovering an exact strategy from a successful contact

Use the compiled integer pattern rows of §1. Append a row that sets
the residual to zero, and repair the supplied relaxed point directly.
The only row the supplied point can violate is the added residual row.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali

namespace ExactRecovery

open LinearProgramming StochasticGames.LinearFeasibilityGap

def rowShape (k m : ℕ) :
    Row (Fin k) (Fin m) ⊕ Unit ≃
    (Fin 6 × Fin m) ⊕ ((Fin 4 × (Fin k × Fin m)) ⊕ ((Bool × Fin k) ⊕ Fin 6)) where
  toFun
    | .inl (.coverageLower j) => .inl (0, j)
    | .inl (.coverageUpper j) => .inl (1, j)
    | .inl (.fixLower j) => .inl (2, j)
    | .inl (.fixUpper j) => .inl (3, j)
    | .inl (.pressureLe j) => .inl (4, j)
    | .inl (.pressureGe j) => .inl (5, j)
    | .inl (.flowLower i j) => .inr (.inl (0, i, j))
    | .inl (.unmarked i j) => .inr (.inl (1, i, j))
    | .inl (.referenceCost i j) => .inr (.inl (2, i, j))
    | .inl (.markedCost i j) => .inr (.inl (3, i, j))
    | .inl (.rowLe i) => .inr (.inr (.inl (false, i)))
    | .inl (.rowGe i) => .inr (.inr (.inl (true, i)))
    | .inl .budgetLe => .inr (.inr (.inr 0))
    | .inl .budgetGe => .inr (.inr (.inr 1))
    | .inl .thresholdLower => .inr (.inr (.inr 2))
    | .inl .residualLower => .inr (.inr (.inr 3))
    | .inl .residualUpper => .inr (.inr (.inr 4))
    | .inr () => .inr (.inr (.inr 5))
  invFun
    | .inl (c, j) => match c.val with
      | 0 => .inl (.coverageLower j)
      | 1 => .inl (.coverageUpper j)
      | 2 => .inl (.fixLower j)
      | 3 => .inl (.fixUpper j)
      | 4 => .inl (.pressureLe j)
      | _ => .inl (.pressureGe j)
    | .inr (.inl (c, i, j)) => match c.val with
      | 0 => .inl (.flowLower i j)
      | 1 => .inl (.unmarked i j)
      | 2 => .inl (.referenceCost i j)
      | _ => .inl (.markedCost i j)
    | .inr (.inr (.inl (false, i))) => .inl (.rowLe i)
    | .inr (.inr (.inl (true, i))) => .inl (.rowGe i)
    | .inr (.inr (.inr c)) => match c.val with
      | 0 => .inl .budgetLe
      | 1 => .inl .budgetGe
      | 2 => .inl .thresholdLower
      | 3 => .inl .residualLower
      | 4 => .inl .residualUpper
      | _ => .inr ()
  left_inv := by
    rintro (r | ⟨⟩)
    · cases r <;> rfl
    · rfl
  right_inv := by
    rintro (⟨c, j⟩ | ⟨c, i, j⟩ | ⟨b, i⟩ | c)
    · fin_cases c <;> rfl
    · fin_cases c <;> rfl
    · cases b <;> rfl
    · fin_cases c <;> rfl

def exactRows (k m : ℕ) : ℕ := 6 * m + (4 * (k * m) + (2 * k + 6))
def exactVars (k m : ℕ) : ℕ := k * m + (m + 2)

def rowIndex (k m : ℕ) : Row (Fin k) (Fin m) ⊕ Unit ≃ Fin (exactRows k m) :=
  (rowShape k m).trans <|
    (Equiv.sumCongr finProdFinEquiv <|
      (Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv) <|
        (Equiv.sumCongr ((Equiv.prodCongr finTwoEquiv.symm (Equiv.refl _)).trans finProdFinEquiv)
          (Equiv.refl _)).trans finSumFinEquiv).trans finSumFinEquiv).trans finSumFinEquiv

def varIndex (k m : ℕ) : Variable (Fin k) (Fin m) ≃ Fin (exactVars k m) :=
  (Equiv.sumCongr finProdFinEquiv
    ((Equiv.sumCongr (Equiv.refl _) finTwoEquiv.symm).trans finSumFinEquiv)).trans finSumFinEquiv

variable {k m : ℕ} (g : Game (Fin k) (Fin m))

/-- A bound for both the compiled pattern rows and the extra unit row. -/
def coefficientHeight : ℕ := (2 * atomBound g).natAbs

theorem coefficientHeight_pos : 0 < coefficientHeight g := by
  unfold coefficientHeight
  exact Int.natAbs_pos.mpr (ne_of_gt (Int.mul_pos (by decide) (atomBound_pos g)))

theorem coefficientHeight_cast : (coefficientHeight g : ℤ) = 2 * atomBound g := by
  unfold coefficientHeight
  rw [Int.natAbs_of_nonneg (Int.mul_nonneg (by decide) (atomBound_pos g).le)]

def roundingPrecision : ℚ :=
  SlackWindow.precision (exactRows k m) (exactVars k m) (coefficientHeight g)

def contactTolerance : ℚ := min (eta g) (roundingPrecision g)

theorem contactTolerance_pos : 0 < contactTolerance g :=
  lt_min (eta_bounds g).1 (SlackWindow.precision_pos _ _ (coefficientHeight_pos g))

theorem contactTolerance_le : contactTolerance g ≤ roundingPrecision g := min_le_right _ _

theorem contactTolerance_le_one : contactTolerance g ≤ 1 :=
  (min_le_left _ _).trans (eta_bounds g).2.2

theorem contactTolerance_lt_one : contactTolerance g < 1 := by
  have hH : (1 : ℚ) ≤ height g := by exact_mod_cast height_pos g
  refine (min_le_left _ _).trans_lt ?_
  unfold eta
  exact (div_lt_iff₀ (by linarith)).mpr (by linarith)

/-- The compiled relaxed rows and one exact row `residual ≤ 0`.
The compiled relaxed system already contains `0 ≤ residual`. -/
def exactSystem (p : Pattern (Fin k) (Fin m)) :
    System (Fin (exactRows k m)) (Fin (exactVars k m)) where
  coeff i j :=
    match (rowIndex k m).symm i with
    | .inl r => matrix g p r ((varIndex k m).symm j)
    | .inr () => if j = varIndex k m (.inr (.inr true)) then 1 else 0
  rhs i :=
    match (rowIndex k m).symm i with
    | .inl r => rhs g p r
    | .inr () => 0

theorem exactSystem_coeff_bound (p : Pattern (Fin k) (Fin m)) (i j : _) :
    |(exactSystem g p).coeff i j| ≤ (coefficientHeight g : ℤ) := by
  rw [coefficientHeight_cast]
  cases h : (rowIndex k m).symm i with
  | inl r => simpa [exactSystem, h] using matrix_bound g p r ((varIndex k m).symm j)
  | inr u =>
    have hb : (1 : ℤ) ≤ 2 * atomBound g := by
      have hp := atomBound_pos g
      omega
    cases u
    by_cases hj : j = varIndex k m (.inr (.inr true)) <;> simp [exactSystem, h, hj, hb]
    omega

private theorem old_row (p : Pattern (Fin k) (Fin m))
    (x : Fin (exactVars k m) → ℚ) (r : Row (Fin k) (Fin m)) :
    (exactSystem g p).matrix.mulVec x (rowIndex k m (.inl r)) =
      (rationalMatrix (matrix g p)).mulVec (fun j => x (varIndex k m j)) r := by
  unfold rationalMatrix
  change (∑ j, ((exactSystem g p).coeff (rowIndex k m (.inl r)) j : ℚ) * x j) =
    ∑ j, (matrix g p r j : ℚ) * x (varIndex k m j)
  simp only [exactSystem, Equiv.symm_apply_apply]
  simpa only [Equiv.apply_symm_apply] using
    (varIndex k m).symm.sum_comp (fun j => (matrix g p r j : ℚ) * x (varIndex k m j))

private theorem zero_row (p : Pattern (Fin k) (Fin m)) (x : Fin (exactVars k m) → ℚ) :
    (exactSystem g p).matrix.mulVec x (rowIndex k m (.inr ())) =
      x (varIndex k m (.inr (.inr true))) := by
  change (∑ j, ((exactSystem g p).coeff (rowIndex k m (.inr ())) j : ℚ) * x j) = _
  simp [exactSystem, apply_ite Int.cast, ite_mul]

/-- Materialize the integer rows before pivot scans and determinant calls. -/
def recoveryInput (p : Pattern (Fin k) (Fin m)) :
    PivotRun.Input (exactRows k m) (exactVars k m) :=
  ⟨Vector.ofFn fun i => Vector.ofFn ((exactSystem g p).coeff i),
    Vector.ofFn (exactSystem g p).rhs⟩

@[simp] theorem recoveryInput_system (p : Pattern (Fin k) (Fin m)) :
    (recoveryInput g p).system = exactSystem g p := by
  change System.mk _ _ = _
  simp [recoveryInput, exactSystem, Matrix.of]
  rfl

def recoveryPoint (x : Fin m → ℚ) (q : Fin k → Fin m → ℚ) (t e : ℚ) :
    Vector ℚ (exactVars k m) :=
  Vector.ofFn fun j => vector x q t e ((varIndex k m).symm j)

theorem recoveryValue_eq (p : Pattern (Fin k) (Fin m)) (x : Fin m → ℚ)
    (q : Fin k → Fin m → ℚ) (t e : ℚ) :
    (RationalInput.run (recoveryInput g p) (recoveryPoint x q t e)
      (coefficientHeight g)).value.value =
      (exactSystem g p).recover (coefficientHeight g)
        (fun j => vector x q t e ((varIndex k m).symm j)) := by
  rw [RationalInput.run_value _ _ (coefficientHeight_pos g), recoveryInput_system]
  congr 1
  funext j
  change (recoveryPoint x q t e)[j.val] = _
  simp [recoveryPoint]

def repair (p : Pattern (Fin k) (Fin m)) (x : Fin m → ℚ) (q : Fin k → Fin m → ℚ)
    (t e : ℚ) : Strategy k m :=
  let y := (RationalInput.run (recoveryInput g p) (recoveryPoint x q t e)
    (coefficientHeight g)).value.value
  let unpacked := fun j => y (varIndex k m j)
  ⟨coverageOf unpacked, g.conditional (flowOf unpacked) p.reference⟩

/-- An explicitly relaxed point is sufficient for exact output. -/
theorem repair_correct (p : Pattern (Fin k) (Fin m))
    {x : Fin m → ℚ} {q : Fin k → Fin m → ℚ} {t e : ℚ}
    (small : e ≤ roundingPrecision g) (relaxed : Relaxed g p x q t e) :
    g.IsBayesNash (repair g p x q t e).coverage (repair g p x q t e).attacks := by
  let input := fun j => vector x q t e ((varIndex k m).symm j)
  have hInput : ∀ j, input (varIndex k m j) = vector x q t e j := fun j => by simp [input]
  have hApprox (i : Fin (exactRows k m)) :
      -roundingPrecision g ≤ (exactSystem g p).slack input i := by
    obtain ⟨r, rfl⟩ := (rowIndex k m).surjective i
    rcases r with r | ⟨⟩
    · have hFeasible := (feasible_vector_iff g p x q t e).mpr relaxed
      unfold StochasticGames.BoundedLinearProgram.Feasible at hFeasible
      have hRow := hFeasible r
      unfold System.slack
      rw [old_row, show (fun v => input (varIndex k m v)) = vector x q t e from funext hInput]
      have hRhs : (exactSystem g p).rhs (rowIndex k m (.inl r)) = rhs g p r := by
        simp [exactSystem]
      rw [hRhs]
      have hPrec := SlackWindow.precision_pos (exactRows k m) (exactVars k m) (coefficientHeight_pos g)
      have hz : (0 : ℚ) ≤ (rhs g p r : ℚ) - (rationalMatrix (matrix g p)).mulVec (vector x q t e) r := by
        simpa [rationalRhs] using sub_nonneg.mpr hRow
      exact (neg_nonpos.mpr hPrec.le).trans hz
    · unfold System.slack
      rw [zero_row, hInput]
      simp [exactSystem, vector, neg_le_neg_iff, small]
  have hz := (exactSystem g p).recover_feasible (coefficientHeight g) input
    (coefficientHeight_pos g) (exactSystem_coeff_bound g p) hApprox
  let y := (exactSystem g p).recover (coefficientHeight g) input
  let v := fun j => y (varIndex k m j)
  have hRows : StochasticGames.BoundedLinearProgram.Feasible (rationalMatrix (matrix g p))
      (rationalRhs (rhs g p) 1) v := by
    unfold StochasticGames.BoundedLinearProgram.Feasible
    intro r
    have hr := hz (rowIndex k m (.inl r))
    rw [old_row] at hr
    simpa [v, y, exactSystem, rationalRhs] using hr
  have hRelax := (feasible_iff g p v).mp hRows
  have hResidual : residualOf v = 0 := by
    have hr := hz (rowIndex k m (.inr ()))
    rw [zero_row] at hr
    have hu : residualOf v ≤ 0 := by
      simpa [residualOf, v, y, exactSystem] using hr
    exact le_antisymm hu hRelax.residual_bounds.1
  rw [hResidual] at hRelax
  unfold repair
  rw [recoveryValue_eq]
  exact g.certificate_isBayesNash (exactCertificate hRelax)

end ExactRecovery
end Kintali
