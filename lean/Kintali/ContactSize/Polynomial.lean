module

public import Kintali.ContactSize.Output
public import Kintali.ContactSize.Prefix
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The bounds on the stored states, projected view, dense repair and
public output are evaluations of fixed natural-coefficient polynomials.
The same holds for the charged binary work of the repair subroutine. -/

@[expose] public section
namespace Kintali.ContactSize

open Polynomial ExactRecovery InputOutput LinearProgramming MarketTrial

private def Evaluation (f : ℕ → ℕ) := ∃ P : Polynomial ℕ, ∀ n, P.eval n = f n

private theorem variable_eval : Evaluation (fun n => n) := ⟨X,by simp⟩

private theorem constant_eval (c : ℕ) : Evaluation (fun _ => c) := ⟨C c,by simp⟩

private theorem add_eval {f g : ℕ → ℕ} (hf : Evaluation f) (hg : Evaluation g) :
    Evaluation (fun n => f n + g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,by simp [hp,hq]⟩

private theorem mul_eval {f g : ℕ → ℕ} (hf : Evaluation f) (hg : Evaluation g) :
    Evaluation (fun n => f n * g n) := by
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,by simp [hp,hq]⟩

private theorem pow_eval {f : ℕ → ℕ} (e : ℕ) (hf : Evaluation f) :
    Evaluation (fun n => f n ^ e) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^e,by simp [hp]⟩

local macro "polynomial_eval" : tactic =>
  `(tactic| with_reducible (repeat' first | assumption | exact variable_eval | apply constant_eval | apply add_eval | apply mul_eval | apply pow_eval))

private theorem dimensions_poly : Evaluation Binary.repairBound := by
  unfold Binary.repairBound exactRows exactVars
  polynomial_eval

private theorem grid_poly : Evaluation Binary.gridBitBound := by
  have h := dimensions_poly
  unfold Binary.gridBitBound
  polynomial_eval

private theorem tolerance_poly : Evaluation toleranceWidth := by
  have h := dimensions_poly
  unfold toleranceWidth
  polynomial_eval

private theorem scale_poly : Evaluation scaleWidth := by
  have h := tolerance_poly
  unfold scaleWidth
  polynomial_eval

private theorem parameters_poly : Evaluation parameterWidth := by
  have h := scale_poly
  have g := grid_poly
  unfold parameterWidth
  polynomial_eval

private theorem records_poly : Evaluation recordLimit := by
  unfold recordLimit sampleLimit
  polynomial_eval

/-- One fixed polynomial bounds the width at every sweep prefix. -/
theorem allocation_polynomial : ∃ P : Polynomial ℕ, ∀ L, P.eval L = allocationWidth L := by
  change Evaluation allocationWidth
  have r := records_poly
  have w := parameters_poly
  unfold allocationWidth stateWidth denominatorWidth factorWidth
  polynomial_eval

theorem view_polynomial : ∃ P : Polynomial ℕ, ∀ L, P.eval L = viewWidth L := by
  change Evaluation viewWidth
  have h : Evaluation allocationWidth := allocation_polynomial
  have r := records_poly
  have s := scale_poly
  unfold viewWidth
  polynomial_eval

theorem repair_length_polynomial : ∃ P : Polynomial ℕ, ∀ L, P.eval L = repairLength L := by
  change Evaluation repairLength
  have u := dimensions_poly
  have v : Evaluation viewWidth := view_polynomial
  have t := tolerance_poly
  unfold repairLength
  polynomial_eval

theorem repair_work_polynomial : ∃ P : Polynomial ℕ, ∀ L, P.eval L = repairWork L := by
  change Evaluation repairWork
  have h : Evaluation repairLength := repair_length_polynomial
  unfold repairWork RationalInput.binaryLimit RationalInput.slotLimit RationalInput.widthLimit
    RecoveryRun.transitionLimit RecoveryRun.operandLimit PivotRun.width RecoveryRun.scale
    PointEncoding.wordLimit
  polynomial_eval

theorem strategy_polynomial : ∃ P : Polynomial ℕ, ∀ L, P.eval L = strategyWidth L := by
  change Evaluation strategyWidth
  have h : Evaluation repairLength := repair_length_polynomial
  unfold strategyWidth RationalInput.widthLimit RecoveryRun.operandLimit PivotRun.width
    RecoveryRun.scale PointEncoding.wordLimit
  polynomial_eval

theorem output_polynomial : ∃ P : Polynomial ℕ, ∀ L, P.eval L = outputLength L := by
  change Evaluation outputLength
  have h : Evaluation strategyWidth := strategy_polynomial
  unfold outputLength
  polynomial_eval

theorem public_output_polynomial : ∃ P : Polynomial ℕ, ∀ (a : Input), a.Valid →
    (solveBits (Binary.input a)).length ≤ P.eval (Binary.lengthInput a) := by
  obtain ⟨P,h⟩ := output_polynomial
  exact ⟨P, fun a valid => (solveBits_length a valid).trans_eq (h _).symm⟩

end Kintali.ContactSize
