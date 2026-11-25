module

public import Kintali.InputOutput.ValidityWork
public import Kintali.InputOutput.CodecWorkSolver
public import Kintali.InputOutput.CodecWorkReencode
public import Kintali.ContactSize.Polynomial

/-! # Public binary work from a valid-market solver

The boolean validity test guards the solver's proof argument and is charged on
every successfully decoded table. The exactness specification concerns valid
markets. Bounds use the addressed binary-word cost of `CompilerRun`.
-/

@[expose] public section

namespace Kintali.InputOutput.PublicWork

open Binary StochasticGames.CompilerRun

abbrev ValidCore := (a : Input) → a.Valid → Run Output

/-- Attach the identity of a computed value without evaluating the run again. -/
def observed {α : Type} (p : Run α) : Run {x : α // p.value = x} :=
  ⟨⟨p.value,rfl⟩,p.work⟩

def guarded (core : ValidCore) (a : Input) : Run Output := do
  let ⟨b,h⟩ ← observed (ValidityWork.run a >>= step 0)
  if ok : b = true then
    core a ((ValidityWork.run_true a).mp (h.trans ok))
  else step 0 ([],[])

theorem guarded_valid (core : ValidCore) (a : Input) (v : a.Valid) :
    (guarded core a).value = (core a v).value := by
  simp [guarded,observed,(ValidityWork.run_true a).mpr v]

theorem guarded_invalid (core : ValidCore) (a : Input) (v : ¬a.Valid) :
    (guarded core a).value = ([],[]) := by
  simp [guarded,observed,ValidityWork.run_true,v]

theorem guarded_work (core : ValidCore) (a : Input) {K W : ℕ}
    (work : ∀ v, (core a v).Bound K W) :
    (guarded core a).Bound (ValidityWork.slots (lengthInput a)+K+2)
      (ValidityWork.width (lengthInput a)+W) := by
  obtain ⟨slots,width⟩ := ValidityWork.run_work a
  by_cases v : a.Valid
  · obtain ⟨cs,cw⟩ := work v
    simp [guarded,observed,Run.Bound,(ValidityWork.run_true a).mpr v]
    omega
  · simp [guarded,observed,Run.Bound,ValidityWork.run_true,v]
    omega

def run (core : ValidCore) := CodecWork.solveRun (guarded core)

/-- Correctness is preserved for every encoding of a valid market accepted by
the public reader. -/
theorem decoded_output (core : ValidCore) (correct : ∀ a v, (core a v).value = solve a)
    (bits : CodecWork.Stream) (a : Input) (ok : inputCodec.decode bits = some a) (v : a.Valid) :
    (run core bits).value = solveBits bits ∧
    outputCodec.decode (run core bits).value = some (solve a) ∧ a.IsBayesNash (solve a) := by
  have val : (run core bits).value = output (solve a) := by
    simp [run,CodecWork.solveRun,CodecWork.input_value,ok,guarded_valid core a v,correct,
      CodecWork.outputWriter.correct]
  exact ⟨by simp [val,solveBits,ok], val ▸ read_output _, solve_correct a v⟩

theorem valid_output (core : ValidCore) (correct : ∀ a v, (core a v).value = solve a)
    (a : Input) (v : a.Valid) :
    (run core (input a)).value = solveBits (input a) ∧
    outputCodec.decode (run core (input a)).value = some (solve a) ∧
    a.IsBayesNash (solve a) :=
  decoded_output core correct _ a (read_input a) v

theorem invalid_output (core : ValidCore) (a : Input) (v : ¬a.Valid) :
    (run core (input a)).value = output ([],[]) := by
  simp [run,CodecWork.solveRun,CodecWork.input_value,guarded_invalid core a v,
    CodecWork.outputWriter.correct]

private theorem eval_le (P : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    P.eval a ≤ P.eval b := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa using Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

private theorem stream_work (core : ValidCore) (bits : CodecWork.Stream) {k w b : ℕ}
    (cost : ∀ a, inputCodec.decode bits = some a → (guarded core a).Bound k w)
    (out : ∀ a, inputCodec.decode bits = some a → (output (guarded core a).value).length ≤ b) :
    (run core bits).Bound (CodecWork.solveSlots bits.length k b) (CodecWork.solveWidth bits.length w b) := by
  obtain ⟨rs,rw⟩ := CodecWork.input_work bits
  cases h : inputCodec.decode bits with
  | none =>
    simp only [run,CodecWork.solveRun,Run.Bound,Run.bind_slots,Run.bind_width,step_value,
      step_slots,step_width,CodecWork.input_value,h,CodecWork.solveSlots,CodecWork.solveWidth]
    omega
  | some a =>
    obtain ⟨cs,cw⟩ := cost a h
    obtain ⟨ws,ww⟩ := CodecWork.output_work (guarded core a).value
    have len := out a h
    simp only [run,CodecWork.solveRun,Run.Bound,Run.bind_slots,Run.bind_width,step_value,
      step_slots,step_width,CodecWork.input_value,h,CodecWork.solveSlots,CodecWork.solveWidth]
    omega

/-- Every supplied bitstream satisfies one polynomial work bound, including
noncanonical encodings, invalid markets and streams on which parsing fails. -/
theorem stream_polynomial (core : ValidCore) (correct : ∀ a v, (core a v).value = solve a)
    (K W : Polynomial ℕ)
    (cost : ∀ a v, (core a v).Bound (K.eval (lengthInput a)) (W.eval (lengthInput a))) :
    ∃ P : Polynomial ℕ, ∀ bits, LinearProgramming.RecoveryRun.binaryWork
      bits.length (run core bits).work ≤ P.eval bits.length := by
  obtain ⟨B,out⟩ := ContactSize.public_output_polynomial
  let D : Polynomial ℕ := 22*Polynomial.X^3+110*Polynomial.X^2+125*Polynomial.X+16
  let G : Polynomial ℕ := 10*Polynomial.X^3+47*Polynomial.X^2+97*Polynomial.X+15
  let H : Polynomial ℕ := 2*Polynomial.X^2+9*Polynomial.X+26
  let T : Polynomial ℕ := 13*Polynomial.X
  let KG := (G+K+2).comp T
  let WH := (H+W).comp T
  let BO := (B+1).comp T
  let U := D+1+KG+72*(BO+1)
  let V := Polynomial.X+8+WH+BO+3
  use U*(64*(Polynomial.X+U+3*V+16)^3)
  intro bits
  have promote (P : Polynomial ℕ) (a : Input) (ok : inputCodec.decode bits = some a) :
      P.eval (lengthInput a) ≤ (P.comp T).eval bits.length := by
    rw [Polynomial.eval_comp]
    exact eval_le P (by simpa [T] using CodecWork.reencode_length ok)
  have works (a : Input) (ok : inputCodec.decode bits = some a) :
      (guarded core a).Bound (KG.eval bits.length) (WH.eval bits.length) := by
    apply (guarded_work core a (cost a)).weaken
    · simpa [KG,G,ValidityWork.slots_eq] using promote (G+K+2) a ok
    · simpa [WH,H,ValidityWork.width_eq] using promote (H+W) a ok
  have outs (a : Input) (ok : inputCodec.decode bits = some a) :
      (output (guarded core a).value).length ≤ BO.eval bits.length := by
    apply le_trans _ (promote (B+1) a ok)
    by_cases v : a.Valid
    · rw [guarded_valid core a v,correct]
      simpa using (out a v).trans (Nat.le_succ _)
    · rw [guarded_invalid core a v]
      change 1 ≤ _
      simp
  apply (CodecWork.addressed_bound bits.length (stream_work core bits works outs)).trans_eq
  simp [D,U,V,CodecWork.solveSlots,CodecWork.solveWidth,CodecWork.inputLimit_eq,CodecWork.binaryLimit]

/-- In particular the upstream typed domain has a single polynomial bound. -/
theorem canonical_polynomial (core : ValidCore) (correct : ∀ a v, (core a v).value = solve a)
    (K W : Polynomial ℕ)
    (cost : ∀ a v, (core a v).Bound (K.eval (lengthInput a)) (W.eval (lengthInput a))) :
    ∃ P : Polynomial ℕ, ∀ a : Input, LinearProgramming.RecoveryRun.binaryWork
      (lengthInput a) (run core (input a)).work ≤ P.eval (lengthInput a) := by
  obtain ⟨P,h⟩ := stream_polynomial core correct K W cost
  exact ⟨P,fun a => h (input a)⟩

end Kintali.InputOutput.PublicWork
