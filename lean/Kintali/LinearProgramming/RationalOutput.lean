module

public import Kintali.LinearProgramming.OutputSize

/-! # Sizes of individual reduced rational output coordinates -/

@[expose] public section

namespace Kintali.LinearProgramming.RationalInput

open StochasticGames.CompilerRun PivotRun

variable {m n : ℕ}

theorem run_den_ne_zero (P : Input m n) (x : Vector ℚ n) (h : ℕ) : (run P x h).value.den ≠ 0 := by
  let X := (PointEncoding.encode x).value
  let res := (PointRun.residuals P X).value
  let p := (PrecisionRun.setup m n h).value
  let mask := (RecoveryRun.classify res X.den p).value
  let s := (PivotRun.choose P mask).value
  have reg : (s.view.matrix P.system).det ≠ 0 := by
    rw [show s.view = _ from PivotRun.choose_value P mask]
    exact (Minor.choose_spec ..).1
  have d : (run P x h).value.den = (s.view.matrix P.system).det * (X.den : ℤ) := by
    simp only [run,Run.bind_value,RecoveryRun.run,CramerRun.repair,CramerRun.output,
      intMul,step_value,PivotRun.determinantOf_value]
    rfl
  rw [d]
  exact mul_ne_zero reg (Int.natCast_ne_zero.mpr X.positive.ne')

/-- Each reduced numerator fits the charged operand bound for the actual
run. Its reduced denominator fits twice the same bound. -/
theorem run_coordinate_size (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) (j : Fin n) :
    let z := (run P x h).value.value j
    z.num.natAbs.size ≤ widthLimit (inputLength P x h) ∧
      z.den.size ≤ 2*widthLimit (inputLength P x h) := by
  let z := run P x h
  have fit : z.work.width ≤ widthLimit (inputLength P x h) := (run_work P x hp coeff).2
  have fields := OutputSize.rational_fields P x h
  have num : z.value.num[j.val].natAbs.size ≤ z.work.width := fields.2 j
  have den : z.value.den.natAbs.size ≤ 2*z.work.width := fields.1
  have reduced := divInt_parts_le z.value.num[j.val] z.value.den (run_den_ne_zero P x h)
  exact ⟨(Nat.size_le_size reduced.1).trans (num.trans fit),
    (Nat.size_le_size reduced.2).trans (den.trans (Nat.mul_le_mul_left 2 fit))⟩

theorem widthLimit_mono : Monotone widthLimit := by
  intro a b le
  unfold widthLimit RecoveryRun.operandLimit PivotRun.width RecoveryRun.scale PointEncoding.wordLimit
  gcongr

/-- A caller may substitute its own upper bound on the dense input length. -/
theorem run_coordinate_size_of_length_le (P : Input m n) (x : Vector ℚ n) {h L : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) (length : inputLength P x h ≤ L) (j : Fin n) :
    let z := (run P x h).value.value j
    z.num.natAbs.size ≤ widthLimit L ∧ z.den.size ≤ 2*widthLimit L := by
  obtain ⟨num,den⟩ := run_coordinate_size P x hp coeff j
  exact ⟨num.trans (widthLimit_mono length),den.trans (Nat.mul_le_mul_left 2 (widthLimit_mono length))⟩

end Kintali.LinearProgramming.RationalInput
