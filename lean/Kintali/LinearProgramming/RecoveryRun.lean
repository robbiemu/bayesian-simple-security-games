module

public import Kintali.LinearProgramming.CramerCost
public import Kintali.LinearProgramming.PrecisionRun
public import Kintali.LinearProgramming.WindowRun

/-! # The stored integer recovery algorithm

The run takes a dense integer inequality system and a common-denominator
rational point. It computes the precision, residuals, slack mask, pivot
and output integers, in that order. Every intermediate table is bound once.
-/

@[expose] public section

namespace Kintali.LinearProgramming.RecoveryRun

open StochasticGames.CompilerRun PivotRun PointRun

variable {m n : ℕ}

def classify (res : Vector ℤ m) (D : ℕ) (p : PrecisionRun.Parameters) : Run (Vector Bool m) := do
  let z ← PointRun.scaledResiduals p.divisor res
  WindowRun.mark z D p.radix

def run (P : Input m n) (X : Point n) (h : ℕ) : Run (CramerRun.Answer n) := do
  let p ← PrecisionRun.setup m n h
  let res ← PointRun.residuals P X
  let mask ← classify res X.den p
  let s ← PivotRun.choose P mask
  CramerRun.repair P X res s

theorem classify_value (P : Input m n) (X : Point n) (h : ℕ) (positive : 0 < h) :
    (classify (PointRun.residuals P X).value X.den (PrecisionRun.setup m n h).value).value =
      Vector.ofFn (P.system.nearlyTight h X.scaled.value) := by
  let Q := SlackWindow.divisor m n h
  let K := SlackWindow.radix n h
  let z := (PointRun.scaledResiduals Q (PointRun.residuals P X).value).value
  have cleared (i : Fin m) : (z[i.val] : ℚ) = (X.den : ℚ)*Q*P.system.slack X.scaled.value i := by
    simp only [z, PointRun.scaledResiduals_value, PointRun.residuals_value, Vector.getElem_ofFn,
      Int.cast_mul, Int.cast_natCast, ScaledPoint.cast_residual]
    rw [show X.scaled.den = X.den from rfl]
    ring
  simp only [classify, Run.bind_value, PrecisionRun.setup_value]
  change (WindowRun.mark z X.den K).value = _
  exact WindowRun.mark_value z X.den K Q X.positive (SlackWindow.divisor_pos m n positive) _ cleared

theorem run_value (P : Input m n) (X : Point n) (h : ℕ) (positive : 0 < h) :
    (run P X h).value.value = P.system.recover h X.scaled.value := by
  let res := (PointRun.residuals P X).value
  let mask := (classify res X.den (PrecisionRun.setup m n h).value).value
  let s := (PivotRun.choose P mask).value
  have selected : s.view = Minor.choose P.system (P.system.nearlyTight h X.scaled.value) := by
    rw [show s.view = _ from PivotRun.choose_value P mask]
    congr 1
    funext i
    simp [mask, res, classify_value P X h positive]
  have reg : (s.view.matrix P.system).det ≠ 0 := by
    rw [selected]
    exact (Minor.choose_spec ..).1
  have rr (i : Fin m) : res[i.val] = X.scaled.residual P.system i := by simp [res]
  simp only [run, Run.bind_value]
  change (CramerRun.repair P X res s).value.value = _
  rw [CramerRun.repair_value P X res s rr reg]
  change (s.view.pivot P.system).repair P.system X.scaled.value = _
  rw [selected]
  rfl

theorem run_feasible (P : Input m n) (X : Point n) (h : ℕ) (positive : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ))
    (approximate : ∀ i, -SlackWindow.precision m n h ≤ P.system.slack X.scaled.value i) :
    P.system.Feasible (run P X h).value.value := by
  rw [run_value P X h positive]
  exact P.system.recover_feasible h X.scaled.value positive coeff approximate

end Kintali.LinearProgramming.RecoveryRun
