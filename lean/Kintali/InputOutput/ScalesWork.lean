module

public import Kintali.InputOutput.MaximaWork

/-! # Computing the private scale and quote grid from the contact tolerance -/

@[expose] public section
namespace Kintali.InputOutput.ScalesWork

open Binary MaximaWork TrialWork ContactSize ExactRecovery StochasticGames.CompilerRun StochasticGames.BinarySize

def ceilNat (q : ℚ) : Run ℕ := do
  let n ← step (q.num.natAbs.size+1) (-q.num)
  let d ← step (max n.natAbs.size q.den.size+1) (n / (q.den : ℤ))
  let c ← step (d.natAbs.size+1) (-d)
  step (c.natAbs.size+1) c.toNat

@[simp] theorem ceil_value (q : ℚ) : (ceilNat q).value = ⌈q⌉₊ := by
  simp only [ceilNat,Run.bind_value,step_value,← Int.ceil_toNat,Rat.ceil_def']

theorem ceil_work {q : ℚ} {w : ℕ} (h : Fits w q) : (ceilNat q).Bound 4 (w+1) ∧ (⌈q⌉₊).size ≤ w := by
  have div := Nat.size_le_size (Int.natAbs_ediv_le_natAbs (-q.num) (q.den : ℤ))
  have abs (z : ℤ) : z.toNat ≤ z.natAbs := by rw [← Int.toNat_add_toNat_neg_eq_natAbs]; omega
  have cn := Nat.size_le_size (abs (-(-q.num/(q.den : ℤ))))
  obtain ⟨h₁,h₂⟩ := h
  simp only [ceilNat,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,step_value,
    Int.natAbs_neg,← Int.ceil_toNat,Rat.ceil_def'] at *
  omega

structure Scales where
  privateScale : ℚ
  grid : ℕ

def run {k m : ℕ} (d : Fields k m) (tolerance : ℚ) : Run Scales := do
  let largest ← gainMax d
  let high ← le 1 largest
  let denominator ← step 0 (if high then largest else 1)
  let scale ← divide tolerance denominator
  let slope ← slopeMax d
  let ratio ← divide slope tolerance
  let n ← ceilNat ratio
  let grid ← step (max 1 n.size) (max 1 n)
  step 0 ⟨scale,grid⟩

theorem run_value {k m : ℕ} (d : Fields k m) (tolerance : ℚ) :
    (run d tolerance).value = ⟨sigma d.game tolerance,gridSize d.game tolerance⟩ := by
  simp [run,gain_value,slope_value,sigma,gridSize,max_def]

def workSlots (S c w : ℕ) := overSlots S c+overSlots S (overSlots S (2*c+5))+2*(4+scalarSlots w)+10
def workWidth (w : ℕ) := scalarWidth w+3

theorem run_work {k m : ℕ} (d : Fields k m) (tolerance : ℚ) {c w S : ℕ}
    (h : FieldBound d c w) (tol : Fits w tolerance) (kd : k ≤ S) (md : m ≤ S) :
    (run d tolerance).Bound (workSlots S c w) (workWidth w) := by
  obtain ⟨gain,gn,slope,sn⟩ := bounds d h kd md
  have one := Fits.one.mono h.positive
  have cmp := le_work one gn
  let den := if 1 ≤ (gainMax d).value then (gainMax d).value else 1
  have df : Fits w den := by dsimp [den]; split <;> assumption
  have scale := divide_work tol df
  have ratio := divide_work sn tol
  have cc := ceil_work (sn.div tol)
  simp only [run,Run.Bound,Run.bind_slots,Run.bind_width,
    le_value,decide_eq_true_eq,step_value,step_slots,step_width,divide_value,ceil_value,
    workSlots,workWidth,scalarWidth] at *
  dsimp only [den] at *
  omega

end Kintali.InputOutput.ScalesWork
