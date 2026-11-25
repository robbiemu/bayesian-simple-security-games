module

public import Kintali.InputOutput.NormalizedFields
public import Kintali.InputOutput.EligibilityWork
public import Kintali.TrialWork.Pattern
import Init.Data.List.MinMaxIdx

/-! # Least-index outside targets and their stored endpoint costs -/

@[expose] public section
namespace Kintali.InputOutput.OutsideWork

open Binary NormalizedWork TrialWork ContactSize ExactRecovery MarketTrial LinearProgramming.ArithmeticRun
open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {k m : ℕ}

/-- On the ascending Fin list the first minimizer is the least minimizer. -/
theorem minOn_eq_least {m : ℕ} (hm : 0 < m) (f : Fin m → ℚ) :
    letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
    (List.finRange m).minOn f (List.ne_nil_of_mem (List.mem_finRange ⟨0,hm⟩)) = leastMinimum f := by
  let _ : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  let js := List.finRange m
  have ne : js ≠ [] := List.ne_nil_of_mem (List.mem_finRange ⟨0,hm⟩)
  let a := js.minOn f ne
  let b := leastMinimum f
  have l : f a ≤ f b := List.apply_minOn_le_of_mem (List.mem_finRange b)
  have r : f b ≤ f a := leastMinimum_spec f a
  have hi : b.val < js.length := by simp [js]
  have index := List.minIdxOn_le_of_apply_getElem_le_apply_minOn (f := f) (xs := js) ne hi
    (by simpa [js] using r)
  have pick := List.getElem_minIdxOn (f := f) (xs := js) ne
  have id : js[js.minIdxOn f ne] = (⟨js.minIdxOn f ne, by
    simpa [js] using List.minIdxOn_lt_length (f := f) (xs := js) ne⟩ : Fin m) := List.getElem_finRange _
  rw [id] at pick
  have eq := congrArg Fin.val pick
  exact le_antisymm (by change a.val ≤ b.val; exact eq ▸ index) (leastMinimum_tie (le_antisymm l r))

def endpoint (d : Fields k m) (i : Fin k) (j : Fin m) : Run ℚ := do
  let gain ← d.gain j
  let active ← lt 0 gain
  let x ← step 0 (if active then (1 : ℚ) else 0)
  d.costAt i j x

@[simp] theorem endpoint_value (d : Fields k m) (i : Fin k) (j : Fin m) :
    (endpoint d i j).value = d.game.cost i j (Holdings.endpoint d.game j) := by
  by_cases h : 0 < (d.gain j).value <;> simp [endpoint,Holdings.endpoint,Fields.game,h]

def endpointSlots (c w : ℕ) := c+4+1+costSlots c w
def priceWidth (w : ℕ) := 3*w+1
def comparisonWidth (w : ℕ) := scalarWidth (priceWidth w)

theorem endpoint_fits (d : Fields k m) {c w : ℕ} (h : FieldBound d c w) (i : Fin k) (j : Fin m) :
    Fits (priceWidth w) (endpoint d i j).value := by
  rw [endpoint_value]
  apply d.cost_fits h
  unfold Holdings.endpoint
  split <;> first | exact Fits.one.mono h.positive | exact Fits.zero.mono h.positive

theorem endpoint_work (d : Fields k m) {c w : ℕ} (h : FieldBound d c w) (i : Fin k) (j : Fin m) :
    (endpoint d i j).Bound (endpointSlots c w) (comparisonWidth w) := by
  have g := (h.gain j).1
  have comp := lt_work (Fits.zero.mono h.positive) (h.gain j).2
  have cv : Fits w (if 0 < (d.gain j).value then (1 : ℚ) else 0) := by
    split <;> first | exact Fits.one.mono h.positive | exact Fits.zero.mono h.positive
  have sum := d.costAt_work h i j cv
  simp only [endpoint,Run.Bound,Run.bind_slots,Run.bind_width,lt_value,decide_eq_true_eq,step_value,
    step_slots,step_width,endpointSlots,comparisonWidth,priceWidth,costWidth,scalarWidth] at *
  omega

structure Directory (k m : ℕ) where
  toSite : Vector (Fin m) k
  price : Vector ℚ k

def run (d : Fields k m) (hm : 0 < m) : Run (Directory k m) := do
  let ids ← tabulate k (fun i => bestFin m hm (endpoint d i))
  let prices ← tabulate k (fun i => do
    let j ← step k.size ids[i.val]
    endpoint d i j)
  step 0 ⟨ids,prices⟩

theorem targets (d : Fields k m) (hm : 0 < m) (i : Fin k) :
    (run d hm).value.toSite[i.val] = redirect d.game hm i := by
  simp only [run,Run.bind_value,step_value,tabulate_value,Vector.getElem_ofFn,bestFin_value,endpoint_value]
  exact minOn_eq_least hm _

theorem prices (d : Fields k m) (hm : 0 < m) (i : Fin k) :
    (run d hm).value.price[i.val] = Holdings.outsideCost d.game (redirect d.game hm) i := by
  let j := (run d hm).value.toSite[i.val]
  change _ = d.game.cost i (redirect d.game hm i) (Holdings.endpoint d.game (redirect d.game hm i))
  rw [← targets d hm i]
  simp [run]

def bestSlots (S c w : ℕ) := 2*S+1+(1+S*(2*endpointSlots c w+4))
def directorySlots (S c w : ℕ) := 3*(S+1)+S*bestSlots S c w+(3*(S+1)+S*(1+endpointSlots c w))+1

theorem run_work (d : Fields k m) (hm : 0 < m) {c w S : ℕ} (h : FieldBound d c w)
    (kd : k ≤ S) (md : m ≤ S) :
    (run d hm).Bound (directorySlots S c w) (comparisonWidth w) := by
  let W := comparisonWidth w
  have wide : w ≤ W := by unfold W comparisonWidth scalarWidth priceWidth; omega
  have best (i : Fin k) : (bestFin m hm (endpoint d i)).Bound (bestSlots S c w) W :=
    (bestFin_work hm (endpoint d i) (h.mSize.trans wide) (endpoint_work d h i) (endpoint_fits d h i)
      le_rfl).weaken (by unfold bestSlots; gcongr) le_rfl
  have ids := tabulate_bound _ (h.kSize.trans wide) best
  have ps (v : Vector (Fin m) k) := tabulate_bound (fun i => do
    let j ← step k.size v[i.val]
    endpoint d i j) (h.kSize.trans wide) (fun i =>
      bound_bind ((bound_step k.size v[i.val]).weaken le_rfl (h.kSize.trans wide)) (endpoint_work d h i v[i.val]))
  let saved := (tabulate k (fun i => bestFin m hm (endpoint d i))).value
  have vals := ps saved
  have ib := ids.1.trans (Nat.add_le_add (Nat.mul_le_mul_left 3 (Nat.add_le_add_right kd 1)) (Nat.mul_le_mul_right _ kd))
  have pb := vals.1.trans (Nat.add_le_add (Nat.mul_le_mul_left 3 (Nat.add_le_add_right kd 1)) (Nat.mul_le_mul_right _ kd))
  simp only [run,Run.Bound,Run.bind_width,Run.bind_slots,step_slots,step_width,directorySlots] at *
  dsimp only [saved,W] at *
  omega

end Kintali.InputOutput.OutsideWork
