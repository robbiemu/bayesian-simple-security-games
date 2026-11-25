module

public import Kintali.InputOutput.OutsideWork

/-! # Computing the largest gain and largest slope at an active site -/

@[expose] public section
namespace Kintali.InputOutput.MaximaWork

open TrialWork ContactSize ExactRecovery StochasticGames.CompilerRun StochasticGames.BinarySize

variable {α : Type} {k m : ℕ}

def scan (f : α → Run ℚ) : List α → Run ℚ
  | [] => step 0 0
  | j::js => do
    let x ← f j
    let y ← scan f js
    let small ← le x y
    step 0 (if small then y else x)

@[simp] theorem scan_nil (f : α → Run ℚ) : (scan f []).value = 0 := rfl
@[simp] theorem scan_cons (f : α → Run ℚ) (j : α) (js : List α) :
    (scan f (j::js)).value = max (f j).value (scan f js).value := by simp [scan,max_def]

theorem scan_nonneg (f : α → Run ℚ) (js : List α) : 0 ≤ (scan f js).value := by
  induction js with
  | nil => rfl
  | cons j js ih => rw [scan_cons]; exact ih.trans (le_max_right ..)

theorem scan_ge (f : α → Run ℚ) (js : List α) (j : α) (mem : j ∈ js) : (f j).value ≤ (scan f js).value := by
  induction js with
  | nil => contradiction
  | cons k ks ih =>
    rw [scan_cons]
    rcases List.mem_cons.mp mem with rfl|h
    · exact le_max_left ..
    · exact (ih h).trans (le_max_right ..)

theorem scan_le (f : α → Run ℚ) (js : List α) (z : ℚ) (zero : 0 ≤ z) (bound : ∀ j ∈ js, (f j).value ≤ z) :
    (scan f js).value ≤ z := by
  induction js with
  | nil => exact zero
  | cons j js ih => rw [scan_cons]; exact max_le (bound j (by simp)) (ih (fun k m => bound k (List.mem_cons_of_mem _ m)))

theorem scan_fits (f : α → Run ℚ) (js : List α) {w : ℕ} (one : 1 ≤ w) (small : ∀ j, Fits w (f j).value) :
    Fits w (scan f js).value := by
  induction js with
  | nil => exact Fits.zero.mono one
  | cons j js ih => rw [scan_cons,max_def]; split <;> first | exact ih | exact small j

theorem scan_work (f : α → Run ℚ) (js : List α) {c w W : ℕ} (one : 1 ≤ w) (width : scalarWidth w ≤ W)
    (cost : ∀ j, (f j).Bound c W) (small : ∀ j, Fits w (f j).value) :
    (scan f js).Bound (1+js.length*(c+4)) W := by
  induction js with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons j js ih =>
    have f' := cost j
    have comp := (le_work (small j) (scan_fits f js one small)).weaken le_rfl width
    simp only [scan,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,List.length_cons,Nat.succ_mul] at *
    omega

def over (n : ℕ) (f : Fin n → Run ℚ) : Run ℚ := finRange n >>= scan f
@[simp] theorem over_value (n : ℕ) (f : Fin n → Run ℚ) :
    (over n f).value = (scan f (List.finRange n)).value := by simp [over]

theorem over_fits (n : ℕ) (f : Fin n → Run ℚ) {w : ℕ} (one : 1 ≤ w) (small : ∀ i, Fits w (f i).value) :
    Fits w (over n f).value := by rw [over_value]; exact scan_fits _ _ one small

def overSlots (S c : ℕ) := 2*S+1+(1+S*(c+4))

theorem over_work (n : ℕ) (f : Fin n → Run ℚ) {S c w W : ℕ} (dim : n ≤ S) (idx : n.size ≤ W)
    (one : 1 ≤ w) (width : scalarWidth w ≤ W) (cost : ∀ i, (f i).Bound c W) (small : ∀ i, Fits w (f i).value) :
    (over n f).Bound (overSlots S c) W := by
  have h := scan_work f (List.finRange n) one width cost small
  have d := finRange_bound n
  have mul := Nat.mul_le_mul_right (c+4) dim
  simp only [over,Run.Bound,Run.bind_slots,Run.bind_width,finRange_value,List.length_finRange,overSlots] at *
  omega

def gainMax (d : Fields k m) := over m d.gain

theorem gain_value (d : Fields k m) : (gainMax d).value = maxGain d.game := by
  let L := List.finRange m
  let T := insert 0 (Finset.univ.image d.game.gain)
  have ub (j : Fin m) : (d.gain j).value ≤ maxGain d.game :=
    Finset.le_max' T ((d.gain j).value) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have zero : (0 : ℚ) ≤ maxGain d.game := Finset.le_max' T 0 (Finset.mem_insert_self ..)
  rw [gainMax,over_value]
  apply le_antisymm (scan_le _ _ _ zero (fun j _ => ub j))
  apply Finset.max'_le
  intro q mem
  rcases Finset.mem_insert.mp mem with rfl|img
  · exact scan_nonneg _ _
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp img
    exact scan_ge d.gain L j (List.mem_finRange j)

def activeSlope (d : Fields k m) (i : Fin k) (j : Fin m) : Run ℚ := do
  let g ← d.gain j
  let pos ← lt 0 g
  if pos then d.slope i j else step 0 0

@[simp] theorem active_value (d : Fields k m) (i : Fin k) (j : Fin m) :
    (activeSlope d i j).value = if 0 < d.game.gain j then d.game.slope i j else 0 := by
  by_cases h : 0 < (d.gain j).value <;> simp [activeSlope,Fields.game,h]

theorem active_fits (d : Fields k m) {w c : ℕ} (fit : FieldBound d c w) (i : Fin k) (j : Fin m) :
    Fits w (activeSlope d i j).value := by rw [active_value]; split <;> first | exact (fit.slope i j).2 | exact Fits.zero.mono fit.positive

theorem active_work (d : Fields k m) {w c : ℕ} (fit : FieldBound d c w) (i : Fin k) (j : Fin m) :
    (activeSlope d i j).Bound (2*c+5) (scalarWidth w) := by
  have g := (fit.gain j).1
  have s := (fit.slope i j).1
  have test := lt_work (Fits.zero.mono fit.positive) (fit.gain j).2
  by_cases h : 0 < (d.gain j).value <;> simp [activeSlope,Run.Bound,h,scalarWidth] at * <;> omega

def slopeMax (d : Fields k m) := over k (fun i => over m (activeSlope d i))

theorem slope_value (d : Fields k m) : (slopeMax d).value = maxSiteSlope d.game := by
  let F := activeSlope d
  let T := siteSlopes d.game
  let rows := fun i => over m (F i)
  have zero : (0 : ℚ) ≤ maxSiteSlope d.game := Finset.le_max' T _ (Finset.mem_insert_self ..)
  have ub (i : Fin k) (j : Fin m) : (F i j).value ≤ maxSiteSlope d.game := by
    rw [show (F i j).value = _ from active_value d i j]
    split
    · rename_i pos
      exact Finset.le_max' T _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ (i,j),pos⟩)))
    · exact zero
  change (over k rows).value = _
  rw [over_value]
  refine le_antisymm (scan_le _ _ _ zero (fun i _ => ?_)) ?_
  · rw [show (rows i).value = _ from over_value m (F i)]
    exact scan_le _ _ _ zero fun j _ => ub i j
  apply Finset.max'_le
  intro q mem
  rcases Finset.mem_insert.mp mem with rfl|img
  · exact scan_nonneg _ _
  · obtain ⟨⟨i,j⟩,inSet,rfl⟩ := Finset.mem_image.mp img
    have pos := (Finset.mem_filter.mp inSet).2
    have row := scan_ge rows (List.finRange k) i (List.mem_finRange i)
    have col := scan_ge (F i) (List.finRange m) j (List.mem_finRange j)
    exact (by simpa only [F,active_value,ite_eq_left pos] using col :
      d.game.slope i j ≤ (scan (F i) (List.finRange m)).value) |>.trans (by simpa [rows] using row)

theorem bounds (d : Fields k m) {S c w : ℕ} (fit : FieldBound d c w) (kd : k ≤ S) (md : m ≤ S) :
    (gainMax d).Bound (overSlots S c) (scalarWidth w) ∧ Fits w (gainMax d).value ∧
    (slopeMax d).Bound (overSlots S (overSlots S (2*c+5))) (scalarWidth w) ∧ Fits w (slopeMax d).value := by
  have wide : w ≤ scalarWidth w := by unfold scalarWidth; omega
  have row (i : Fin k) := over_work m (activeSlope d i) md (fit.mSize.trans wide) fit.positive le_rfl
    (active_work d fit i) (active_fits d fit i)
  have small (i : Fin k) := over_fits m (activeSlope d i) fit.positive (active_fits d fit i)
  exact ⟨over_work m d.gain md (fit.mSize.trans wide) fit.positive le_rfl
    (fun j => (fit.gain j).1.weaken le_rfl wide) (fun j => (fit.gain j).2),
    over_fits m d.gain fit.positive (fun j => (fit.gain j).2),
    over_work k _ kd (fit.kSize.trans wide) fit.positive le_rfl row small,over_fits k _ fit.positive small⟩

end Kintali.InputOutput.MaximaWork
