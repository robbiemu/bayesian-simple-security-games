module

public import Kintali.InputOutput.ScalesWork

/-! # Preparing the finite quote-search inputs from the stored game and tolerance

The directory keeps least-index outside minimizers and endpoint costs. The
eligible vector uses one closed-form calculation per type/target pair.
-/

@[expose] public section
namespace Kintali.InputOutput.PrepareWork

open Binary ContactSize TrialWork ExactRecovery MarketTrial NormalizedWork
open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {k m : ℕ}

def positives (d : Fields k m) : List (Fin m) → Run ℕ
  | [] => step 0 0
  | j::js => do
    let g ← d.gain j
    let p ← lt 0 g
    let q ← positives d js
    natAdd q (if p then 1 else 0)

@[simp] theorem positives_value (d : Fields k m) (js : List (Fin m)) : (positives d js).value =
    (js.filter fun j => decide (0 < d.game.gain j)).length := by
  induction js with
  | nil => rfl
  | cons j js ih => by_cases h : 0 < (d.gain j).value <;> simp [positives,ih,h,Fields.game,natAdd]

theorem positives_work (d : Fields k m) {w c S : ℕ} (h : FieldBound d c w) (js : List (Fin m)) (fit : js.length ≤ S) :
    (positives d js).Bound (1+js.length*(c+5)) (S+scalarWidth w) := by
  induction js with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons j js ih =>
    have small : js.length ≤ S := by simp at fit; omega
    have rest := ih small
    have g := (h.gain j).1
    have p := lt_work (Fits.zero.mono h.positive) (h.gain j).2
    have len : (positives d js).value.size ≤ S := (size_le_self _).trans
      (by rw [positives_value]; exact (List.length_filter_le ..).trans small)
    by_cases pos : 0 < (d.gain j).value <;>
      simp [positives,Run.Bound,natAdd,pos,scalarWidth,Nat.succ_mul] at * <;> omega

def witnesses (d : Fields k m) : Run ℕ := do
  let js ← finRange m
  let n ← positives d js
  let a ← natAdd k n
  let b ← natMul k n
  natAdd a b

@[simp] theorem witnesses_value (d : Fields k m) : (witnesses d).value = witnessBound d.game := by
  simp [witnesses,witnessBound,Game.positiveTargets,natAdd,natMul]

def witnessSlots (S c : ℕ) := (2*S+1)+(1+S*(c+5))+3
def witnessWidth (S w : ℕ) := 2*S+scalarWidth w+2

theorem witnesses_work (d : Fields k m) {S w c : ℕ} (h : FieldBound d c w) (kd : k ≤ S) (md : m ≤ S) :
    (witnesses d).Bound (witnessSlots S c) (witnessWidth S w) := by
  let js := List.finRange m
  let n := (positives d js).value
  have len : n ≤ S := by
    dsimp only [n]; rw [positives_value]
    exact (List.length_filter_le ..).trans (by simpa [js] using md)
  have ns := (size_le_self n).trans len
  have ks := (size_le_self k).trans kd
  have ms := (size_le_self m).trans md
  have sum := size_le_self (k+n)
  have mul := size_mul_le k n
  have r := finRange_bound m
  have scan := positives_work d h js (by simpa [js] using md)
  have lenj : js.length ≤ S := by simpa [js] using md
  have sl := scan.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ lenj) 1)
  simp only [witnesses,Run.Bound,Run.bind_slots,Run.bind_width,finRange_value,natAdd,natMul,
    step_width,step_slots,step_value,witnessSlots,witnessWidth] at *
  dsimp only [n,js] at *
  omega

structure Prepared (k m : ℕ) where
  scales : ScalesWork.Scales
  directory : OutsideWork.Directory k m
  witness : ℕ
  counts : Vector ℕ (k*m)

def fromTables (t : Tables k m) (hm : 0 < m) (tol : ℚ) : Run (Prepared k m) := do
  let scales ← ScalesWork.run t.fields tol
  let directory ← OutsideWork.run t.fields hm
  let witness ← witnesses t.fields
  let counts ← EligibilityWork.table t directory.price scales.grid
  step 0 ⟨scales,directory,witness,counts⟩

theorem fromTables_value (a : Input) (hm : 0 < a.targets) (t : Tables a.types a.targets) (ht : t.game = a.game) :
    let p := (fromTables t hm (contactTolerance a.game)).value
    p.scales.grid = grid a.game ∧ p.scales.privateScale = privateScale a.game ∧
      p.witness = witnessBound a.game ∧ p.counts = eligible a.game hm ∧
      ∀ i, p.directory.toSite[i.val] = redirect a.game hm i := by
  have eq : t.fields.game = a.game := ht
  have cs := EligibilityWork.table_value a hm t ht (OutsideWork.run t.fields hm).value.price
    (fun i => by rw [OutsideWork.prices,eq])
  simp only [fromTables,Run.bind_value,step_value,ScalesWork.run_value,witnesses_value,eq]
  exact ⟨rfl,rfl,trivial,cs,fun i => by rw [OutsideWork.targets,eq]⟩

def fieldWidth (S : ℕ) := 2*S+1
def scaleWidth (S : ℕ) := fieldWidth S+toleranceWidth S
def eligibilityWidth (S : ℕ) := S*S+S+OutsideWork.priceWidth (fieldWidth S)+gridBitBound S+2
def setupSlots (S : ℕ) := ScalesWork.workSlots S 2 (scaleWidth S)+OutsideWork.directorySlots S 2 (fieldWidth S)+
  witnessSlots S 2+1+(3*(S*S+1)+S*S*(6+EligibilityWork.countSlots (eligibilityWidth S)))+1
def setupWidth (S : ℕ) := ScalesWork.workWidth (scaleWidth S)+OutsideWork.comparisonWidth (fieldWidth S)+
  witnessWidth S (fieldWidth S)+EligibilityWork.countWidth (eligibilityWidth S)+2*S+1

theorem fromTables_work (a : Input) (valid : a.Valid) (t : Tables a.types a.targets) (ht : t.game = a.game) :
    (fromTables t valid.1 (contactTolerance a.game)).Bound (setupSlots (lengthInput a)) (setupWidth (lengthInput a)) := by
  let S := lengthInput a
  let d := t.fields
  have eq : d.game = a.game := ht
  have ok : FieldBound d 2 (fieldWidth S) := fields_bound a valid t ht
  have kd : a.types ≤ S := (dimensions a).2.1
  have md : a.targets ≤ S := (dimensions a).1
  have ks := (size_le_self _).trans kd
  have ms := (size_le_self _).trans md
  have scale := ScalesWork.run_work d (contactTolerance a.game)
    (ok.mono (Nat.le_add_right (fieldWidth S) (toleranceWidth S)))
    ((tolerance_fits a valid).mono (Nat.le_add_left (toleranceWidth S) (fieldWidth S))) kd md
  have dir := OutsideWork.run_work d valid.1 ok kd md
  have w := witnesses_work d ok kd md
  let E := eligibilityWidth S
  have gridFit : (grid a.game).size+1 ≤ E := by have := grid_size a valid; dsimp [E,eligibilityWidth,S]; omega
  have eWide : S*S+S ≤ E := by dsimp [E,eligibilityWidth]; omega
  have priceWide : OutsideWork.priceWidth (fieldWidth S) ≤ E := by dsimp [E,eligibilityWidth]; omega
  have fits : fieldWidth S ≤ E := by unfold OutsideWork.priceWidth at priceWide; omega
  have scan := EligibilityWork.table_work t (OutsideWork.run d valid.1).value.price kd md eWide gridFit
    (fun j => (ok.gain j).2.mono fits)
    (fun i j => ⟨(ok.intercept i j).2.mono fits,(ok.slope i j).2.mono fits⟩)
    (fun i => by
      rw [OutsideWork.prices]
      have p := OutsideWork.endpoint_fits d ok i (redirect d.game valid.1 i)
      rw [OutsideWork.endpoint_value] at p
      exact p.mono priceWide)
  have value : (ScalesWork.run d (contactTolerance a.game)).value.grid = grid a.game := by rw [ScalesWork.run_value,eq]; rfl
  simp only [fromTables,Run.Bound,Run.bind_slots,Run.bind_width,step_width,step_slots] at *
  change _ ≤ setupSlots S ∧ _ ≤ setupWidth S
  dsimp only [d] at value scan w dir scale
  rw [value]
  change (ScalesWork.run t.fields (contactTolerance a.game)).work.slots ≤ ScalesWork.workSlots S 2 (scaleWidth S) ∧
    (ScalesWork.run t.fields (contactTolerance a.game)).work.width ≤ ScalesWork.workWidth (scaleWidth S) at scale
  dsimp only [E] at scan
  unfold setupSlots setupWidth
  omega

end Kintali.InputOutput.PrepareWork
