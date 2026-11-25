module

public import Kintali.InputOutput.DenominatorWork
public import Kintali.ContactSize.Parameters
public import Kintali.LinearProgramming.PrecisionRun
import all Kintali.InputOutput.Grid

/-! # Computing contact tolerance from the distinct rational data

The two inverse precisions have numerator one. Taking their minimum amounts
to selecting the larger positive denominator. This allows the prepared
game to reuse the charged integer-power and LP radix routines.
-/

@[expose] public section
namespace Kintali.InputOutput.ToleranceWork

open Binary NormalizedWork DatumWork ContactSize ExactRecovery LinearProgramming
open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {k m : ℕ}

structure Dimensions where
  rows : ℕ
  vars : ℕ

def dimensionsRun (k m : ℕ) : Run Dimensions := do
  let km ← natMul k m
  let m2 ← natAdd m 2
  let vars ← natAdd km m2
  let bids ← natMul 4 km
  let two ← natMul 2 k
  let bounds ← natAdd two 6
  let row ← natAdd bids bounds
  let six ← natMul 6 m
  let rows ← natAdd six row
  step 0 ⟨rows,vars⟩

@[simp] theorem dimensions_value (k m : ℕ) :
    (dimensionsRun k m).value = ⟨exactRows k m,exactVars k m⟩ := by simp [dimensionsRun,exactRows,exactVars,natAdd,natMul]

theorem dimensions_work (k m : ℕ) : (dimensionsRun k m).Bound 10 (exactRows k m+exactVars k m+6) := by
  have h := size_le_self
  have k' := h k
  have m' := h m
  have km := h (k*m)
  have m2 := h (m+2)
  have bids := h (4*(k*m))
  have two := h (2*k)
  have bounds := h (2*k+6)
  have row := h (4*(k*m)+(2*k+6))
  have six := h (6*m)
  simp only [dimensionsRun,Run.Bound,Run.bind_slots,Run.bind_width,natAdd,natMul,step_slots,step_width,
    step_value,exactRows,exactVars]
  norm_num
  have : (4 : ℕ).size = 3 := rfl
  have : (6 : ℕ).size = 3 := rfl
  have : (2 : ℕ).size = 2 := rfl
  omega

def C (x : ScaleData) := 2*(x.magnitude*x.denominator)
def dataOf (g : Game (Fin k) (Fin m)) : ScaleData := ⟨denominator g,magnitude g⟩

@[simp] theorem coefficient_eq (g : Game (Fin k) (Fin m)) : C (dataOf g) = coefficientHeight g := by
  simp [C,dataOf,coefficientHeight,atomBound,Int.natAbs_mul]

@[simp] theorem height_eq (g : Game (Fin k) (Fin m)) :
    (exactVars k m*coefficientHeight g)^(exactVars k m) = height g := by
  rw [← coefficient_eq]
  simp only [height,variable_count,Fintype.card_fin,C,dataOf,exactVars]
  ring_nf

def required (g : Game (Fin k) (Fin m)) := max (4*height g) (SlackWindow.divisor (exactRows k m) (exactVars k m) (coefficientHeight g))

theorem required_pos (g : Game (Fin k) (Fin m)) : 0 < required g :=
  (SlackWindow.divisor_pos _ _ (coefficientHeight_pos g)).trans_le (le_max_right ..)

theorem tolerance_eq (g : Game (Fin k) (Fin m)) : contactTolerance g = 1/(required g : ℚ) := by
  let A := 4 * height g
  let B := SlackWindow.divisor (exactRows k m) (exactVars k m) (coefficientHeight g)
  have ap : (0 : ℚ) < (A : ℚ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 4) (height_pos g)
  have bp : (0 : ℚ) < (B : ℚ) := by exact_mod_cast SlackWindow.divisor_pos _ _ (coefficientHeight_pos g)
  have a : eta g = 1/(A : ℚ) := by simp [eta,A]
  change min (eta g) (1/(B : ℚ)) = 1/((max A B : ℕ) : ℚ)
  rw [a]
  rcases le_total A B with h|h
  · rw [max_eq_right h,min_eq_right (one_div_le_one_div_of_le ap (by exact_mod_cast h))]
  · rw [max_eq_left h,min_eq_left (one_div_le_one_div_of_le bp (by exact_mod_cast h))]

theorem required_size (a : Input) (v : a.Valid) : (required a.game).size ≤ toleranceWidth (lengthInput a) := by
  have small := (tolerance_fits a v).2
  rw [tolerance_eq,one_div,Rat.den_inv] at small
  simpa [ne_of_gt (required_pos a.game)] using small

structure Constants where
  denominator : ℕ
  coefficient : ℕ
  tolerance : ℚ

def scalar (d : Dimensions) (x : ScaleData) : Run Constants := do
  let factor ← natMul x.magnitude x.denominator
  let coeff ← natMul 2 factor
  let base ← natMul d.vars coeff
  let H ← ScalarRun.power base d.vars
  let safe ← natMul 4 H
  let lp ← PrecisionRun.setup d.rows d.vars coeff
  let n ← step (max safe.size lp.divisor.size) (max safe lp.divisor)
  let tol ← CodecWork.reduce 1 n
  step 0 ⟨x.denominator,coeff,tol⟩

theorem scalar_value (g : Game (Fin k) (Fin m)) :
    (scalar ⟨exactRows k m,exactVars k m⟩ (dataOf g)).value = ⟨denominator g,coefficientHeight g,contactTolerance g⟩ := by
  have c := coefficient_eq g
  change 2*((dataOf g).magnitude*(dataOf g).denominator) = _ at c
  simp only [scalar,Run.bind_value,step_value,natMul,ScalarRun.power_value,PrecisionRun.setup_value,
    CodecWork.reduce_value,c,height_eq,tolerance_eq,required]
  norm_num [dataOf]

def operandWidth (S : ℕ) := toleranceWidth S+2*repairBound S+10
def scalarSlots (S : ℕ) := 20*(repairBound S+4)+5*operandWidth S+20

set_option maxHeartbeats 800000 in
theorem scalar_work (a : Input) (v : a.Valid) :
    (scalar ⟨exactRows a.types a.targets,exactVars a.types a.targets⟩ (dataOf a.game)).Bound
      (scalarSlots (lengthInput a)) (operandWidth (lengthInput a)+2) := by
  let g := a.game
  let S := lengthInput a
  let W := operandWidth S
  let U := repairBound S
  let r := exactRows a.types a.targets
  let n := exactVars a.types a.targets
  let c := coefficientHeight g
  let d := denominator g
  let m := magnitude g
  let Q := SlackWindow.divisor r n c
  let A := 4*height g
  have raw : (max A Q).size ≤ W := (required_size a v).trans (by dsimp [W,S,operandWidth]; omega)
  have size {x : ℕ} (hx : x ≤ max A Q) : x.size ≤ W := (Nat.size_le_size hx).trans raw
  have ap : 0 < n := by dsimp [n,exactVars]; omega
  have cp : 0 < c := coefficientHeight_pos g
  have bp : 0 < n*c := Nat.mul_pos ap cp
  have power : (n*c)^n = height g := height_eq _
  have base : n*c ≤ (n*c)^n := by simpa only [pow_one] using (Nat.pow_le_pow_right bp (by omega : 1 ≤ n))
  have hr : height g ≤ A := by dsimp [A]; omega
  have hb : n*c ≤ max A Q := base.trans (power ▸ hr.trans (le_max_left ..))
  have co : c ≤ max A Q := (Nat.le_mul_of_pos_left c ap).trans hb
  have ce : 2*(m*d) = c := coefficient_eq _
  have fac : m*d ≤ max A Q := by omega
  have dfit := size ((Nat.le_mul_of_pos_left d (magnitude_pos g)).trans fac)
  have mfit := size ((Nat.le_mul_of_pos_right m (denominator_pos g)).trans fac)
  have ffit := size fac
  have cfit := size co
  have bfit := size hb
  have hfit := size (hr.trans (le_max_left ..))
  have safe := size (le_max_left A Q)
  have qfit := size (le_max_right A Q)
  obtain ⟨rb,nb,_,_⟩ := Binary.repair_bounds a v
  have nr : n ≤ U := nb
  have rr : r ≤ U := rb
  have uw : U+1 ≤ W := by dsimp [U,W,operandWidth]; omega
  have counter := (size_le_self (U+1)).trans uw
  have nw := (size_le_self n).trans (nr.trans (by omega : U ≤ W))
  have exp := ScalarRun.power_work (n*c) n n W le_rfl bp nw bfit (power ▸ hfit)
  have prec := PrecisionRun.setup_work cp (Nat.add_le_add_right rr 1) (Nat.add_le_add_right nr 1)
    counter cfit qfit (by dsimp [W,operandWidth]; omega)
  have reduced := CodecWork.reduce_work (1 : ℤ) (max A Q) (W := W) (by change 1 ≤ W; omega) raw
  have cc : 2*((dataOf g).magnitude*(dataOf g).denominator) = c := ce
  change (scalar ⟨r,n⟩ (dataOf g)).Bound (scalarSlots S) (W+2)
  simp only [scalar,Run.Bound,Run.bind_slots,Run.bind_width,natMul,step_value,step_slots,step_width,cc,
    ScalarRun.power_value,PrecisionRun.setup_value,power] at *
  change m.size ≤ W at mfit
  change d.size ≤ W at dfit
  simp only [dataOf] at *
  dsimp only [r,n,c,m,d,Q,A,W,U,S,g] at *
  have : (4 : ℕ).size = 3 := rfl
  have : (2 : ℕ).size = 2 := rfl
  unfold scalarSlots
  constructor
  · omega
  · simp only [max_le_iff]
    omega

def parameters {k m : ℕ} (t : Tables k m) : Run Constants := do
  let data ← collect t.fields
  let dimensions ← dimensionsRun k m
  scalar dimensions data

theorem parameters_value {k m : ℕ} (t : Tables k m) : (parameters t).value =
    ⟨denominator t.game,coefficientHeight t.game,contactTolerance t.game⟩ := by
  simp only [parameters,Run.bind_value,collect_value,dimensions_value,Tables.fields_game]
  exact scalar_value t.game

def setupSlots (S : ℕ) := DatumWork.scaleSlots S+10+scalarSlots S
def setupWidth (S : ℕ) := DatumWork.scaleWidth S+operandWidth S+2

theorem parameters_work (a : Input) (v : a.Valid) (t : Tables a.types a.targets) (ht : t.game = a.game) :
    (parameters t).Bound (setupSlots (lengthInput a)) (setupWidth (lengthInput a)) := by
  have data := collect_work a v t ht
  have dims := dimensions_work a.types a.targets
  have arithmetic := scalar_work a v
  obtain ⟨rows,vars,_,_⟩ := Binary.repair_bounds a v
  simp only [parameters,Run.Bound,Run.bind_slots,Run.bind_width,collect_value,dimensions_value,Tables.fields_game,ht,
    setupSlots,setupWidth] at *
  simp only [dataOf] at arithmetic
  unfold operandWidth at *
  omega

def run {k m : ℕ} (t : Tables k m) : Run ℚ :=
  let p := parameters t
  ⟨p.value.tolerance,p.work⟩

theorem run_value {k m : ℕ} (t : Tables k m) : (run t).value = contactTolerance t.game := by simp [run,parameters_value]

theorem run_work (a : Input) (v : a.Valid) (t : Tables a.types a.targets) (ht : t.game = a.game) :
    (run t).Bound (setupSlots (lengthInput a)) (setupWidth (lengthInput a)) := by
  simpa only [run,Run.Bound] using parameters_work a v t ht

end Kintali.InputOutput.ToleranceWork
