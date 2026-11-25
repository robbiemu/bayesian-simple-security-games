module

public import Kintali.LinearProgramming.OutputSize
public import StochasticGames.CostedBinary
import all StochasticGames.CostedBinary

/-! # Writing the repaired point as a binary stream

The format writes the dimension, the shared signed denominator, then the
signed numerators in coordinate order. It uses the project's existing
self-delimiting natural and integer encodings and their charged writers.
-/

@[expose] public section

namespace Kintali.LinearProgramming.OutputEncoding

open StochasticGames.CompilerRun StochasticGames.BinarySize StochasticGames.CompilationCost
open StochasticGames.CostedBinary PivotRun CramerRun

variable {m n : ℕ}

def bits (A : Answer n) : List Bool :=
  natBits n ++ intBits A.den ++ (List.finRange n).flatMap (fun j => intBits A.num[j.val])

def fields (A : Answer n) : List (Fin n) → Run (List Bool)
  | [] => step 0 []
  | j :: js => do
    let z ← step n.size A.num[j.val]
    let tail ← fields A js
    writeInt z tail

def write (A : Answer n) : Run (List Bool) := do
  let js ← finRange n
  let nums ← fields A js
  let rest ← writeInt A.den nums
  writeNat n rest

private theorem fields_value (A : Answer n) (js : List (Fin n)) :
    (fields A js).value = js.flatMap (fun j => intBits A.num[j.val]) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [fields, Run.bind_value, step_value, List.flatMap_cons]
    rw [(writeInt_spec _ _ (le_rfl : A.num[j.val].natAbs.size ≤ _)).out, ih]

theorem write_value (A : Answer n) : (write A).value = bits A := by
  simp only [write, Run.bind_value, finRange_value, fields_value]
  rw [(writeInt_spec _ _ (le_rfl : A.den.natAbs.size ≤ _)).out,
    (writeNat_spec _ _ (le_rfl : n.size ≤ _)).out]
  simp [bits, List.append_assoc]

private theorem fields_work (A : Answer n) (js : List (Fin n)) {W : ℕ}
    (indices : n.size ≤ W) (nums : ∀ j : Fin n, A.num[j.val].natAbs.size ≤ W) :
    (fields A js).Bound (1+js.length*(8*W+9)) (W+3) := by
  induction js with
  | nil => exact ⟨by simp [fields],by simp [fields]⟩
  | cons j js ih =>
    have put := (writeInt_spec A.num[j.val] (fields A js).value (nums j)).cost
    have len : (intBits A.num[j.val]).length ≤ 2*W+2 := by
      simp only [intBits, List.length_cons, natBits_length]
      have := nums j
      omega
    constructor
    · change 1+((fields A js).work.slots + (writeInt A.num[j.val] (fields A js).value).work.slots) ≤
        1+(js.length+1)*(8*W+9)
      have p := put.1
      have tail := ih.1
      rw [Nat.add_mul]
      omega
    · exact max_le (by change n.size ≤ W+3; omega) (max_le ih.2 put.2)

theorem write_work (A : Answer n) {W : ℕ} (indices : n.size ≤ W)
    (den : A.den.natAbs.size ≤ W) (nums : ∀ j : Fin n, A.num[j.val].natAbs.size ≤ W) :
    (write A).Bound (32*(n+1)*(W+2)) (W+3) := by
  let js := List.finRange n
  let tail := (fields A js).value
  let ds := (writeInt A.den tail).value
  have ran := finRange_bound n
  have fs := fields_work A js indices nums
  have ws := (writeInt_spec A.den tail den).cost
  have hd := (writeNat_spec n ds indices).cost
  have dl : (intBits A.den).length ≤ 2*W+2 := by simp only [intBits,List.length_cons,natBits_length]; omega
  have nl : (natBits n).length ≤ 2*W+1 := by simp only [natBits_length]; omega
  constructor
  · simp only [write, Run.bind_slots, finRange_value]
    change (finRange n).work.slots+((fields A js).work.slots+((writeInt A.den tail).work.slots+
      (writeNat n ds).work.slots)) ≤ _
    have r := ran.1
    have f : (fields A js).work.slots ≤ 1+n*(8*W+9) := by
      simpa only [show js.length = n from List.length_finRange] using fs.1
    have w := ws.1
    have h := hd.1
    ring_nf at f ⊢
    omega
  · simp only [write, Run.bind_width, finRange_value]
    exact max_le (ran.2.trans (by omega)) (max_le fs.2 (max_le ws.2 hd.2))

def run (P : Input m n) (x : Vector ℚ n) (h : ℕ) : Run (List Bool) :=
  RationalInput.run P x h >>= write

theorem run_value (P : Input m n) (x : Vector ℚ n) (h : ℕ) :
    (run P x h).value = bits (RationalInput.run P x h).value := by
  simp only [run, Run.bind_value, write_value]

def fieldWidth (S : ℕ) := 2*RationalInput.widthLimit S+S+1

def slots (S : ℕ) := RationalInput.slotLimit S + 32*(S+1)*(fieldWidth S+2)

theorem run_work (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) :
    (run P x h).Bound (slots (RationalInput.inputLength P x h)) (fieldWidth (RationalInput.inputLength P x h)+3) := by
  let S := RationalInput.inputLength P x h
  let v := RationalInput.run P x h
  have main := RationalInput.run_work P x hp coeff
  have fit : v.work.width ≤ RationalInput.widthLimit S := main.2
  have dim : n ≤ S := by dsimp [S,RationalInput.inputLength]; omega
  have idx := (size_le_self n).trans dim
  obtain ⟨den,nums⟩ := OutputSize.rational_fields P x h
  change v.value.den.natAbs.size ≤ 2*v.work.width at den
  change ∀ j : Fin n, v.value.num[j.val].natAbs.size ≤ v.work.width at nums
  have wt : v.work.width ≤ fieldWidth S := by unfold fieldWidth; omega
  have send := write_work v.value (by unfold fieldWidth; omega : n.size ≤ fieldWidth S)
    (by unfold fieldWidth; omega) (fun j => (nums j).trans wt)
  exact (bound_bind (f := write) (main.weaken le_rfl (by change RationalInput.widthLimit S ≤ fieldWidth S + 3; unfold fieldWidth; omega)) send).weaken
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 32 (Nat.add_le_add_right dim 1))) _) le_rfl

def binaryLimit (S : ℕ) := slots S * (64*(S+slots S+3*(fieldWidth S+3)+16)^3)

/-- Binary word work of ordinary rational input recovery, including every
emitted bit of the signed shared-denominator result. -/
theorem run_binary_work (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) :
    RecoveryRun.binaryWork (RationalInput.inputLength P x h) (run P x h).work ≤
      binaryLimit (RationalInput.inputLength P x h) := by
  let S := RationalInput.inputLength P x h
  let W := (run P x h).work
  have bound := run_work P x hp coeff
  have count : W.slots ≤ slots S := bound.1
  have operands : W.width ≤ fieldWidth S+3 := bound.2
  have cw := size_le_self (S+1)
  have sw := size_le_self (W.slots+1)
  have ww := size_le_self (W.width+1)
  have combined : max W.width (addressWidth S W.slots W.width)+1 ≤ S+slots S+3*(fieldWidth S+3)+16 := by
    unfold addressWidth
    omega
  exact Nat.mul_le_mul count (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left combined 3))

end Kintali.LinearProgramming.OutputEncoding
