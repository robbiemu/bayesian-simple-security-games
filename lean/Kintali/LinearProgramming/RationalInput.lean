module

public import Kintali.LinearProgramming.PointEncoding

/-! # Recovery from individually encoded rational coordinates

This interface counts directly from the stored input fields. Its returned
signed integer ratios may be decoded as rationals with `Answer.value`.
-/

@[expose] public section

namespace Kintali.LinearProgramming.RationalInput

open StochasticGames.CompilerRun StochasticGames.BinarySize PivotRun PointRun RecoveryRun

variable {m n : ℕ}

def integerBits (a : ℤ) := a.natAbs.size + 1

def inputLength (P : Input m n) (x : Vector ℚ n) (h : ℕ) : ℕ :=
  m+n+3+h.size +
    (∑ i : Fin m, (integerBits (P.system.rhs i) + ∑ j : Fin n, integerBits (P.system.coeff i j))) +
    ∑ j : Fin n, (integerBits x[j.val].num + x[j.val].den.size + 1)

def run (P : Input m n) (x : Vector ℚ n) (h : ℕ) : Run (CramerRun.Answer n) := do
  let X ← PointEncoding.encode x
  RecoveryRun.run P X h

theorem run_value (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h) :
    (run P x h).value.value = P.system.recover h (PointEncoding.input x) := by
  simp only [run, Run.bind_value, RecoveryRun.run_value P _ h hp, PointEncoding.encode_point]

theorem run_feasible (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ))
    (approximate : ∀ i, -SlackWindow.precision m n h ≤ P.system.slack (PointEncoding.input x) i) :
    P.system.Feasible (run P x h).value.value := by
  rw [run_value P x hp]
  exact P.system.recover_feasible h _ hp coeff approximate

def slotLimit (S : ℕ) := 16*(S+2) + transitionLimit (PointEncoding.wordLimit S)

def widthLimit (S : ℕ) := operandLimit (PointEncoding.wordLimit S)

theorem run_work (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) :
    (run P x h).Bound (slotLimit (inputLength P x h)) (widthLimit (inputLength P x h)) := by
  let S := inputLength P x h
  let T := PointEncoding.wordLimit S
  let X := (PointEncoding.encode x).value
  let U := 2^(S+1+n*S)
  let B := 2^S
  let M := ∑ i : Fin m, (integerBits (P.system.rhs i) + ∑ j : Fin n, integerBits (P.system.coeff i j))
  let V := ∑ j : Fin n, (integerBits x[j.val].num + x[j.val].den.size+1)
  have form : S = m+n+3+h.size+M+V := rfl
  have rows : m+2 ≤ S := by omega
  have cols : n+1 ≤ S := by omega
  have hs : h.size ≤ S := by omega
  have entry (j : Fin n) : integerBits x[j.val].num + x[j.val].den.size + 1 ≤ V :=
    Finset.single_le_sum (f := fun j : Fin n => integerBits x[j.val].num+x[j.val].den.size+1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have nums (j : Fin n) : x[j.val].num.natAbs.size ≤ S := by
    have ej := entry j
    unfold integerBits at ej
    omega
  have dens (j : Fin n) : x[j.val].den.size ≤ S := by
    have ej := entry j
    omega
  have bs (i : Fin m) : (P.system.rhs i).natAbs.size ≤ S := by
    have ri : integerBits (P.system.rhs i) + ∑ j : Fin n, integerBits (P.system.coeff i j) ≤ M :=
      Finset.single_le_sum (f := fun i : Fin m => integerBits (P.system.rhs i) + ∑ j : Fin n, integerBits (P.system.coeff i j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    unfold integerBits at ri
    omega
  have rhs (i : Fin m) : |P.system.rhs i| ≤ (B : ℤ) := by
    rw [← Int.natCast_natAbs, Nat.cast_le]
    exact (Nat.size_le.mp (bs i)).le
  have encoded : X.scaled = ScaledPoint.encode (PointEncoding.input x) := PointEncoding.encode_value x
  have denSize : X.den.size ≤ 1+n*S := by
    have le := PointEncoding.product_size x (List.finRange n) dens
    rw [PointEncoding.denominator_value, List.length_finRange] at le
    change X.scaled.den.size ≤ _
    rw [encoded]
    exact le
  have uBound (j : Fin n) : |X.scaled.num j| ≤ (U : ℤ) := by
    rw [← Int.natCast_natAbs, Nat.cast_le]
    apply Nat.le_of_lt
    apply Nat.size_le.mp
    have enc := ScaledPoint.encoded_num_size (PointEncoding.input x) j
    rw [← encoded] at enc
    have d : (ScaledPoint.denominator (PointEncoding.input x)).size = X.den.size := by
      change (ScaledPoint.encode (PointEncoding.input x)).den.size = X.scaled.den.size
      rw [encoded]
    rw [d] at enc
    have nbit : (PointEncoding.input x j).num.natAbs.size ≤ S := nums j
    omega
  have nn := Nat.mul_le_mul_right S (by omega : n ≤ S)
  have tfit : S+2+n*S ≤ T := by
    dsimp [T,PointEncoding.wordLimit]
    ring_nf at nn ⊢
    omega
  have fit : InputBits m n h B U X.den T := by
    have BB : B.size = S+1 := Nat.size_pow
    have UU : U.size = (S+1+n*S)+1 := Nat.size_pow
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩
  have encode := PointEncoding.encode_work x (by omega : n ≤ S) nums dens
  have recover := RecoveryRun.run_work P X hp coeff rhs uBound fit
  have fold : T ≤ widthLimit S := by
    change T ≤ 64*(64*(T+2)^3+2)^2
    ring_nf
    omega
  exact bound_bind (f := fun X => RecoveryRun.run P X h) (encode.weaken le_rfl fold) recover

def binaryLimit (S : ℕ) := slotLimit S * (64*(S+slotLimit S+3*widthLimit S+16)^3)

/-- Addressed binary word work is polynomial in the length of the dense
integer matrix and individually stored rational input point. -/
theorem run_binary_work (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) :
    binaryWork (inputLength P x h) (run P x h).work ≤ binaryLimit (inputLength P x h) := by
  let S := inputLength P x h
  let W := (run P x h).work
  have runBound := run_work P x hp coeff
  have slots : W.slots ≤ slotLimit S := runBound.1
  have operands : W.width ≤ widthLimit S := runBound.2
  have cw := size_le_self (S+1)
  have sw := size_le_self (W.slots+1)
  have ww := size_le_self (W.width+1)
  have combined : max W.width (addressWidth S W.slots W.width)+1 ≤ S+slotLimit S+3*widthLimit S+16 := by
    unfold addressWidth
    omega
  exact Nat.mul_le_mul slots (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left combined 3))

end Kintali.LinearProgramming.RationalInput
