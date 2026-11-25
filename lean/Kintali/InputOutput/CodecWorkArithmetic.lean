module

public import Kintali.InputOutput.Codec
public import StochasticGames.CompilerRun
import Mathlib.Data.Rat.Lemmas

/-! # Reading and reducing a signed rational field

Two Euclidean remainders cut the second argument at least in half. The
reader can therefore start with one iteration per denominator bit. Division
and remainder are addressed binary word operations.
-/

@[expose] public section

namespace Kintali.InputOutput.CodecWork
open StochasticGames.CompilerRun StochasticGames.BinarySize

/-- A pair of Euclidean steps. Zero fuel returns the first argument. -/
def gcdRun : ℕ → ℕ → ℕ → Run ℕ
  | 0, a, _ => step 0 a
  | k+1, a, b => do
    let _ ← step (k+1).size k
    let stop ← step b.size (b == 0)
    if stop then step 0 a else do
      let r ← step (max a.size b.size) (a % b)
      let stop ← step r.size (r == 0)
      if stop then step 0 b else do
        let s ← step (max b.size r.size) (b % r)
        gcdRun k r s

private theorem twice_mod_le {b r : ℕ} (hr : 0 < r) (h : r ≤ b) : 2*(b%r) ≤ b := by
  have t := Nat.mod_lt b hr
  have small : b % r ≤ b-r := by
    rw [Nat.mod_eq_sub_mod h]
    exact Nat.mod_le _ _
  omega

theorem gcdRun_value (k a b : ℕ) (h : b < 2^k) : (gcdRun k a b).value = a.gcd b := by
  induction k generalizing a b with
  | zero =>
    have : b = 0 := by simpa using h
    subst b
    simp [gcdRun]
  | succ k ih =>
    by_cases hb : b = 0
    · subst b; simp [gcdRun]
    by_cases hr : a % b = 0
    · simp [gcdRun,hb,hr, Nat.gcd_rec b a, Nat.gcd_comm a b]
    have small := twice_mod_le (Nat.pos_of_ne_zero hr) (Nat.mod_lt a (Nat.pos_of_ne_zero hb)).le
    have h' : b % (a%b) < 2^k := by rw [pow_succ] at h; omega
    simp only [gcdRun,Run.bind_value,step_value,beq_iff_eq, hb, hr, ite_false, ih _ _ h']
    calc
      _ = (b%(a%b)).gcd (a%b) := Nat.gcd_comm _ _
      _ = (a%b).gcd b := Nat.gcd_rec _ _ |>.symm
      _ = b.gcd a := Nat.gcd_rec _ _ |>.symm
      _ = a.gcd b := Nat.gcd_comm _ _

theorem gcdRun_work (k a b W : ℕ) (hk : k ≤ W) (ha : a.size ≤ W) (hb : b.size ≤ W) :
    (gcdRun k a b).Bound (5*k+1) W := by
  induction k generalizing a b with
  | zero => exact (bound_step _ _).weaken le_rfl (Nat.zero_le _)
  | succ k ih =>
    have counter := (size_le_self (k+1)).trans hk
    have hr := (Nat.size_le_size (Nat.mod_le a b)).trans ha
    have hs := (Nat.size_le_size (Nat.mod_le b (a%b))).trans hb
    have tail := ih (a%b) (b%(a%b)) (by omega) hr hs
    by_cases bz : b = 0 <;> by_cases rz : a%b = 0 <;>
      simp [gcdRun,Run.Bound,bz,rz] at tail ⊢ <;> omega

/-- Compute the reduced pair. The proofs carried by Rat reuse the computed
gcd result. They are erased by Lean. -/
def reduce (z : ℤ) (d : ℕ) : Run ℚ :=
  let width := max z.natAbs.size d.size + 2
  if hz : d = 0 then step width 0 else
    let g := gcdRun d.size z.natAbs d
    let h := gcdRun_value d.size z.natAbs d (Nat.lt_size_self d)
    let n := step (max z.natAbs.size g.value.size + 2) (z / (g.value : ℤ))
    let den := step (max d.size g.value.size + 2) (d / g.value)
    let q : ℚ := ⟨n.value, den.value, by
                    change d / g.value ≠ 0
                    rw [h]
                    exact Rat.normalize.den_nz hz rfl,
                  by
                    change (z / (g.value : ℤ)).natAbs.Coprime (d / g.value)
                    rw [h]
                    exact Rat.normalize.reduced hz rfl⟩
    -- Read the sign/magnitude and bit length, test the denominator, divide
    -- each field and allocate the reduced pair.
    ⟨q, (Work.one width).seq ((Work.one width).seq ((Work.one width).seq
       (g.work.seq (n.work.seq (den.work.seq (Work.one 0))))))⟩

theorem reduce_value (z : ℤ) (d : ℕ) : (reduce z d).value = (z : ℚ) / d := by
  by_cases hd : d = 0
  · subst d; simp [reduce]
  simp only [reduce, dite_eq_right hd,step_value,gcdRun_value _ _ _ (Nat.lt_size_self d)]
  rw [← Rat.mkRat_eq_div, ← Rat.normalize_eq_mkRat hd, Rat.normalize_eq]

theorem reduce_work (z : ℤ) (d : ℕ) {W : ℕ} (hz : z.natAbs.size ≤ W) (hd : d.size ≤ W) :
    (reduce z d).Bound (5*W+7) (W+2) := by
  have h := gcdRun_work d.size z.natAbs d W hd hz hd
  by_cases hd' : d = 0
  · simp only [reduce,hd',dite_true,Run.Bound,step_slots,step_width] at *
    omega
  have divisor := (Nat.size_le_size (Nat.gcd_le_right z.natAbs (Nat.pos_of_ne_zero hd'))).trans hd
  simp only [reduce,dite_eq_right hd',Run.Bound,Work.seq,Work.one,step_slots,step_width,
    gcdRun_value _ _ _ (Nat.lt_size_self d)] at *
  omega

end Kintali.InputOutput.CodecWork
