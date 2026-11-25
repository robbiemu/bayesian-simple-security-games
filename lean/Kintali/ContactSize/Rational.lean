module

public import Kintali.LinearProgramming.Bounds
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Positivity

/-! Binary sizes of reduced rational coordinates and finite sums. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.ContactSize

open StochasticGames.BinarySize

/-- Both unsigned magnitudes in the reduced representation fit in `w` bits. -/
def Fits (w : ℕ) (q : ℚ) := q.num.natAbs.size ≤ w ∧ q.den.size ≤ w

namespace Fits

theorem mono {a b : ℕ} {q : ℚ} (h : Fits a q) (le : a ≤ b) : Fits b q :=
  ⟨h.1.trans le, h.2.trans le⟩

theorem pos {w : ℕ} {q : ℚ} (h : Fits w q) : 1 ≤ w :=
  (Nat.size_le_size (show 1 ≤ q.den from q.den_pos)).trans h.2

theorem zero : Fits 1 0 := by unfold Fits; decide
theorem one : Fits 1 1 := by unfold Fits; decide

theorem natCast (n : ℕ) : Fits (n.size + 1) (n : ℚ) := by
  simp [Fits]

theorem inv {a : ℕ} {q : ℚ} (h : Fits a q) : Fits a q⁻¹ := by
  by_cases hn : q.num = 0
  · rw [Rat.zero_of_num_zero hn, inv_zero]
    exact zero.mono h.pos
  · simpa [Fits, Rat.num_inv, Rat.den_inv, hn, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn,
      and_comm] using h

theorem mul {a b : ℕ} {q r : ℚ} (hq : Fits a q) (hr : Fits b r) : Fits (a+b) (q*r) := by
  have h := LinearProgramming.divInt_parts_le (q.num*r.num) ((q.den*r.den : ℕ) : ℤ)
    (by exact_mod_cast mul_ne_zero q.den_ne_zero r.den_ne_zero)
  rw [Rat.divInt_ofNat, ← Rat.mul_eq_mkRat] at h
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
  exact ⟨(Nat.size_le_size h.1).trans ((size_mul_le ..).trans (Nat.add_le_add hq.1 hr.1)),
    (Nat.size_le_size h.2).trans ((size_mul_le ..).trans (Nat.add_le_add hq.2 hr.2))⟩

theorem div {a b : ℕ} {q r : ℚ} (hq : Fits a q) (hr : Fits b r) : Fits (a+b) (q/r) := by
  rw [div_eq_mul_inv]
  exact hq.mul hr.inv

theorem add {a b : ℕ} {q r : ℚ} (hq : Fits a q) (hr : Fits b r) : Fits (a+b+1) (q+r) := by
  have h := LinearProgramming.divInt_parts_le (q.num*r.den + q.den*r.num) ((q.den : ℤ)*r.den)
    (mul_ne_zero (by exact_mod_cast q.den_ne_zero) (by exact_mod_cast r.den_ne_zero))
  rw [← Rat.add_num_den] at h
  have hn := h.1.trans (Int.natAbs_add_le ..)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn h
  have h₁ := Nat.size_le.mp ((size_mul_le ..).trans (Nat.add_le_add hq.1 hr.2))
  have h₂ := Nat.size_le.mp ((size_mul_le ..).trans (Nat.add_le_add hq.2 hr.1))
  refine ⟨Nat.size_le.mpr ?_, ((Nat.size_le_size h.2).trans ((size_mul_le ..).trans
    (Nat.add_le_add hq.2 hr.2))).trans (Nat.le_succ _)⟩
  rw [pow_succ]
  omega

theorem sum {I : Type*} (s : Finset I) (f : I → ℚ) {w : ℕ}
    (h : ∀ i ∈ s, Fits w (f i)) : Fits (1+s.card*(w+1)) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    have h₁ := h i (Finset.mem_insert_self ..)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact (h₁.add h₂).mono (by rw [Nat.add_mul]; omega)

theorem abs_le {w : ℕ} {q : ℚ} (h : Fits w q) : |q| ≤ ((2^w : ℕ) : ℚ) := by
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hn : q.num.natAbs ≤ 2^w := (Nat.size_le.mp h.1).le
  calc
    |q| ≤ |q| * q.den := le_mul_of_one_le_right (abs_nonneg _) hd
    _ = |(q.num : ℚ)| := by rw [← Rat.mul_den_eq_num q, abs_mul]; simp
    _ ≤ _ := by exact_mod_cast (show |q.num| ≤ (2^w : ℕ) from by
      rw [← Int.natCast_natAbs]; exact_mod_cast hn)

theorem of_den_of_abs {q : ℚ} {d N : ℕ} (hd : q.den ≤ d) (h : |q| ≤ (N : ℚ)) :
    Fits (d.size + N.size) q := by
  have value : |(q.num : ℚ)| ≤ ((N*d : ℕ) : ℚ) := by
    rw [← Rat.mul_den_eq_num q, abs_mul, Nat.cast_mul]
    simp only [abs_of_nonneg (Nat.cast_nonneg q.den : (0:ℚ) ≤ q.den)]
    exact mul_le_mul h (by exact_mod_cast hd) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hn : q.num.natAbs ≤ N*d := by
    have v : |q.num| ≤ ((N*d : ℕ) : ℤ) := by exact_mod_cast value
    exact Int.ofNat_le.mp (by simpa using v)
  exact ⟨((Nat.size_le_size hn).trans (size_mul_le ..)).trans (by omega),
    (Nat.size_le_size hd).trans (Nat.le_add_right ..)⟩

end Fits
end Kintali.ContactSize
