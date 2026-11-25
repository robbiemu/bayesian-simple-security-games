module

public import Kintali.LinearProgramming.BasisSearch
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Binary length of a feasible basis solution

Both determinants in a Cramer coordinate have magnitude at most `n! * h^n`
when the integer coefficients and right-hand sides have magnitude at most `h`.
Reduction to lowest terms preserves the bounds.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open StochasticGames

def minorBound (n h : ℕ) : ℕ := n.factorial * h ^ n

theorem minorBound_pos {h : ℕ} (n : ℕ) (positive : 0 < h) : 0 < minorBound n h :=
  Nat.mul_pos n.factorial_pos (Nat.pow_pos positive)

theorem power_size_le (a n : ℕ) : (a ^ n).size ≤ 1 + n * a.size := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    have h := BinarySize.size_mul_le (a ^ n) a
    omega

theorem minorBound_size (n h : ℕ) :
    (minorBound n h).size ≤ 1 + n * (n.size + h.size) := by
  have bound : minorBound n h ≤ (n * h) ^ n := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ n.factorial_le_pow
  exact ((Nat.size_le_size bound).trans (power_size_le _ _)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left n (BinarySize.size_mul_le n h)) _)

theorem determinant_natAbs_le {n h : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (entries : ∀ i j, |M i j| ≤ (h : ℤ)) : (determinant M).natAbs ≤ minorBound n h := by
  have bound := DeterminantGap.det_abs_le_of_entries M (h : ℤ) entries
  rw [determinant_eq]
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  simpa [minorBound] using bound

theorem divInt_parts_le (p d : ℤ) (hd : d ≠ 0) :
    (Rat.divInt p d).num.natAbs ≤ p.natAbs ∧ (Rat.divInt p d).den ≤ d.natAbs := by
  let q := Rat.divInt p d
  obtain ⟨c, hc, hd'⟩ := Rat.num_den_mk (q := q) hd rfl
  have hc0 : c ≠ 0 := by
    intro zero
    exact hd (by simpa [zero] using hd')
  have pos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
  have num := congrArg Int.natAbs hc
  have den := congrArg Int.natAbs hd'
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at num den
  change q.num.natAbs ≤ _ ∧ q.den ≤ _
  exact ⟨num ▸ Nat.le_mul_of_pos_left _ pos, den ▸ Nat.le_mul_of_pos_left _ pos⟩

namespace System

variable {m n : ℕ} (P : System (Fin m) (Fin n))

/-- A bound on the signed magnitude of every stored integer. -/
def HeightAtMost (h : ℕ) : Prop :=
  (∀ i j, |P.coeff i j| ≤ (h : ℤ)) ∧ (∀ i, |P.rhs i| ≤ (h : ℤ))

theorem solve_coordinate_size {x : Fin n → ℚ} {h : ℕ}
    (hit : P.solve = some x) (height : P.HeightAtMost h) (j : Fin n) :
    (x j).num.natAbs.size ≤ 1 + n * (n.size + h.size) ∧
    (x j).den.size ≤ 1 + n * (n.size + h.size) := by
  obtain ⟨rows, _, accepted⟩ := List.exists_of_findSome?_eq_some hit
  obtain ⟨nonzero, _, rfl⟩ := P.checkedBasis_spec accepted
  let M := P.basisMatrix rows
  let num := determinant (M.updateCol j (P.rhs ∘ rows))
  let den := determinant M
  have denBound : den.natAbs ≤ minorBound n h :=
    determinant_natAbs_le M (fun i k => height.1 (rows i) k)
  have numBound : num.natAbs ≤ minorBound n h := by
    apply determinant_natAbs_le
    intro i k
    rw [Matrix.updateCol_apply]
    split
    · exact height.2 (rows i)
    · exact height.1 (rows i) k
  have bounds := divInt_parts_le num den nonzero
  exact ⟨(Nat.size_le_size (bounds.1.trans numBound)).trans (minorBound_size ..),
    (Nat.size_le_size (bounds.2.trans denBound)).trans (minorBound_size ..)⟩

end System

end Kintali.LinearProgramming
