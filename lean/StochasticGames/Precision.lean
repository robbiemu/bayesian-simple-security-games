module

public import StochasticGames.ShiftedComparisons
public import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! ## Clear denominators and choose a fold depth -/

public section

namespace StochasticGames
namespace Precision

/-- A scale clears a rational constant when the scaled value is an integer. -/
def Clears (D : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, (D : ℚ) * q = (z : ℚ)

theorem Clears.zero (D : ℕ) : Clears D 0 := ⟨0, by simp⟩

theorem Clears.one (D : ℕ) : Clears D 1 := ⟨D, by simp⟩

theorem Clears.add {D : ℕ} {a b : ℚ} (ha : Clears D a) (hb : Clears D b) :
    Clears D (a + b) := by
  obtain ⟨p, pEq⟩ := ha
  obtain ⟨q, qEq⟩ := hb
  exact ⟨p + q, by rw [mul_add, pEq, qEq, Int.cast_add]⟩

theorem Clears.sub {D : ℕ} {a b : ℚ} (ha : Clears D a) (hb : Clears D b) :
    Clears D (a - b) := by
  obtain ⟨p, pEq⟩ := ha
  obtain ⟨q, qEq⟩ := hb
  exact ⟨p - q, by rw [mul_sub, pEq, qEq, Int.cast_sub]⟩

/-- A single integer scale computed from the literal input constants. -/
def denominator (constants : List ℚ) : ℕ :=
  (constants.map Rat.den).prod

theorem denominator_pos (constants : List ℚ) : 0 < denominator constants := by
  induction constants with
  | nil => decide
  | cons head tail ih =>
      exact Nat.mul_pos head.den_pos ih

private theorem divides_denominator {q : ℚ} {constants : List ℚ} (member : q ∈ constants) :
    q.den ∣ denominator constants := by
  induction constants with
  | nil => simp at member
  | cons head tail ih =>
      change q.den ∣ head.den * denominator tail
      rcases List.mem_cons.mp member with equals | inTail
      · subst head
        exact dvd_mul_right _ _
      · exact dvd_mul_of_dvd_right (ih inTail) _

theorem denominator_clears {q : ℚ} {constants : List ℚ} (member : q ∈ constants) :
    Clears (denominator constants) q := by
  obtain ⟨k, factorization⟩ := divides_denominator member
  refine ⟨q.num * (k : ℤ), ?_⟩
  rw [factorization, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  calc
    (q.den : ℚ) * (k : ℚ) * q = (q * (q.den : ℚ)) * (k : ℚ) := by ring
    _ = (q.num : ℚ) * (k : ℚ) := by rw [q.mul_den_eq_num]

/-- Use the binary length of the rounded ratio to choose the comparison depth. -/
def rounds (width gap : ℚ) : ℕ :=
  (Int.toNat ⌈width / (2 * gap)⌉).size

theorem error_lt_gap {width gap : ℚ} (widthNonneg : 0 ≤ width) (gapPos : 0 < gap) :
    ShiftedComparisons.gapBound width (rounds width gap) / 2 < gap := by
  let ratio := width / (2 * gap)
  have scalePos : 0 < 2 * gap := mul_pos (by norm_num) gapPos
  have ratioNonneg : 0 ≤ ratio := div_nonneg widthNonneg scalePos.le
  have ceilingNonneg : 0 ≤ ⌈ratio⌉ := by
    exact_mod_cast (ratioNonneg.trans (Int.le_ceil ratio))
  have ceilingEq : (Int.toNat ⌈ratio⌉ : ℚ) = (⌈ratio⌉ : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg ceilingNonneg
  have natStrict : Int.toNat ⌈ratio⌉ < 2 ^ rounds width gap :=
    Nat.size_le.mp le_rfl
  have rationalStrict : (Int.toNat ⌈ratio⌉ : ℚ) < (2 : ℚ) ^ rounds width gap := by
    exact_mod_cast natStrict
  have strict : ratio < (2 : ℚ) ^ rounds width gap :=
    (Int.le_ceil ratio).trans_lt (by simpa only [ceilingEq] using rationalStrict)
  have product := (div_lt_iff₀ scalePos).1 strict
  rw [ShiftedComparisons.gapBound_eq, div_div]
  have divisorPos : 0 < (2 : ℚ) ^ rounds width gap * 2 :=
    mul_pos (pow_pos (by norm_num) _) (by norm_num)
  apply (div_lt_iff₀ divisorPos).2
  exact product.trans_eq (by ring)

end Precision
end StochasticGames
