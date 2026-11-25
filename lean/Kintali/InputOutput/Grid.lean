module

public import Kintali.InputOutput.Bounds
public import Kintali.MarketTrial
public import Kintali.LinearProgramming.RationalBounds

/-! # Quote-grid indices have polynomial length in the public binary input -/

@[expose] public section

namespace Kintali.InputOutput.Binary

open ExactRecovery LinearProgramming StochasticGames.BinarySize

/-- A uniform bound for the number of rows, number of columns and coefficient
bit length supplied to the exact repair system. -/
def repairBound (L : ℕ) : ℕ :=
  exactRows L L + exactVars L L + 3 + 2 * ((2 + L + L + L * L + L * L) * (4 * L + 2))

private theorem repair_bounds (a : Input) (h : a.Valid) :
    let U := repairBound (lengthInput a)
    exactRows a.types a.targets ≤ U ∧ exactVars a.types a.targets ≤ U ∧
      (coefficientHeight a.game).size ≤ U ∧ tableBits a.game ≤ U := by
  let L := lengthInput a
  have dims := dimensions a
  have r : exactRows a.types a.targets ≤ exactRows L L := by
    unfold exactRows
    gcongr <;> first | exact dims.1 | exact dims.2.1
  have v : exactVars a.types a.targets ≤ exactVars L L := by
    unfold exactVars
    gcongr <;> first | exact dims.1 | exact dims.2.1
  have sizes := tableBits_bound a h
  have d := denominator_size a.game
  have m := magnitude_size a.game
  have eq : coefficientHeight a.game = 2 * (magnitude a.game * denominator a.game) := by
    simp [coefficientHeight, atomBound, Int.natAbs_mul]
  have two : (2 : ℕ).size = 2 := rfl
  have u := size_mul_le 2 (magnitude a.game * denominator a.game)
  have w := size_mul_le (magnitude a.game) (denominator a.game)
  rw [two, ← eq] at u
  dsimp only [repairBound]
  dsimp only [L] at r v
  omega

/-- An input of L bits has quote indices of at most this many bits; all
operations in this expression are fixed polynomial operations on L. -/
def gridBitBound (L : ℕ) : ℕ :=
  let U := repairBound L
  U + 3 + (1 + U * (U + 3 + 2 * U)) + 16 * (U + 2) ^ 3

theorem grid_size (a : Input) (h : a.Valid) :
    (MarketTrial.grid a.game).size ≤ gridBitBound (lengthInput a) := by
  let g := a.game
  let U := repairBound (lengthInput a)
  obtain ⟨hr, hv, hc, ht⟩ := repair_bounds a h
  let D := SlackWindow.divisor (exactRows a.types a.targets) (exactVars a.types a.targets) (coefficientHeight g)
  let H := ExactRecovery.height g
  let B := max (4 * H) D
  have hH : 0 < H := height_pos g
  have hD : 0 < D := SlackWindow.divisor_pos _ _ (coefficientHeight_pos g)
  have hB : 0 < B := hD.trans_le (le_max_right ..)
  have tol : 1 / (B : ℚ) ≤ contactTolerance g := by
    apply le_min
    · unfold eta
      have hp : (0 : ℚ) < 4 * (H : ℚ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 4) hH
      exact one_div_le_one_div_of_le hp (by exact_mod_cast le_max_left (4*H) D)
    · exact one_div_le_one_div_of_le (by exact_mod_cast hD : (0 : ℚ) < (D : ℚ))
        (by exact_mod_cast le_max_right (4*H) D)
  have ds : D.size ≤ 16 * (U + 2)^3 := SlackWindow.divisor_size_polynomial hr hv hc
  have vn : Fintype.card (Variable (Fin a.types) (Fin a.targets)) = exactVars a.types a.targets := by
    simp [exactVars]
  have hs : H.size ≤ 1 + U * (U + 3 + 2 * U) := by
    have hh := height_size g
    dsimp only at hh
    rw [vn] at hh
    exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul hv
      (Nat.add_le_add (Nat.add_le_add_right ((size_le_self _).trans hv) _)
        (Nat.mul_le_mul_left _ ht))) _)
  have fs : (4*H).size ≤ 3 + H.size := size_mul_le 4 H
  have bs : B.size ≤ 3 + (1 + U * (U + 3 + 2 * U)) + 16 * (U+2)^3 := by
    rcases le_total (4*H) D with hp | hp
    · rw [show B = D from max_eq_right hp]
      omega
    · rw [show B = 4*H from max_eq_left hp]
      omega
  have gs := gridSize_size g hB tol
  change (gridSize g (contactTolerance g)).size ≤ U + 3 + (1+U*(U+3+2*U)) + 16*(U+2)^3
  change tableBits g ≤ U at ht
  omega

end Kintali.InputOutput.Binary
