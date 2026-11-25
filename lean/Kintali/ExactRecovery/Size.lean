module

public import Kintali.ExactRecovery.Matrix
public import Kintali.ExactRecovery.Grid
public import Kintali.LinearProgramming.Bounds

/-! # Binary length and row count of Lemma 2's pattern systems -/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery

open StochasticGames.BinarySize Kintali.LinearProgramming

variable {I J : Type*} [Fintype I] [Fintype J]

theorem row_count : Fintype.card (Row I J) =
    4 * Fintype.card I * Fintype.card J + 6 * Fintype.card J + 2 * Fintype.card I + 5 := by
  rw [← Fintype.card_congr (Row.proxyTypeEquiv I J)]
  simp [Fintype.card_sigma]
  ring

/-- Sum of the reduced numerator and denominator lengths, counting each
distinct table entry once; repeated inputs can only increase the full encoding. -/
def tableBits (g : Game I J) : ℕ := ∑ a ∈ data g, (a.num.natAbs.size + a.den.size)

theorem denominator_size (g : Game I J) : (denominator g).size ≤ 1 + tableBits g := by
  apply (System.prod_size_le (data g) Rat.den).trans
  exact Nat.add_le_add_left (Finset.sum_le_sum (fun a _ => Nat.le_add_left ..)) _

theorem magnitude_size (g : Game I J) : (magnitude g).size ≤ tableBits g := by
  have one : (1 : ℚ) ∈ data g := by simp [data]
  have pos : 1 ≤ (data g).sup (fun a : ℚ => a.num.natAbs) :=
    Finset.le_sup (f := fun r : ℚ => r.num.natAbs) one
  obtain ⟨a,ha,eq⟩ := Finset.sup_mem_of_nonempty (f := fun r : ℚ => r.num.natAbs) ⟨1,one⟩
  rw [magnitude, max_eq_right pos, ← eq]
  exact (Nat.le_add_right ..).trans (Finset.single_le_sum
    (f := fun r : ℚ => r.num.natAbs.size + r.den.size) (fun _ _ => Nat.zero_le _) ha)

/-- Writing H requires O(n(log n + table bits)) bits. Both the coefficients
and the right-hand sides use the same polynomial-size integer scaling. -/
theorem height_size (g : Game I J) :
    let n := Fintype.card (Variable I J)
    (height g).size ≤ 1 + n * (n.size + 3 + 2 * tableBits g) := by
  let n := Fintype.card (Variable I J)
  have bound : (n * (2 * denominator g * magnitude g)).size ≤ n.size + 3 + 2 * tableBits g := by
    have a := size_mul_le n (2 * denominator g * magnitude g)
    have b := size_mul_le (2 * denominator g) (magnitude g)
    have c := size_mul_le 2 (denominator g)
    have d := denominator_size g
    have m := magnitude_size g
    have two : (2 : ℕ).size = 2 := rfl
    omega
  exact (power_size_le _ n).trans (Nat.add_le_add_left (Nat.mul_le_mul_left n bound) _)

theorem datum_abs_le_magnitude (g : Game I J) {a : ℚ} (ha : a ∈ data g) :
    |a| ≤ (magnitude g : ℚ) := by
  have bound : |(scaled g a : ℚ)| ≤ (atomBound g : ℚ) := by exact_mod_cast scaled_abs_le g ha
  have pos : (0 : ℚ) < denominator g := by exact_mod_cast denominator_pos g
  rw [scaled_cast g ha, abs_mul, abs_of_pos pos] at bound
  apply (mul_le_mul_iff_right₀ pos).mp
  simpa [atomBound, mul_comm] using bound

theorem maxSiteSlope_bound (g : Game I J) : maxSiteSlope g ≤ (magnitude g : ℚ) := by
  apply Finset.max'_le
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | included
  · exact Nat.cast_nonneg _
  · obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp included
    exact (le_abs_self _).trans (datum_abs_le_magnitude g (slope_mem g i j))

/-- If 1/B ≤ η, a grid built by the paper's ceiling has at most MB gaps.
Its explicit binary index length is polynomial even when that count is large. -/
theorem gridSize_bound (g : Game I J) {η : ℚ} {B : ℕ} (positive : 0 < B)
    (tolerance : 1 / (B : ℚ) ≤ η) : gridSize g η ≤ magnitude g * B := by
  have bp : (0 : ℚ) < B := by exact_mod_cast positive
  have ep : 0 < η := (one_div_pos.mpr bp).trans_le tolerance
  have mult : (1 : ℚ) ≤ η * B := (div_le_iff₀ bp).mp tolerance
  have scaled := mul_le_mul_of_nonneg_left mult (Nat.cast_nonneg (magnitude g) : (0 : ℚ) ≤ magnitude g)
  apply max_le (Nat.mul_pos (magnitude_pos g) positive) (Nat.ceil_le.mpr _)
  apply (div_le_iff₀ ep).mpr
  push_cast
  exact (maxSiteSlope_bound g).trans (by linarith)

theorem gridSize_size (g : Game I J) {η : ℚ} {B : ℕ} (positive : 0 < B)
    (tolerance : 1 / (B : ℚ) ≤ η) : (gridSize g η).size ≤ tableBits g + B.size :=
  ((Nat.size_le_size (gridSize_bound g positive tolerance)).trans (size_mul_le _ _)).trans
    (Nat.add_le_add_right (magnitude_size g) _)

end Kintali.ExactRecovery
