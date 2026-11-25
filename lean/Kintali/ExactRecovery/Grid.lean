module

public import Kintali.ExactRecovery.Scale
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Quote grid and private mass

Quote z/G has G−z private gaps above it. The next quote strictly above x<1 is
(floor(Gx)+1)/G even when x is exactly on a grid point.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery

abbrev Quote (G : ℕ) := Fin (G + 1)

def price {G : ℕ} (z : Quote G) : ℚ := (z.val : ℚ) / G

def cap (G : ℕ) : Quote G := Fin.last G

theorem cap_price {G : ℕ} (hG : 0 < G) : price (cap G) = 1 := by
  simpa [price, cap] using div_self (by exact_mod_cast hG.ne' : (G : ℚ) ≠ 0)

/-- The minimum with G makes the function total, including at x=1. -/
def nextQuote (G : ℕ) (x : ℚ) : Quote G :=
  ⟨min G (⌊(G : ℚ) * x⌋₊ + 1), by omega⟩

theorem nextQuote_bounds {G : ℕ} (hG : 0 < G) {x : ℚ} (hx : 0 ≤ x) (hlt : x < 1) :
    x < price (nextQuote G x) ∧ price (nextQuote G x) ≤ x + 1 / G := by
  have gp : (0 : ℚ) < G := by exact_mod_cast hG
  have nn := mul_nonneg gp.le hx
  have floorBound : ⌊(G : ℚ) * x⌋₊ < G := (Nat.floor_lt nn).mpr
    (by simpa using mul_lt_mul_of_pos_left hlt gp)
  change x < ((min G (⌊(G : ℚ) * x⌋₊ + 1) : ℕ) : ℚ) / G ∧
    ((min G (⌊(G : ℚ) * x⌋₊ + 1) : ℕ) : ℚ) / G ≤ x + 1 / G
  rw [min_eq_right (by omega), Nat.cast_add, Nat.cast_one, lt_div_iff₀ gp, div_le_iff₀ gp,
    add_mul, div_mul_cancel₀ _ gp.ne']
  constructor
  · simpa only [mul_comm] using Nat.lt_floor_add_one ((G : ℚ) * x)
  · linarith [Nat.floor_le nn, mul_comm (G : ℚ) x]

theorem nextQuote_first {G : ℕ} (hG : 0 < G) {x : ℚ} (hx : 0 ≤ x)
    {z : Quote G} (hz : x < price z) : nextQuote G x ≤ z := by
  have gp : (0 : ℚ) < G := by exact_mod_cast hG
  have floorBound : ⌊(G : ℚ) * x⌋₊ < z.val := (Nat.floor_lt (mul_nonneg gp.le hx)).mpr
    (by simpa only [mul_comm] using (lt_div_iff₀ gp).mp hz)
  change min G (⌊(G : ℚ) * x⌋₊ + 1) ≤ z.val
  exact (min_le_right ..).trans floorBound

theorem gap_mass {G : ℕ} (hG : 0 < G) (σ : ℚ) : (∑ _ : Fin G, σ / G) = σ := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [Nat.ne_of_gt hG]

theorem mass_above_price {G : ℕ} (hG : 0 < G) (σ : ℚ) (z : Quote G) :
    (∑ k : Fin G, if z.val ≤ k.val then σ / G else 0) = σ * (1 - price z) := by
  classical
  have count : (Finset.univ.filter (fun k : Fin G => z.val ≤ k.val)).card = G - z.val := by
    by_cases hz : z.val < G
    · let a : Fin G := ⟨z.val,hz⟩
      have eq : Finset.univ.filter (fun k : Fin G => z.val ≤ k.val) = Finset.Ici a := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
        rfl
      rw [eq, Fin.card_Ici]
    · have high : ∀ k : Fin G, ¬z.val ≤ k.val := fun k h => hz (h.trans_lt k.isLt)
      simp [high, Nat.sub_eq_zero_of_le (by omega : G ≤ z.val)]
  rw [← Finset.sum_filter, Finset.sum_const, count, nsmul_eq_mul, Nat.cast_sub (by omega : z.val ≤ G)]
  unfold price
  field_simp [Nat.ne_of_gt hG]

variable {I J : Type*} [Fintype I] [Fintype J]

def siteSlopes (g : Game I J) : Finset ℚ :=
  insert 0 ((Finset.univ.filter fun a : I × J => 0 < g.gain a.2).image
    fun a => g.slope a.1 a.2)

def maxSiteSlope (g : Game I J) : ℚ := (siteSlopes g).max' (Finset.insert_nonempty ..)

def maxGain (g : Game I J) : ℚ :=
  (insert 0 (Finset.univ.image g.gain)).max' (Finset.insert_nonempty ..)

def eta (g : Game I J) : ℚ := 1 / (4 * (height g : ℚ))
def sigma (g : Game I J) (η : ℚ) : ℚ := η / max 1 (maxGain g)
def gridSize (g : Game I J) (η : ℚ) : ℕ := max 1 ⌈maxSiteSlope g / η⌉₊

theorem eta_bounds (g : Game I J) : 0 < eta g ∧ eta g < 1 / (height g : ℚ) ∧ eta g ≤ 1 := by
  have hp : (0 : ℚ) < height g := by exact_mod_cast height_pos g
  have ho : (1 : ℚ) ≤ height g := by exact_mod_cast height_pos g
  refine ⟨div_pos (by norm_num) (mul_pos (by norm_num) hp), ?_, ?_⟩
  · exact one_div_lt_one_div_of_lt hp (by linarith)
  · unfold eta
    apply (div_le_iff₀ (mul_pos (by norm_num) hp)).mpr
    linarith

omit [Fintype I] in
theorem sigma_pos (g : Game I J) {η : ℚ} (he : 0 < η) : 0 < sigma g η :=
  div_pos he (lt_of_lt_of_le zero_lt_one (le_max_left ..))

omit [Fintype I] in
theorem gain_sigma_le (g : Game I J) {η : ℚ} (he : 0 ≤ η) (j : J) :
    g.gain j * sigma g η ≤ η := by
  have member : g.gain j ∈ insert 0 (Finset.univ.image g.gain) :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have bound := (Finset.le_max' _ _ member).trans (le_max_right (1 : ℚ) (maxGain g))
  unfold sigma
  rw [← mul_div_assoc, div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left ..))]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right bound he

theorem gridSize_pos (g : Game I J) (η : ℚ) : 0 < gridSize g η :=
  lt_of_lt_of_le (by decide : 0 < 1) (le_max_left ..)

theorem slope_step_le (g : Game I J) {η : ℚ} (he : 0 < η) (i : I) (j : J)
    (site : 0 < g.gain j) : g.slope i j / gridSize g η ≤ η := by
  have hm : g.slope i j ∈ siteSlopes g := Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem (fun a : I × J => g.slope a.1 a.2)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i,j), site⟩))
  have ceilLe : (⌈maxSiteSlope g / η⌉₊ : ℚ) ≤ gridSize g η := by
    exact_mod_cast (le_max_right 1 ⌈maxSiteSlope g / η⌉₊)
  have maxLe := (div_le_iff₀ he).mp ((Nat.le_ceil _).trans ceilLe)
  apply (div_le_iff₀ (by exact_mod_cast gridSize_pos g η : (0 : ℚ) < gridSize g η)).mpr
  exact (Finset.le_max' _ _ hm).trans (maxLe.trans_eq (mul_comm ..))

end Kintali.ExactRecovery
