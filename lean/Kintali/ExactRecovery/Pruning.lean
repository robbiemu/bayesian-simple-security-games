module

public import Kintali.ExactRecovery.Grid
public import Kintali.ExactRecovery.Holdings
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Outside and reference minimizers, and the eligible optional prefix

All targets take part in the two minimizations. The eligible optional indices
at an active site are a computable initial segment of 0,…,G−1. A horizontal
cost line is handled separately, including ties with the outside cost.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.ExactRecovery

variable {I J : Type*}

def minimizers [Fintype J] (f : J → ℚ) : Finset J :=
  Finset.univ.filter fun j => ∀ k, f j ≤ f k

theorem minimizers_nonempty [Fintype J] [Nonempty J] (f : J → ℚ) :
    (minimizers f).Nonempty := by
  obtain ⟨j,_,least⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k => least k (Finset.mem_univ _)⟩⟩

def leastMinimum [Fintype J] [Nonempty J] [LinearOrder J] (f : J → ℚ) : J :=
  (minimizers f).min' (minimizers_nonempty f)

theorem leastMinimum_spec [Fintype J] [Nonempty J] [LinearOrder J] (f : J → ℚ) (j : J) :
    f (leastMinimum f) ≤ f j :=
  (Finset.mem_filter.mp ((minimizers f).min'_mem (minimizers_nonempty f))).2 j

theorem leastMinimum_tie [Fintype J] [Nonempty J] [LinearOrder J] {f : J → ℚ} {j : J}
    (tie : f j = f (leastMinimum f)) : leastMinimum f ≤ j :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k =>
    tie.trans_le (leastMinimum_spec f k)⟩)

def outsideTarget [Fintype J] [Nonempty J] [LinearOrder J] (g : Game I J) (i : I) : J :=
  leastMinimum fun j => g.cost i j (Holdings.endpoint g j)

def referenceTarget [Fintype J] [Nonempty J] [LinearOrder J] (g : Game I J) (x : J → ℚ) (i : I) : J :=
  leastMinimum fun j => g.cost i j (x j)

theorem outsideTarget_min [Fintype J] [Nonempty J] [LinearOrder J] (g : Game I J) (i : I) (j : J) :
    Holdings.outsideCost g (outsideTarget g) i ≤ g.cost i j (Holdings.endpoint g j) :=
  leastMinimum_spec (fun k => g.cost i k (Holdings.endpoint g k)) j

theorem referenceTarget_min [Fintype J] [Nonempty J] [LinearOrder J] (g : Game I J)
    (x : J → ℚ) (i : I) (j : J) :
    g.cost i (referenceTarget g x i) (x (referenceTarget g x i)) ≤ g.cost i j (x j) :=
  leastMinimum_spec (fun k => g.cost i k (x k)) j

/-- Number of eligible optional quotes, excluding the permanent cap G.
For positive slope, solve the affine cost inequality and take a floor. -/
def eligibleCount (g : Game I J) (redirect : I → J) (G : ℕ) (i : I) (j : J) : ℕ :=
  if 0 < g.gain j ∧ g.intercept i j ≤ Holdings.outsideCost g redirect i then
    if g.slope i j = 0 then G else
      min G (⌊((Holdings.outsideCost g redirect i - g.intercept i j) * G) / g.slope i j⌋₊ + 1)
  else 0

theorem eligibleCount_le (g : Game I J) (redirect : I → J) (G : ℕ) (i : I) (j : J) :
    eligibleCount g redirect G i j ≤ G := by
  unfold eligibleCount
  split_ifs <;> first | exact le_rfl | exact min_le_left .. | exact Nat.zero_le _

theorem eligible_iff_lt_count (g : Game I J) (redirect : I → J) {G : ℕ} (grid : 0 < G)
    (i : I) (j : J) (nonneg : 0 ≤ g.slope i j) (z : Fin G) :
    Holdings.Eligible g redirect i j z.castSucc ↔ z.val < eligibleCount g redirect G i j := by
  let w := Holdings.outsideCost g redirect i
  let a := g.intercept i j
  let b := g.slope i j
  have gp : (0 : ℚ) < G := by exact_mod_cast grid
  change (0 < g.gain j ∧ a + b * ((z.val : ℚ) / G) ≤ w) ↔ _
  unfold eligibleCount
  by_cases admissible : 0 < g.gain j ∧ a ≤ w
  · rw [ite_eq_left admissible]
    by_cases flat : b = 0
    · simp only [show g.slope i j = 0 from flat, ↓reduceIte, flat, zero_mul, add_zero,
        admissible.1, true_and]
      exact iff_of_true admissible.2 z.isLt
    · rw [ite_eq_right (show g.slope i j ≠ 0 from flat)]
      have bp : 0 < b := lt_of_le_of_ne nonneg (Ne.symm flat)
      have nn := div_nonneg (mul_nonneg (sub_nonneg.mpr admissible.2) gp.le) bp.le
      change (0 < g.gain j ∧ a + b * ((z.val : ℚ) / G) ≤ w) ↔
        z.val < min G (⌊(w-a) * G / b⌋₊ + 1)
      rw [lt_min_iff, and_iff_right z.isLt, Nat.lt_succ_iff, Nat.le_floor_iff nn, le_div_iff₀ bp,
        and_iff_right admissible.1]
      have identity : (a + b * ((z.val : ℚ) / G)) * G = a * G + b * z.val := by
        field_simp [gp.ne']
      constructor
      · intro cost
        have hm := mul_le_mul_of_nonneg_right cost gp.le
        linarith
      · intro bound
        apply (mul_le_mul_iff_left₀ gp).mp
        linarith
  · rw [ite_eq_right admissible]
    have extra := mul_nonneg nonneg (div_nonneg (Nat.cast_nonneg z.val) gp.le)
    exact iff_of_false (fun ⟨site,hc⟩ => admissible ⟨site, by dsimp [b] at hc; linarith⟩)
      (Nat.not_lt_zero _)

end Kintali.ExactRecovery
