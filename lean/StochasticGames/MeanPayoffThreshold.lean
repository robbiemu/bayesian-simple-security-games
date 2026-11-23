module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.SaddlePoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer max-atoms and the mean-payoff threshold

Rational potentials of an integer max-atom system can be rounded componentwise.
The edge transformation in the threshold reduction reverses the strict sign of
every bounded-length integer cycle. The last lemma applies this arithmetic to a
supplied saddle point of positional cycle payoffs. Positional determinacy and
the construction of a cycle from a graph and a pair of policies are hypotheses
of the surrounding reduction.
-/

@[expose] public section

namespace StochasticGames.MeanPayoffThreshold

/-- Scaling both sides and all offsets by the same positive rational preserves a row. -/
theorem scale_max_atom (u v w a b s : ℚ) (hs : 0 < s) :
    u ≤ max (v + a) (w + b) ↔ s * u ≤ max (s * v + s * a) (s * w + s * b) := by
  rw [← mul_add, ← mul_add, ← mul_max_of_nonneg _ _ hs.le, mul_le_mul_iff_right₀ hs]

/-- Flooring a feasible row commutes with its integer offsets and its maximum. -/
theorem floor_max_atom {u v w : ℚ} (a b : ℤ)
    (h : u ≤ max (v + a) (w + b)) : ⌊u⌋ ≤ max (⌊v⌋ + a) (⌊w⌋ + b) := by
  simpa only [Int.floor_mono.map_max, Int.floor_add_intCast] using Int.floor_le_floor h

/-- After clearing denominators, rational and integer feasibility are equivalent. -/
theorem max_atoms_feasible_iff {Var Row : Type*} (lhs left right : Row → Var)
    (a b : Row → ℤ) :
    (∃ x : Var → ℚ, ∀ i, x (lhs i) ≤ max (x (left i) + a i) (x (right i) + b i)) ↔
    (∃ x : Var → ℤ, ∀ i, x (lhs i) ≤ max (x (left i) + a i) (x (right i) + b i)) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun j => ⌊x j⌋, fun i => floor_max_atom _ _ (hx i)⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun j => (x j : ℚ), fun i => ?_⟩
    change (x (lhs i) : ℚ) ≤ max ((x (left i) : ℚ) + a i) ((x (right i) : ℚ) + b i)
    exact_mod_cast hx i

/-- Changing owners exchanges maximization and minimization. These are the new edge weights. -/
def swapWeight (N : ℕ) (w : ℤ) : ℤ := -(N : ℤ) * w - 1

theorem sum_swapWeight (N : ℕ) (weights : List ℤ) :
    (weights.map (swapWeight N)).sum = -(N : ℤ) * weights.sum - weights.length := by
  induction weights with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih,
      swapWeight]
    ring

/-- Integer totals leave a large enough gap to complement the weak threshold. -/
theorem swap_total_nonneg_iff {N len : ℕ} (positive : 0 < len) (bounded : len ≤ N) (z : ℤ) :
    0 ≤ -(N : ℤ) * z - len ↔ z < 0 := by
  have hlen : (0 : ℤ) < len := by exact_mod_cast positive
  have hbound : (len : ℤ) ≤ N := by exact_mod_cast bounded
  have hN : (0 : ℤ) ≤ N := Int.natCast_nonneg N
  constructor
  · intro h
    by_contra! hz
    nlinarith [mul_nonneg hN hz]
  · intro hz
    have hz' : z ≤ -1 := by omega
    nlinarith [mul_le_mul_of_nonneg_left hz' hN]

def cycleMean (weights : List ℤ) : ℚ := (weights.sum : ℚ) / weights.length

theorem cycleMean_swap (N : ℕ) (weights : List ℤ) (positive : 0 < weights.length) :
    cycleMean (weights.map (swapWeight N)) = -(N : ℚ) * cycleMean weights - 1 := by
  have hlen : (weights.length : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  simp only [cycleMean, sum_swapWeight, List.length_map]
  push_cast
  field_simp [hlen]

theorem cycleMean_swap_nonneg_iff {N : ℕ} (weights : List ℤ)
    (positive : 0 < weights.length) (bounded : weights.length ≤ N) :
    0 ≤ cycleMean (weights.map (swapWeight N)) ↔ cycleMean weights < 0 := by
  have hlen : (0 : ℚ) < weights.length := by exact_mod_cast positive
  simp only [cycleMean, List.length_map, sum_swapWeight, le_div_iff₀ hlen, div_lt_iff₀ hlen,
    zero_mul]
  exact_mod_cast swap_total_nonneg_iff positive bounded weights.sum

/-- Min chooses the first coordinate of the original saddle and Max the second.
Swapping the players sends this pair to a saddle for the transformed cycle means. -/
theorem positional_saddle_swap {MinStrategy MaxStrategy : Type*}
    (cycles : MinStrategy → MaxStrategy → List ℤ) (N : ℕ)
    (positive : ∀ i j, 0 < (cycles i j).length)
    {i₀ : MinStrategy} {j₀ : MaxStrategy}
    (saddle : IsSaddlePointOn Set.univ Set.univ (fun i j => cycleMean (cycles i j)) i₀ j₀) :
    IsSaddlePointOn Set.univ Set.univ
      (fun j i => cycleMean ((cycles i j).map (swapWeight N))) j₀ i₀ := by
  intro j hj i hi
  change cycleMean ((cycles i j₀).map (swapWeight N)) ≤
    cycleMean ((cycles i₀ j).map (swapWeight N))
  rw [cycleMean_swap _ _ (positive i j₀), cycleMean_swap _ _ (positive i₀ j)]
  exact sub_le_sub_right (mul_le_mul_of_nonpos_left (saddle i hi j hj)
    (neg_nonpos.mpr (Nat.cast_nonneg N))) 1

end StochasticGames.MeanPayoffThreshold
