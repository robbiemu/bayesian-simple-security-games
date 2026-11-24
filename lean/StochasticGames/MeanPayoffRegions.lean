module

public import StochasticGames.MeanPayoffGraph
public import StochasticGames.MeanPayoffThreshold
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Turning real inequalities on edges into integer positional certificates

On a simple cycle the potential terms cancel, its length is at most the
number of vertices, and its total weight is integral. These three facts
allow a small additive error per edge in the discounted Bellman inequalities.
-/

public section
namespace StochasticGames.MeanPayoff

open Quiver MeanPayoffGraph

private theorem path_bound {V : Type*} [Quiver V]
    (w : ∀ {i j : V}, (i ⟶ j) → ℤ) (a b : ℝ) (x : V → ℝ)
    (h : ∀ {i j : V} (e : i ⟶ j), b ≤ a * w e + x j - x i)
    {i j : V} (q : Path i j) :
    b * q.length ≤ a * q.addWeight w + x j - x i := by
  induction q with
  | nil => simp
  | cons q e ih =>
    simp only [Path.length_cons, Path.addWeight_cons, Nat.cast_add, Nat.cast_one,
      Int.cast_add, mul_add, mul_one]
    linarith [h e]

private theorem swap_path {V : Type*} [Quiver V]
    (w : ∀ {i j : V}, (i ⟶ j) → ℤ) (N : ℕ) {i j : V} (q : Path i j) :
    q.addWeight (fun e => -(N : ℤ) * w e - 1) =
      -(N : ℤ) * q.addWeight w - q.length := by
  induction q with
  | nil => simp
  | cons q e ih =>
    simp only [Path.addWeight_cons, Path.length_cons, Nat.cast_add, Nat.cast_one, ih, mul_add]
    omega

variable {V E : Type*} [Fintype V] [Fintype E] (src dst : E → V) (w : E → ℤ)

/-- Every simple cycle has integer total strictly greater than minus one. -/
theorem potential_of_small_error (a : ℝ) (x : V → ℝ)
    (ha : (Fintype.card V : ℝ) * Fintype.card V < a)
    (h : ∀ e, -(Fintype.card V : ℝ) ≤ a * w e + x (dst e) - x (src e)) :
    ∃ y : V → ℤ, ∀ e, y (src e) ≤ w e + y (dst e) := by
  apply (row_potential_iff src dst w).mpr
  let := rowQuiver src dst
  let weight : ∀ {i j : V}, (i ⟶ j) → ℤ := fun {_ _} e => w e.val
  apply (closed_iff_simple_cycles (V := V) weight).mpr
  intro i j q e simple
  let loop := q.cons e
  have length : (loop.length : ℝ) ≤ Fintype.card V := by
    exact_mod_cast simple_cycle_length_le_card q e simple
  have bound := path_bound (V := V) weight a (-(Fintype.card V : ℝ)) x
    (fun {i j} e => by obtain ⟨r, rfl, rfl⟩ := e; exact h r) loop
  change 0 ≤ loop.addWeight weight
  by_contra! neg
  have hn : (loop.addWeight weight : ℤ) ≤ -1 := by omega
  have hn' : ((loop.addWeight weight : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hn
  have ha0 : 0 ≤ a := (mul_self_nonneg _).trans ha.le
  nlinarith [mul_le_mul_of_nonneg_left hn' ha0,
    mul_le_mul_of_nonneg_left length (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)]

/-- Every simple cycle has strictly negative integer weight. After changing
weights to `-|V| w - 1` its new total is therefore nonnegative. -/
theorem swap_potential_of_strict (a : ℝ) (x : V → ℝ) (ha : 0 < a)
    (h : ∀ e, a * w e + x (dst e) - x (src e) ≤ -1) :
    ∃ y : V → ℤ, ∀ e,
      y (src e) ≤ (-(Fintype.card V : ℤ) * w e - 1) + y (dst e) := by
  apply (row_potential_iff src dst _).mpr
  let := rowQuiver src dst
  let weight : ∀ {i j : V}, (i ⟶ j) → ℤ := fun {_ _} e => w e.val
  apply (closed_iff_simple_cycles (V := V)
    (fun {_ _} e => -(Fintype.card V : ℤ) * weight e - 1)).mpr
  intro i j q e simple
  let loop := q.cons e
  have pos : 0 < loop.length := Nat.zero_lt_succ _
  have bound := path_bound (V := V) weight (-a) 1 (fun v => -x v)
    (fun {i j} e => by obtain ⟨r, rfl, rfl⟩ := e; dsimp [weight]; linarith [h r]) loop
  rw [swap_path (V := V) weight (Fintype.card V)]
  apply (MeanPayoffThreshold.swap_total_nonneg_iff pos (simple_cycle_length_le_card q e simple) _).mpr
  change loop.addWeight weight < 0
  have hp : (0 : ℝ) < loop.length := by exact_mod_cast pos
  by_contra! hn
  have hn' : (0 : ℝ) ≤ loop.addWeight weight := by exact_mod_cast hn
  nlinarith [mul_nonneg ha.le hn']

end StochasticGames.MeanPayoff
