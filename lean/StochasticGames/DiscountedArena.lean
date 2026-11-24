module

public import StochasticGames.MeanPayoffGame
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Linarith

/-! # A discounted Bellman equation for a finite deterministic arena -/

public section
namespace StochasticGames.MeanPayoff.Game

variable {V E : Type*} [Fintype E] (G : Game V E)

private theorem extremum (z : E → ℝ) (v : V) :
    ∃ a : G.Move v, ∀ b : G.Move v,
      if G.isMax v then z b ≤ z a else z a ≤ z b := by
  classical
  obtain ⟨e, he⟩ := G.outgoing v
  have hn : (Finset.univ : Finset (G.Move v)).Nonempty := ⟨⟨e, he⟩, Finset.mem_univ _⟩
  cases h : G.isMax v
  · obtain ⟨a, _, ha⟩ := Finset.exists_min_image _ (fun a : G.Move v => z a) hn
    exact ⟨a, fun b => ha b (Finset.mem_univ _)⟩
  · obtain ⟨a, _, ha⟩ := Finset.exists_max_image _ (fun a : G.Move v => z a) hn
    exact ⟨a, fun b => ha b (Finset.mem_univ _)⟩

private noncomputable def pick (z : E → ℝ) : G.Policy :=
  fun v => (G.extremum z v).choose

private theorem pick_le (z : E → ℝ) (v : V) (b : G.Move v) :
    if G.isMax v then z b ≤ z (G.pick z v) else z (G.pick z v) ≤ z b :=
  (G.extremum z v).choose_spec b

private theorem extreme_mono_add (x y : E → ℝ) (c : ℝ) (h : ∀ e, x e ≤ y e + c) (v : V) :
    x (G.pick x v) ≤ y (G.pick y v) + c := by
  cases hv : G.isMax v
  · have hh := G.pick_le x v (G.pick y v)
    simp only [hv, Bool.false_eq_true, ↓reduceIte] at hh
    exact hh.trans (h _)
  · have hh := G.pick_le y v (G.pick x v)
    simp only [hv, ↓reduceIte] at hh
    exact (h _).trans (add_le_add_left hh _)

/-- A single positional policy chooses discounted-optimal actions at both
players' vertices. Every edge retained by fixing just one player then
satisfies the corresponding one-sided Bellman inequality. -/
theorem discounted_policy [Fintype V] (d : ℝ) (hd : 0 ≤ d) (h1 : d < 1) :
    ∃ (f : V → ℝ) (p : G.Policy), ∀ e,
      (G.Allowed p e → f (G.src e) ≤ G.weight e + d * f (G.dst e)) ∧
      (G.Swap.Allowed p e → G.weight e + d * f (G.dst e) ≤ f (G.src e)) := by
  classical
  let Q (x : V → ℝ) (e : E) : ℝ := G.weight e + d * x (G.dst e)
  let B (x : V → ℝ) (v : V) : ℝ := Q x (G.pick (Q x) v)
  have mono (x y : V → ℝ) (v : V) : B x v ≤ B y v + d * dist x y := by
    refine G.extreme_mono_add (Q x) (Q y) _ ?_ v
    intro e
    have hh := dist_le_pi_dist x y (G.dst e)
    rw [Real.dist_eq] at hh
    dsimp [Q]
    linarith [mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hh) hd]
  let k : NNReal := ⟨d, hd⟩
  have contr : ContractingWith k B := by
    refine ⟨show d < 1 from h1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    apply (dist_pi_le_iff (mul_nonneg hd dist_nonneg)).mpr
    intro v
    rw [Real.dist_eq, abs_le]
    have hxy := mono x y v
    have hyx := mono y x v
    rw [dist_comm y x] at hyx
    change - (d * dist x y) ≤ _ ∧ _ ≤ d * dist x y
    constructor <;> linarith
  let f := contr.fixedPoint B
  have fix (v : V) : Q f (G.pick (Q f) v) = f v :=
    congrFun contr.fixedPoint_isFixedPt v
  refine ⟨f, G.pick (Q f), fun e => ?_⟩
  let v := G.src e
  have ho := G.pick_le (Q f) v ⟨e, rfl⟩
  rw [← fix (G.src e)]
  change (G.Allowed _ e → Q f (G.pick (Q f) v) ≤ Q f e) ∧
    (G.Swap.Allowed _ e → Q f e ≤ Q f (G.pick (Q f) v))
  cases hv : G.isMax v
  · simp [hv] at ho
    refine ⟨fun _ => ho, fun ha => ?_⟩
    have eq := ha (by simp [Swap, ← show v = G.src e from rfl, hv])
    exact le_of_eq (congrArg (Q f) eq)
  · simp [hv] at ho
    refine ⟨fun ha => ?_, fun _ => ho⟩
    exact le_of_eq (congrArg (Q f) (ha hv)).symm

end StochasticGames.MeanPayoff.Game
