module

public import StochasticGames.DiscountedArena
public import StochasticGames.MeanPayoffRegions
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic
/-! # Positional determinacy of the integer zero threshold

Use a discount sufficiently close to one and partition the vertices by
their normalized discounted values. Among `|V|+1` disjoint intervals one
contains no vertex value. The gap makes the upper and lower regions closed
under the respective optimal choices. Bellman inequalities and integer
cycle rounding then yield positional potential certificates on both regions.
-/
public section
namespace StochasticGames.MeanPayoff.Game
variable {V E : Type*} [Fintype V] [Fintype E] (G : Game V E)

private theorem empty_interval (g : V → ℝ) :
    ∃ k : Fin (Fintype.card V + 1), ∀ v,
      g v ≤ -(k.val : ℝ) - 1 ∨ -(k.val : ℝ) ≤ g v := by
  by_contra! h
  choose v hl hu using h
  have inj : Function.Injective v := by
    intro i j eq
    have separate (a b : Fin (Fintype.card V + 1)) (ab : a < b) (same : v a = v b) : False := by
      have diff : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast (show a.val + 1 ≤ b.val from ab)
      have lo := hl a
      rw [same] at lo
      linarith [hu b]
    exact le_antisymm (le_of_not_gt fun h => separate j i h eq.symm)
      (le_of_not_gt fun h => separate i j h eq)
  simpa using Fintype.card_le_of_injective _ inj

/-- Max has a positional potential certificate at the start, or Min has
one after swapping owners and replacing each weight by `-|V| w - 1`. -/
theorem certificate_or_swap (s : V) : G.Certificate s ∨ G.Swap.Certificate s := by
  classical
  let N : ℝ := Fintype.card V
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let A := N * N + 1
  have hA : N * N < A := by dsimp [A]; linarith
  have Apos : 0 < A := (mul_self_nonneg _).trans_lt hA
  obtain ⟨W₀, hW₀⟩ := Finite.bddAbove_range (fun e => |(G.weight e : ℝ)|)
  let W := max W₀ 0
  have hW : 0 ≤ W := le_max_right _ _
  have wb (e : E) : -(W : ℝ) ≤ G.weight e ∧ (G.weight e : ℝ) ≤ W :=
    abs_le.mp ((hW₀ (Set.mem_range_self e)).trans (le_max_left _ _))
  let K := A * W + N + 2
  have hK : 1 < K := by dsimp [K]; linarith [mul_nonneg Apos.le hW]
  let δ := 1 / K
  have hδ : 0 < δ := one_div_pos.mpr (by linarith)
  have hδ1 : δ < 1 := (div_lt_one (by linarith : 0 < K)).mpr hK
  have unit : δ * K = 1 := div_mul_cancel₀ _ (by linarith)
  let d := 1 - δ
  have hd : 0 ≤ d := by dsimp [d]; linarith
  obtain ⟨f, p, bell⟩ := G.discounted_policy d hd (by dsimp [d]; linarith)
  let x v := A * f v
  let g v := δ * x v
  obtain ⟨i, gap⟩ := empty_interval g
  let k : ℝ := i.val
  have k0 : 0 ≤ k := Nat.cast_nonneg _
  have kN : k ≤ N := by dsimp [k, N]; exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  let R v := -k ≤ g v
  let L v := g v ≤ -k - 1
  have cover (v : V) : L v ∨ R v := gap v
  have budget : δ * (A * W + k + 1) < 1 := by
    rw [← unit]
    exact mul_lt_mul_of_pos_left (by dsimp [K]; linarith) hδ
  have prod : 0 ≤ δ * A := mul_nonneg hδ.le Apos.le
  have up (e : E) (he : G.Allowed p e) :
      g (G.src e) ≤ δ * A * G.weight e + d * g (G.dst e) := by
    have hh := mul_le_mul_of_nonneg_left ((bell e).1 he) prod
    dsimp [g, x]
    nlinarith only [hh]
  have down (e : E) (he : G.Swap.Allowed p e) :
      δ * A * G.weight e + d * g (G.dst e) ≤ g (G.src e) := by
    have hh := mul_le_mul_of_nonneg_left ((bell e).2 he) prod
    dsimp [g, x]
    nlinarith only [hh]
  have keepR (e : E) (he : G.Allowed p e) (hs : R (G.src e)) : R (G.dst e) := by
    apply (cover _).resolve_left
    intro hl
    have step := up e he
    have ww := mul_le_mul_of_nonneg_left (wb e).2 prod
    have gg := mul_le_mul_of_nonneg_left hl hd
    dsimp [d] at gg step
    change -k ≤ g (G.src e) at hs
    nlinarith only [hs, step, ww, gg, budget]
  have keepL (e : E) (he : G.Swap.Allowed p e) (hs : L (G.src e)) : L (G.dst e) := by
    apply (cover _).resolve_right
    intro hr
    have step := down e he
    have ww := mul_le_mul_of_nonneg_left (wb e).1 prod
    have gg := mul_le_mul_of_nonneg_left hr hd
    dsimp [d] at gg step
    change g (G.src e) ≤ -k - 1 at hs
    nlinarith only [hs, step, ww, gg, budget, mul_nonneg hδ.le k0, hδ]
  rcases cover s with ls | rs
  · right
    let T := {e : E // G.Swap.Allowed p e ∧ L (G.src e)}
    obtain ⟨y, hy⟩ := MeanPayoff.swap_potential_of_strict (fun e : T => G.src e)
      (fun e : T => G.dst e) (fun e : T => G.weight e) A x Apos (by
        intro e
        have hh := mul_le_mul_of_nonneg_left ((bell e.val).2 e.property.1) Apos.le
        have hg := keepL e.val e.property.1 e.property.2
        change g (G.dst e.val) ≤ -k - 1 at hg
        dsimp [g, x] at hg
        dsimp [x, d] at *
        nlinarith only [hh, hg, k0])
    exact ⟨p, L, y, ls, fun e he hs => ⟨keepL e he hs, hy ⟨e, he, hs⟩⟩⟩
  · left
    let T := {e : E // G.Allowed p e ∧ R (G.src e)}
    obtain ⟨y, hy⟩ := MeanPayoff.potential_of_small_error (fun e : T => G.src e)
      (fun e : T => G.dst e) (fun e : T => G.weight e) A x hA (by
        intro e
        have hh := mul_le_mul_of_nonneg_left ((bell e.val).1 e.property.1) Apos.le
        have hg := keepR e.val e.property.1 e.property.2
        change -k ≤ g (G.dst e.val) at hg
        dsimp [g, x] at hg
        change -N ≤ _
        dsimp [x, d] at *
        nlinarith only [hh, hg, kN])
    exact ⟨p, R, y, rs, fun e he hs => ⟨keepR e he hs, hy ⟨e, he, hs⟩⟩⟩

end StochasticGames.MeanPayoff.Game
