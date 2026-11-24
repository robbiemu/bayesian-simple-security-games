module

public import StochasticGames.MeanPayoffDetermination
public import StochasticGames.MeanPayoffPlay
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-! # The value threshold, positional potentials, and owner reversal -/
public section
namespace StochasticGames.MeanPayoff.Game
variable {V E : Type*} [Fintype V] [Fintype E] (G : Game V E)

omit [Fintype E] in
/-- A positional certificate bounds the total weight uniformly over time
and over all history-dependent opposing strategies. -/
theorem certificate_bounds_prefix (s : V) (h : G.Certificate s) :
    ∃ (p : G.Policy) (b : ℤ), ∀ τ n, b ≤ G.total s (G.mix (fun _ => p) τ) n := by
  obtain ⟨p, R, x, hs, keep⟩ := h
  obtain ⟨hi, hhi⟩ := Finite.bddAbove_range x
  refine ⟨p, x s - hi, fun τ n => ?_⟩
  let t := G.mix (fun _ => p) τ
  have walk (m : ℕ) :
      R (G.history s t m).1 ∧ x s ≤ G.total s t m + x (G.history s t m).1 := by
    induction m with
    | zero => simpa [history, total] using hs
    | succ m ih =>
      let v := (G.history s t m).1
      let e := G.arc s t m
      have src : G.src e = v := (t _ v).property
      have allowed : G.Allowed p e := by
        intro hm
        rw [src] at hm ⊢
        change ((if G.isMax v then p v else τ _ v) : G.Move v).val = (p v).val
        simp [hm]
      have step := keep e allowed (src ▸ ih.1)
      change R (G.dst e) ∧ x s ≤ G.total s t m + G.weight e + x (G.dst e)
      rw [src] at step
      exact ⟨step.1, by linarith [ih.2, step.2]⟩
  linarith [(walk n).2, hhi (Set.mem_range_self (G.history s t n).1)]

theorem certificate_guarantees (s : V) (h : G.Certificate s) : G.Guarantees s 0 := by
  obtain ⟨p, b, hb⟩ := G.certificate_bounds_prefix s h
  refine ⟨fun _ => p, fun τ => G.lower_payoff _ _ _ 0 b (fun n => ?_)⟩
  simpa using (show (b : ℝ) ≤ G.total s (G.mix (fun _ => p) τ) n by exact_mod_cast hb τ n)

omit [Fintype E] in
/-- Opposite players choosing the same strategies follow the same arcs. -/
private theorem swap_mix (σ τ : G.Strategy) : G.Swap.mix τ σ = G.mix σ τ := by
  funext l v
  cases h : G.isMax v <;> simp [mix, Swap, h]

omit [Fintype E] in
theorem swap_profile_total (s : V) (σ τ : G.Strategy) (n : ℕ) :
    G.Swap.total s (G.Swap.mix τ σ) n =
      -(Fintype.card V : ℤ) * G.total s (G.mix σ τ) n - n := by
  rw [G.swap_mix]
  let t := G.mix σ τ
  have hh (m : ℕ) : G.Swap.history s t m = G.history s t m := by
    induction m with
    | zero => rfl
    | succ m ih => exact congrArg (fun h : V × List E =>
        (G.dst (t h.2 h.1), (t h.2 h.1).val :: h.2)) ih
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total, Nat.cast_succ, mul_add, ih]
    change _ + (-(Fintype.card V : ℤ) * G.weight (G.Swap.arc s t n) - 1) = _
    have ea : G.Swap.arc s t n = G.arc s t n := congrArg
      (fun h : V × List E => (t h.2 h.1).val) (hh n)
    rw [ea]
    change _ = -(Fintype.card V : ℤ) * G.total s t n +
      -(Fintype.card V : ℤ) * G.weight (G.arc s t n) - _
    ring

/-- A swapped certificate forces original lower payoff at most `-1/|V|`. -/
theorem value_le_of_swap_certificate (s : V) (h : G.Swap.Certificate s) :
    G.value s ≤ -1 / (Fintype.card V : ℝ) := by
  let : Nonempty V := ⟨s⟩
  have pos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  obtain ⟨p, b, hb⟩ := G.Swap.certificate_bounds_prefix s h
  apply G.value_le_of_min
  refine ⟨fun _ => p, fun σ => G.upper_payoff _ _ _ _ (-(b : ℝ) / Fintype.card V) (fun n => ?_)⟩
  have step := hb σ n
  rw [G.swap_profile_total s σ (fun _ => p) n] at step
  have eq : (b : ℝ) ≤ -(Fintype.card V : ℝ) * G.total s (G.mix σ (fun _ => p)) n - n := by
    exact_mod_cast step
  field_simp [pos.ne']
  nlinarith only [eq]

/-- An original certificate bounds every swapped payoff against that same
positional policy from above by minus one. -/
theorem swap_value_le_of_certificate (s : V) (h : G.Certificate s) : G.Swap.value s ≤ -1 := by
  obtain ⟨p, b, hb⟩ := G.certificate_bounds_prefix s h
  apply G.Swap.value_le_of_min
  refine ⟨fun _ => p, fun τ => G.Swap.upper_payoff _ _ _ _ (-(Fintype.card V : ℝ) * b) (fun n => ?_)⟩
  rw [G.swap_profile_total s (fun _ => p) τ n]
  push_cast
  have step : (b : ℝ) ≤ G.total s (G.mix (fun _ => p) τ) n := by exact_mod_cast hb τ n
  nlinarith only [mul_le_mul_of_nonneg_left step
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)]

theorem nonnegative_iff_certificate (s : V) : G.Nonnegative s ↔ G.Certificate s := by
  refine ⟨fun h => (G.certificate_or_swap s).resolve_right (fun hs => ?_), fun h =>
    G.le_value_of_guarantees s 0 (G.certificate_guarantees s h)⟩
  let : Nonempty V := ⟨s⟩
  have pos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  exact (not_lt_of_ge h) ((G.value_le_of_swap_certificate s hs).trans_lt (div_neg_of_neg_of_pos (by norm_num) pos))

theorem swap_nonnegative_iff (s : V) : G.Swap.Nonnegative s ↔ ¬ G.Nonnegative s := by
  constructor
  · intro hs h
    have neg := G.swap_value_le_of_certificate s ((G.nonnegative_iff_certificate s).mp h)
    change 0 ≤ G.Swap.value s at hs
    linarith
  · intro h
    apply (G.Swap.nonnegative_iff_certificate s).mpr
    exact (G.certificate_or_swap s).resolve_left (h ∘ (G.nonnegative_iff_certificate s).mpr)

/-- If each Max policy allows every vertex to be reached from the start,
a winning region containing the start includes every vertex. -/
theorem nonnegative_iff_potential (s : V)
    (accessible : ∀ (p : G.Policy) (R : V → Prop), R s →
      (∀ e, G.Allowed p e → R (G.src e) → R (G.dst e)) → ∀ v, R v) :
    G.Nonnegative s ↔ ∃ (p : G.Policy) (x : V → ℤ), ∀ e, G.Allowed p e →
      x (G.src e) ≤ G.weight e + x (G.dst e) := by
  rw [G.nonnegative_iff_certificate]
  constructor
  · rintro ⟨p, R, x, hs, step⟩
    have all := accessible p R hs fun e he hv => (step e he hv).1
    exact ⟨p, x, fun e he => (step e he (all _)).2⟩
  · rintro ⟨p, x, h⟩
    exact ⟨p, fun _ => True, x, trivial, fun e he _ => ⟨trivial, h e he⟩⟩

end StochasticGames.MeanPayoff.Game
