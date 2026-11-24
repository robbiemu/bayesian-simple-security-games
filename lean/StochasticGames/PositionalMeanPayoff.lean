module

public import StochasticGames.MeanPayoffSemantics
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! # Positional optimality at the actual mean-payoff value

Integer reweighting applies the two-sided certificate theorem at any rational
threshold. The policy spaces are finite. If every positional policy fell short
of the lower value, finitely many opposing witnesses and one intermediate
rational threshold would witness this simultaneously. The dual argument gives
a positional minimizing policy at the same value.
-/

public section
namespace StochasticGames.MeanPayoff.Game
variable {V E : Type*} (G : Game V E)

private def shift (q : ℚ) : Game V E :=
  {G with weight := fun e => (q.den : ℤ) * G.weight e - q.num}

private theorem shifted_total (s : V) (q : ℚ) (σ τ : G.Strategy) (n : ℕ) :
    (G.shift q).total s ((G.shift q).mix σ τ) n =
      (q.den : ℤ) * G.total s (G.mix σ τ) n - q.num * n := by
  let t := G.mix σ τ
  change (G.shift q).total s t n = _
  have hh (m : ℕ) : (G.shift q).history s t m = G.history s t m := by
    induction m with
    | zero => rfl
    | succ m ih => exact congrArg (fun h : V × List E =>
        (G.dst (t h.2 h.1), (t h.2 h.1).val :: h.2)) ih
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total, ih, Nat.cast_succ, mul_add, mul_one]
    have ea : (G.shift q).arc s t n = G.arc s t n :=
      congrArg (fun h : V × List E => (t h.2 h.1).val) (hh n)
    change _ + ((q.den : ℤ) * G.weight ((G.shift q).arc s t n) - q.num) = _
    rw [ea]
    change _ = (q.den : ℤ) * G.total s t n + q.den * G.weight (G.arc s t n) - _
    ring

variable [Fintype V] [Fintype E]

private theorem rational_prefix_threshold (s : V) (q : ℚ) :
    (∃ (p : G.Policy) (b : ℝ), ∀ τ n, (q : ℝ) * n + b ≤ G.total s (G.mix (fun _ => p) τ) n) ∨
    (∃ (p : G.Policy) (b : ℝ), ∀ σ n, (G.total s (G.mix σ (fun _ => p)) n : ℝ) ≤ q * n + b) := by
  have den : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  let : Nonempty V := ⟨s⟩
  have size : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rcases (G.shift q).certificate_or_swap s with high | low
  · left
    obtain ⟨p, b, hb⟩ := (G.shift q).certificate_bounds_prefix s high
    refine ⟨p, (b : ℝ) / q.den, fun τ n => ?_⟩
    have hh := hb τ n
    rw [G.shifted_total s q (fun _ => p) τ n] at hh
    have rr : (b : ℝ) ≤ (q.den : ℝ) * G.total s (G.mix (fun _ => p) τ) n - (q.num : ℝ) * n := by
      exact_mod_cast hh
    rw [Rat.cast_def]
    field_simp [den.ne']
    linarith only [rr]
  · right
    obtain ⟨p, b, hb⟩ := (G.shift q).Swap.certificate_bounds_prefix s low
    refine ⟨p, -(b : ℝ) / ((Fintype.card V : ℝ) * q.den), fun σ n => ?_⟩
    have hh := hb σ n
    rw [(G.shift q).swap_profile_total s σ (fun _ => p) n,
      G.shifted_total s q σ (fun _ => p) n] at hh
    have rr : (b : ℝ) ≤ -(Fintype.card V : ℝ) *
        ((q.den : ℝ) * G.total s (G.mix σ (fun _ => p)) n - (q.num : ℝ) * n) - n := by
      exact_mod_cast hh
    rw [Rat.cast_def]
    field_simp [den.ne', size.ne']
    nlinarith only [rr, Nat.cast_nonneg n (α := ℝ)]

theorem rational_positional_threshold (s : V) (q : ℚ) :
    (∃ p : G.Policy, ∀ τ, (q : ℝ) ≤ G.payoff s (fun _ => p) τ) ∨
    (∃ p : G.Policy, ∀ σ, G.payoff s σ (fun _ => p) ≤ (q : ℝ)) := by
  rcases G.rational_prefix_threshold s q with ⟨p, b, h⟩ | ⟨p, b, h⟩
  · exact Or.inl ⟨p, fun τ => G.lower_payoff _ _ _ _ _ (h τ)⟩
  · exact Or.inr ⟨p, fun σ => G.upper_payoff _ _ _ _ _ (h σ)⟩

/-- Both players attain the same value with positional strategies against
arbitrary history-dependent strategies. -/
theorem positional_saddle (s : V) :
    ∃ p q : G.Policy, (∀ τ, G.value s ≤ G.payoff s (fun _ => p) τ) ∧
      (∀ σ, G.payoff s σ (fun _ => q) ≤ G.value s) := by
  classical
  let p₀ : G.Policy := fun v => ⟨(G.outgoing v).choose, (G.outgoing v).choose_spec⟩
  have inhabited : (Finset.univ : Finset G.Policy).Nonempty := ⟨p₀, Finset.mem_univ _⟩
  have maxWins : ∃ p : G.Policy, ∀ τ, G.value s ≤ G.payoff s (fun _ => p) τ := by
    by_contra! fail
    choose opponent loss using fail
    let f (p : G.Policy) := G.payoff s (fun _ => p) (opponent p)
    obtain ⟨p, _, greatest⟩ := Finset.exists_max_image _ f inhabited
    obtain ⟨r, hr, hv⟩ := exists_rat_btwn (loss p)
    rcases G.rational_positional_threshold s r with ⟨t, lower⟩ | ⟨t, upper⟩
    · exact (not_lt_of_ge ((lower (opponent t)).trans (greatest t (Finset.mem_univ _)))) hr
    · exact (not_lt_of_ge (G.value_le_of_min s r ⟨fun _ => t, upper⟩)) hv
  have minWins : ∃ q : G.Policy, ∀ σ, G.payoff s σ (fun _ => q) ≤ G.value s := by
    by_contra! fail
    choose opponent loss using fail
    let f (p : G.Policy) := G.payoff s (opponent p) (fun _ => p)
    obtain ⟨p, _, least⟩ := Finset.exists_min_image _ f inhabited
    obtain ⟨r, hv, hr⟩ := exists_rat_btwn (loss p)
    rcases G.rational_positional_threshold s r with ⟨t, lower⟩ | ⟨t, upper⟩
    · exact (not_lt_of_ge (G.le_value_of_guarantees s r ⟨fun _ => t, lower⟩)) hv
    · exact (not_lt_of_ge ((least t (Finset.mem_univ _)).trans (upper (opponent t)))) hr
  obtain ⟨p, hp⟩ := maxWins
  obtain ⟨q, hq⟩ := minWins
  exact ⟨p, q, hp, hq⟩

/-- The owner/weight reversal acts affinely on the exact game value. A
rational threshold separates the two sides of any purported strict
inequality. Both prefix bounds transfer along the same arc sequence. -/
theorem swap_value (s : V) :
    G.Swap.value s = -(Fintype.card V : ℝ) * G.value s - 1 := by
  let : Nonempty V := ⟨s⟩
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  let z := (-G.Swap.value s - 1) / N
  have eq : z * N = -G.Swap.value s - 1 := div_mul_cancel₀ _ hN.ne'
  have sep (r : ℚ) : (G.value s ≤ r ∧ -N * (r : ℝ) - 1 ≤ G.Swap.value s) ∨
      ((r : ℝ) ≤ G.value s ∧ G.Swap.value s ≤ -N * (r : ℝ) - 1) := by
    rcases G.rational_prefix_threshold s r with ⟨p, b, step⟩ | ⟨p, b, step⟩
    · right
      refine ⟨G.le_value_of_guarantees _ _ ⟨fun _ => p, fun τ =>
        G.lower_payoff _ _ _ _ _ (step τ)⟩, G.Swap.value_le_of_min _ _ ⟨fun _ => p, fun τ =>
          G.Swap.upper_payoff _ _ _ _ (-N*b) (fun n => ?_)⟩⟩
      rw [G.swap_profile_total s (fun _ => p) τ n]
      push_cast
      dsimp [N]
      nlinarith only [mul_le_mul_of_nonneg_left (step τ n) hN.le]
    · left
      refine ⟨G.value_le_of_min _ _ ⟨fun _ => p, fun σ =>
        G.upper_payoff _ _ _ _ _ (step σ)⟩, G.Swap.le_value_of_guarantees _ _ ⟨fun _ => p, fun σ =>
          G.Swap.lower_payoff _ _ _ _ (-N*b) (fun n => ?_)⟩⟩
      rw [G.swap_profile_total s σ (fun _ => p) n]
      push_cast
      dsimp [N]
      nlinarith only [mul_le_mul_of_nonneg_left (step σ n) hN.le]
  suffices same : G.value s = z by
    change G.Swap.value s = -N * G.value s - 1
    rw [same]
    linarith only [eq]
  apply le_antisymm
  · by_contra! h
    obtain ⟨r, hz, hv⟩ := exists_rat_btwn h
    rcases sep r with hr | hr
    · exact (not_lt_of_ge hr.1) hv
    · nlinarith only [mul_lt_mul_of_pos_right hz hN, hr.2, eq]
  · by_contra! h
    obtain ⟨r, hv, hz⟩ := exists_rat_btwn h
    rcases sep r with hr | hr
    · nlinarith only [mul_lt_mul_of_pos_right hz hN, hr.2, eq]
    · exact (not_lt_of_ge hr.1) hv

end StochasticGames.MeanPayoff.Game
