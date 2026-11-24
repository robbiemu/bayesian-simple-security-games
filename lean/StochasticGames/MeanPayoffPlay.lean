module

public import StochasticGames.MeanPayoffGame
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # History-dependent play and the lower mean-payoff value

The full list of prior arc indices, in reverse chronological order, is
available at every decision. The finite-prefix payoff is the sum of the
weights of the first n arcs divided by n. The lower value is the supremum
of the real bounds Max can guarantee on its limit inferior.
-/

@[expose] public section
namespace StochasticGames.MeanPayoff.Game
open Filter
variable {V E : Type*} (G : Game V E)

abbrev Strategy := List E → G.Policy

def mix (σ τ : G.Strategy) : G.Strategy :=
  fun history v => if G.isMax v then σ history v else τ history v

def history (s : V) (p : G.Strategy) : ℕ → V × List E
  | 0 => (s, [])
  | n+1 =>
    let h := history s p n
    let e := (p h.2 h.1).val
    (G.dst e, e :: h.2)

def arc (s : V) (p : G.Strategy) (n : ℕ) : E :=
  let h := G.history s p n
  (p h.2 h.1).val

def total (s : V) (p : G.Strategy) : ℕ → ℤ
  | 0 => 0
  | n+1 => total s p n + G.weight (G.arc s p n)

noncomputable def average (s : V) (p : G.Strategy) (n : ℕ) : ℝ :=
  (G.total s p n : ℝ) / n

noncomputable def payoff (s : V) (σ τ : G.Strategy) : ℝ :=
  liminf (G.average s (G.mix σ τ)) atTop

def Guarantees (s : V) (a : ℝ) : Prop :=
  ∃ σ, ∀ τ, a ≤ G.payoff s σ τ

noncomputable def value (s : V) : ℝ := sSup {a | G.Guarantees s a}

def Nonnegative (s : V) : Prop := 0 ≤ G.value s

private noncomputable def defaultStrategy : G.Strategy :=
  fun _ v => ⟨(G.outgoing v).choose, (G.outgoing v).choose_spec⟩

private theorem average_bounds [Finite E] :
    ∃ l u : ℝ, ∀ s p, ∀ᶠ n in atTop, l ≤ G.average s p n ∧ G.average s p n ≤ u := by
  obtain ⟨lo, hlo⟩ := Finite.bddBelow_range G.weight
  obtain ⟨hi, hhi⟩ := Finite.bddAbove_range G.weight
  refine ⟨lo, hi, fun s p => ?_⟩
  have bound (n : ℕ) : lo * n ≤ G.total s p n ∧ G.total s p n ≤ hi * n := by
    induction n with
    | zero => simp [total]
    | succ n ih =>
      simp only [total, Nat.cast_succ, mul_add, mul_one]
      exact ⟨add_le_add ih.1 (hlo (Set.mem_range_self _)),
        add_le_add ih.2 (hhi (Set.mem_range_self _))⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  exact ⟨(le_div_iff₀ hnr).mpr (by exact_mod_cast (bound n).1),
    (div_le_iff₀ hnr).mpr (by exact_mod_cast (bound n).2)⟩

private theorem bound_under [Finite E] (s : V) (p : G.Strategy) :
    atTop.IsBoundedUnder (· ≥ ·) (G.average s p) ∧
    atTop.IsBoundedUnder (· ≤ ·) (G.average s p) := by
  obtain ⟨l, u, h⟩ := G.average_bounds
  exact ⟨⟨l, (h s p).mono fun _ hh => hh.1⟩, ⟨u, (h s p).mono fun _ hh => hh.2⟩⟩

private theorem payoff_bounds [Finite E] (s : V) :
    ∃ l u : ℝ, ∀ σ τ, l ≤ G.payoff s σ τ ∧ G.payoff s σ τ ≤ u := by
  obtain ⟨l, u, h⟩ := G.average_bounds
  refine ⟨l, u, fun σ τ => ?_⟩
  let p := G.mix σ τ
  obtain ⟨blo, bhi⟩ := G.bound_under s p
  exact ⟨le_liminf_of_le bhi.isCobounded_flip ((h s p).mono fun _ hh => hh.1),
    liminf_le_of_frequently_le ((h s p).mono fun _ hh => hh.2).frequently blo⟩

theorem le_value_of_guarantees [Finite E] (s : V) (a : ℝ) (h : G.Guarantees s a) :
    a ≤ G.value s := by
  obtain ⟨_, u, bound⟩ := G.payoff_bounds s
  refine le_csSup ⟨u, ?_⟩ h
  rintro b ⟨σ, hb⟩
  exact (hb G.defaultStrategy).trans (bound σ _).2

theorem value_le_of_min [Finite E] (s : V) (a : ℝ)
    (h : ∃ τ, ∀ σ, G.payoff s σ τ ≤ a) : G.value s ≤ a := by
  obtain ⟨l, _, bound⟩ := G.payoff_bounds s
  obtain ⟨τ, ht⟩ := h
  exact csSup_le (s := {b | G.Guarantees s b}) ⟨l, G.defaultStrategy, fun t => (bound _ t).1⟩ (by
    rintro b ⟨σ, hb⟩
    exact (hb τ).trans (ht σ))

private theorem tendsto_line (a b : ℝ) :
    Tendsto (fun n : ℕ => a + b / n) atTop (nhds a) := by
  simpa using (tendsto_const_nhds (x := a)).add (tendsto_const_div_atTop_nhds_zero_nat b)

theorem lower_payoff [Finite E] (s : V) (σ τ : G.Strategy) (a b : ℝ)
    (h : ∀ n : ℕ, a * n + b ≤ (G.total s (G.mix σ τ) n : ℝ)) : a ≤ G.payoff s σ τ := by
  let p := G.mix σ τ
  have cmp : ∀ᶠ n : ℕ in atTop, a + b / n ≤ G.average s p n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have positive : (0 : ℝ) < n := by exact_mod_cast hn
    apply (le_div_iff₀ positive).mpr
    rw [add_mul, div_mul_cancel₀ _ positive.ne']
    exact h n
  have lim := tendsto_line a b
  rw [← lim.liminf_eq]
  exact liminf_le_liminf cmp lim.isBoundedUnder_ge (G.bound_under s p).2.isCobounded_flip

theorem upper_payoff [Finite E] (s : V) (σ τ : G.Strategy) (a b : ℝ)
    (h : ∀ n : ℕ, (G.total s (G.mix σ τ) n : ℝ) ≤ a * n + b) : G.payoff s σ τ ≤ a := by
  let p := G.mix σ τ
  have cmp : ∀ᶠ n : ℕ in atTop, G.average s p n ≤ a + b / n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have positive : (0 : ℝ) < n := by exact_mod_cast hn
    apply (div_le_iff₀ positive).mpr
    rw [add_mul, div_mul_cancel₀ _ positive.ne']
    exact h n
  have lim := tendsto_line a b
  rw [← lim.liminf_eq]
  exact liminf_le_liminf cmp (G.bound_under s p).1 lim.isBoundedUnder_le.isCobounded_flip

end StochasticGames.MeanPayoff.Game
