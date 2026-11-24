module

public import StochasticGames.SourceBellman
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Winning probabilities of history-dependent plays

Each player supplies a probability vector on the listed moves after every finite history.
A history records the states and the move occurrences (including fair-coin outcomes).
The finite play tree gives the probability of winning by a given move and the mass of
first winning on a given move. The sum of these disjoint first-hit masses is the eventual
reachability payoff. Thus plays that never visit Win contribute zero.
-/

@[expose] public section

namespace StochasticGames.Source

noncomputable section

open Filter Topology
open Reachability (Cube midpoint)

variable {ι : Type*} {n : ℕ}

/-- A probability distribution on `n+1` move occurrences. -/
structure Lottery (n : ℕ) where
  weight : Fin (n + 1) → ℝ
  nonneg (k) : 0 ≤ weight k
  total : ∑ k, weight k = 1

def Lottery.pure (k : Fin (n + 1)) : Lottery n where
  weight j := if j = k then 1 else 0
  nonneg j := by split <;> norm_num
  total := by simp

def Lottery.fairCoin : Lottery 1 where
  weight _ := 1/2
  nonneg _ := by norm_num
  total := by norm_num [Fin.sum_univ_two]

def Lottery.expect (d : Lottery n) (f : Fin (n + 1) → unitInterval) : unitInterval :=
  ⟨∑ k, d.weight k * (f k : ℝ), Finset.sum_nonneg (fun k _ => mul_nonneg (d.nonneg k)
      (f k).property.1), by
    calc
      _ ≤ ∑ k, d.weight k * 1 := Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (f k).property.2 (d.nonneg k)
      _ = 1 := by simp [d.total]⟩

theorem Lottery.expect_mono (d : Lottery n) : Monotone d.expect := by
  intro f g h
  change (∑ k, d.weight k * (f k : ℝ)) ≤ ∑ k, d.weight k * (g k : ℝ)
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (d.nonneg k)

@[simp] theorem Lottery.expect_const (d : Lottery n) (c : unitInterval) :
    d.expect (fun _ => c) = c := by
  apply Subtype.ext
  change (∑ k, d.weight k * (c : ℝ)) = c
  rw [← Finset.sum_mul, d.total, one_mul]

@[simp] theorem Lottery.expect_pure (k : Fin (n + 1)) (f : Fin (n + 1) → unitInterval) :
    (Lottery.pure k).expect f = f k := by
  apply Subtype.ext
  simp [Lottery.expect, Lottery.pure, ite_mul]

@[simp] theorem Lottery.expect_fairCoin (f : Fin 2 → unitInterval) :
    fairCoin.expect f = midpoint (f 0) (f 1) := by
  apply Subtype.ext
  change (∑ k, (1/2 : ℝ) * (f k : ℝ)) = ((f 0 : ℝ) + f 1) / 2
  rw [Fin.sum_univ_two]
  ring

theorem Lottery.expect_le (d : Lottery n) (f : Fin (n + 1) → unitInterval) (c : unitInterval)
    (h : ∀ k, f k ≤ c) : d.expect f ≤ c :=
  (d.expect_mono h).trans_eq (d.expect_const c)

theorem Lottery.le_expect (d : Lottery n) (f : Fin (n + 1) → unitInterval) (c : unitInterval)
    (h : ∀ k, c ≤ f k) : c ≤ d.expect f :=
  (d.expect_const c).symm.trans_le (d.expect_mono h)

theorem Lottery.expect_add (d : Lottery n) (f g h : Fin (n + 1) → unitInterval)
    (hadd : ∀ k, (f k : ℝ) = g k + (h k : ℝ)) :
    (d.expect f : ℝ) = d.expect g + (d.expect h : ℝ) := by
  change (∑ k, d.weight k * (f k : ℝ)) =
    (∑ k, d.weight k * (g k : ℝ)) + ∑ k, d.weight k * (h k : ℝ)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [hadd, mul_add]

/-- Previous states and observed move indices, most recent first. The current state is
supplied separately. The two fair-coin outcomes have indices 0 and 1. -/
abbrev History (ι : Type*) := List (ι × ℕ)

abbrev Decision (ι : Type*) := (head : Position ι) → (tail : List (Position ι)) → Lottery tail.length
abbrev Strategy (ι : Type*) := History ι → ι → Decision ι
abbrev PureDecision (ι : Type*) :=
  (head : Position ι) → (tail : List (Position ι)) → Fin (tail.length + 1)
abbrev PureStrategy (ι : Type*) := History ι → ι → PureDecision ι

def PureDecision.toDecision (d : PureDecision ι) : Decision ι :=
  fun head tail => Lottery.pure (d head tail)

def PureStrategy.toStrategy (σ : PureStrategy ι) : Strategy ι :=
  fun h i => (σ h i).toDecision

instance : Nonempty (PureStrategy ι) := ⟨fun _ _ _ _ => 0⟩
instance : Nonempty (Strategy ι) := ⟨fun _ _ _ _ => Lottery.pure 0⟩

/-- Number of additional moves after the first listed move. -/
def Row.arityPred : Row ι → ℕ
  | .max _ tail | .min _ tail => tail.length
  | .chance _ _ => 1

def Row.next (row : Row ι) : Fin (row.arityPred + 1) → Position ι :=
  match row with
  | .max head tail | .min head tail => move head tail
  | .chance left right => fun k => if k = 0 then left else right

def Row.law (row : Row ι) (σ τ : Decision ι) : Lottery row.arityPred :=
  match row with
  | .max head tail => σ head tail
  | .min head tail => τ head tail
  | .chance _ _ => Lottery.fairCoin

def Row.step (row : Row ι) (σ τ : Decision ι) (f : ℕ → Position ι → unitInterval) :
    unitInterval :=
  (row.law σ τ).expect (fun k => f k.val (row.next k))

theorem Row.step_mono (row : Row ι) (σ τ : Decision ι) {f g : ℕ → Position ι → unitInterval}
    (h : ∀ k p, f k p ≤ g k p) : row.step σ τ f ≤ row.step σ τ g :=
  (row.law σ τ).expect_mono fun k => h k.val (row.next k)

@[simp] theorem Row.chance_step (a b : Position ι) (σ τ : Decision ι)
    (f : ℕ → Position ι → unitInterval) :
    (Row.chance a b).step σ τ f = midpoint (f 0 a) (f 1 b) := by
  change Lottery.fairCoin.expect (fun k : Fin 2 => f k.val (if k = 0 then a else b)) = _
  rw [Lottery.expect_fairCoin]
  simp

/-- Probability mass of leaves that have reached Win within `n` moves. At either terminal
the branch stops immediately. At a nonterminal the continuation uses the observed move. -/
def winWithin (rows : ι → Row ι) (σ τ : Strategy ι) : ℕ → History ι → Position ι → unitInterval
  | 0, _, p => label ⊥ p
  | _+1, _, .inr b => label (⊥ : Cube ι) (.inr b)
  | n+1, h, .inl i => (rows i).step (σ h i) (τ h i)
      (fun k => winWithin rows σ τ n ((i, k) :: h))

/-- Mass of paths that visit Win for the first time on exactly move `n`. Once a branch
has already stopped at a terminal, its mass at all later times is zero. -/
def firstHit (rows : ι → Row ι) (σ τ : Strategy ι) : ℕ → History ι → Position ι → unitInterval
  | 0, _, p => label ⊥ p
  | _+1, _, .inr _ => 0
  | n+1, h, .inl i => (rows i).step (σ h i) (τ h i)
      (fun k => firstHit rows σ τ n ((i, k) :: h))

theorem winWithin_add_firstHit (rows : ι → Row ι) (σ τ : Strategy ι) (n : ℕ)
    (h : History ι) (p : Position ι) :
    (winWithin rows σ τ (n+1) h p : ℝ) = winWithin rows σ τ n h p + (firstHit rows σ τ (n+1) h p : ℝ) := by
  induction n generalizing h p with
  | zero =>
    cases p with
    | inl i => simp [winWithin, firstHit, label]
    | inr b => cases b <;> simp [winWithin, firstHit, label]
  | succ n ih =>
    cases p with
    | inr b => simp [winWithin, firstHit]
    | inl i =>
      exact ((rows i).law (σ h i) (τ h i)).expect_add _ _ _ fun k => ih _ _

theorem winWithin_mono (rows : ι → Row ι) (σ τ : Strategy ι) (h : History ι) (p : Position ι) :
    Monotone (fun n => winWithin rows σ τ n h p) := by
  apply monotone_nat_of_le_succ
  intro n
  change (winWithin rows σ τ n h p : ℝ) ≤ winWithin rows σ τ (n+1) h p
  rw [winWithin_add_firstHit]
  exact le_add_of_nonneg_right (firstHit rows σ τ (n+1) h p).property.1

/-- An increasing union of finite winning events. -/
def eventual (rows : ι → Row ι) (σ τ : Strategy ι) (p : Position ι) : unitInterval :=
  ⨆ n, winWithin rows σ τ n [] p

theorem tendsto_winWithin (rows : ι → Row ι) (σ τ : Strategy ι) (p : Position ι) :
    Tendsto (fun n => winWithin rows σ τ n [] p) atTop (𝓝 (eventual rows σ τ p)) :=
  tendsto_atTop_iSup (winWithin_mono rows σ τ [] p)

theorem sum_firstHit (rows : ι → Row ι) (σ τ : Strategy ι) (n : ℕ)
    (h : History ι) (p : Position ι) :
    ∑ k ∈ Finset.range (n+1), (firstHit rows σ τ k h p : ℝ) = winWithin rows σ τ n h p := by
  induction n with
  | zero => simp [firstHit, winWithin]
  | succ n ih => rw [Finset.sum_range_succ, ih, winWithin_add_firstHit]

/-- The payoff is the countable sum over disjoint first-winning times. Each summand is
computed solely from the strategies' actual transition probabilities on the finite tree. -/
theorem hasSum_firstHit (rows : ι → Row ι) (σ τ : Strategy ι) (p : Position ι) :
    HasSum (fun k => (firstHit rows σ τ k [] p : ℝ)) (eventual rows σ τ p : ℝ) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => (firstHit rows σ τ k [] p).property.1) _).2
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  simpa only [sum_firstHit, Function.comp_def] using
    (continuous_subtype_val.tendsto _).comp (tendsto_winWithin rows σ τ p)

end

end StochasticGames.Source
