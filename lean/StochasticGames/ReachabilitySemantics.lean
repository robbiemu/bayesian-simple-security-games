module

public import StochasticGames.SourcePlay
import Mathlib.Tactic.Linarith

/-!
# Reachability values and strict H4 certificates

Pure finite-horizon choices guarantee the Bellman iterates against every history-dependent
behavioral strategy. For every prefixed vector, a single pure positional Min strategy bounds
all winning probabilities. These two guarantees identify the lower and upper values of
actual play with the least Bellman fixed point, including in games with nonterminating plays.
-/

@[expose] public section

namespace StochasticGames.Source

noncomputable section

open Reachability (Cube)

variable {ι : Type*}

def maximize (x : Cube ι) : PureDecision ι :=
  fun head tail => argUpper (fun k => label x (move head tail k))

def minimize (x : Cube ι) : PureDecision ι :=
  fun head tail => argLower (fun k => label x (move head tail k))

theorem Row.maximize_guarantee (row : Row ι) (x : Cube ι) (τ : Decision ι) :
    row.eval x ≤ row.step (maximize x).toDecision τ (fun _ => label x) := by
  cases row with
  | max head tail =>
    let f := fun k => label x (move head tail k)
    change upper f ≤ (Lottery.pure (argUpper f)).expect f
    rw [Lottery.expect_pure, apply_argUpper f]
  | min head tail =>
    let f := fun k => label x (move head tail k)
    exact (τ head tail).le_expect f (lower f) (lower_le f)
  | chance left right => rw [Row.chance_step]; exact le_rfl

theorem Row.minimize_guarantee (row : Row ι) (x : Cube ι) (σ : Decision ι) :
    row.step σ (minimize x).toDecision (fun _ => label x) ≤ row.eval x := by
  cases row with
  | max head tail =>
    let f := fun k => label x (move head tail k)
    exact (σ head tail).expect_le f (upper f) (le_upper f)
  | min head tail =>
    let f := fun k => label x (move head tail k)
    change (Lottery.pure (argLower f)).expect f ≤ lower f
    rw [Lottery.expect_pure, apply_argLower f]
  | chance left right => rw [Row.chance_step]; exact le_rfl

/-- With `N` moves in total, use the value of the moves remaining after the next one. -/
def horizonMax (rows : ι → Row ι) (N : ℕ) : PureStrategy ι :=
  fun h _ => maximize (iterate rows (N - (h.length + 1)))

def horizonMin (rows : ι → Row ι) (N : ℕ) : PureStrategy ι :=
  fun h _ => minimize (iterate rows (N - (h.length + 1)))

theorem horizonMax_guarantee (rows : ι → Row ι) (N : ℕ) (τ : Strategy ι) (n : ℕ)
    (h : History ι) (p : Position ι) (hlen : n + h.length = N) :
    label (iterate rows n) p ≤ winWithin rows (horizonMax rows N).toStrategy τ n h p := by
  induction n generalizing h p with
  | zero => exact le_rfl
  | succ n ih =>
    cases p with
    | inr b => cases b <;> exact le_rfl
    | inl i =>
      rw [iterate_succ]
      change (rows i).eval (iterate rows n) ≤
        (rows i).step (maximize (iterate rows (N - (h.length + 1)))).toDecision (τ h i) _
      have heq : N - (h.length + 1) = n := by omega
      rw [heq]
      apply ((rows i).maximize_guarantee _ _).trans
      apply Row.step_mono
      intro k p
      apply ih
      simp only [List.length_cons]
      omega

theorem horizonMin_guarantee (rows : ι → Row ι) (N : ℕ) (σ : Strategy ι) (n : ℕ)
    (h : History ι) (p : Position ι) (hlen : n + h.length = N) :
    winWithin rows σ (horizonMin rows N).toStrategy n h p ≤ label (iterate rows n) p := by
  induction n generalizing h p with
  | zero => exact le_rfl
  | succ n ih =>
    cases p with
    | inr b => cases b <;> exact le_rfl
    | inl i =>
      rw [iterate_succ]
      change (rows i).step (σ h i) (minimize (iterate rows (N - (h.length + 1)))).toDecision _ ≤
        (rows i).eval (iterate rows n)
      have heq : N - (h.length + 1) = n := by omega
      rw [heq]
      refine le_trans ?_ ((rows i).minimize_guarantee (iterate rows n) (σ h i))
      apply Row.step_mono
      intro k p
      apply ih
      simp only [List.length_cons]
      omega

/-- Both finite-horizon game values quantify over all behavioral strategies, and both
equal the backward-induction vector. -/
theorem finite_horizon_values (rows : ι → Row ι) (n : ℕ) (p : Position ι) :
    (⨆ σ, ⨅ τ, winWithin rows σ τ n [] p) = label (iterate rows n) p ∧
    (⨅ τ, ⨆ σ, winWithin rows σ τ n [] p) = label (iterate rows n) p := by
  have hlo : label (iterate rows n) p ≤ ⨆ σ, ⨅ τ, winWithin rows σ τ n [] p :=
    le_iSup_of_le (horizonMax rows n).toStrategy (le_iInf fun τ =>
      horizonMax_guarantee rows n τ n [] p (by simp))
  have hhi : (⨅ τ, ⨆ σ, winWithin rows σ τ n [] p) ≤ label (iterate rows n) p :=
    iInf_le_of_le (horizonMin rows n).toStrategy (iSup_le fun σ =>
      horizonMin_guarantee rows n σ n [] p (by simp))
  have hweak := iSup_iInf_le_iInf_iSup (fun σ τ => winWithin rows σ τ n [] p)
  exact ⟨le_antisymm (hweak.trans hhi) hlo, le_antisymm hhi (hlo.trans hweak)⟩

/-- The choice depends only on the current state's menu and the fixed vector `x`. -/
def positionalMin (x : Cube ι) : PureStrategy ι := fun _ _ => minimize x

theorem positionalMin_within_le (rows : ι → Row ι) (x : Cube ι) (hx : bellman rows x ≤ x)
    (σ : Strategy ι) (n : ℕ) (h : History ι) (p : Position ι) :
    winWithin rows σ (positionalMin x).toStrategy n h p ≤ label x p := by
  induction n generalizing h p with
  | zero => exact label_mono bot_le p
  | succ n ih =>
    cases p with
    | inr b => cases b <;> exact le_rfl
    | inl i =>
      refine (le_trans ?_ ((rows i).minimize_guarantee x (σ h i))).trans (hx i)
      exact (rows i).step_mono _ _ (fun k p => ih ((i,k)::h) p)

theorem positionalMin_eventual_le (rows : ι → Row ι) (x : Cube ι) (hx : bellman rows x ≤ x)
    (σ : Strategy ι) (p : Position ι) :
    eventual rows σ (positionalMin x).toStrategy p ≤ label x p :=
  iSup_le fun n => positionalMin_within_le rows x hx σ n [] p

/-- Lower game value, defined from strategy payoffs. -/
def value (rows : ι → Row ι) (p : Position ι) : unitInterval :=
  ⨆ σ, ⨅ τ, eventual rows σ τ p

/-- Upper game value, defined independently by reversing the strategy quantifiers. -/
def upperValue (rows : ι → Row ι) (p : Position ι) : unitInterval :=
  ⨅ τ, ⨆ σ, eventual rows σ τ p

theorem value_le_upperValue (rows : ι → Row ι) (p : Position ι) :
    value rows p ≤ upperValue rows p :=
  iSup_iInf_le_iInf_iSup (fun σ τ => eventual rows σ τ p)

theorem iterate_le_value (rows : ι → Row ι) (n : ℕ) (p : Position ι) :
    label (iterate rows n) p ≤ value rows p := by
  apply le_iSup_of_le (horizonMax rows n).toStrategy
  apply le_iInf
  intro τ
  exact (horizonMax_guarantee rows n τ n [] p (by simp)).trans
    (le_iSup (fun k => winWithin rows (horizonMax rows n).toStrategy τ k [] p) n)

theorem lfp_le_value (rows : ι → Row ι) (p : Position ι) :
    label (bellman rows).lfp p ≤ value rows p := by
  cases p with
  | inl i =>
    change (bellman rows).lfp i ≤ _
    rw [lfp_eq_iSup_iterate, iSup_apply]
    exact iSup_le fun n => iterate_le_value rows n (.inl i)
  | inr b =>
    have hb := iterate_le_value rows 0 (Sum.inr b)
    cases b <;> exact hb

theorem upperValue_le_prefixed (rows : ι → Row ι) (x : Cube ι) (hx : bellman rows x ≤ x)
    (p : Position ι) : upperValue rows p ≤ label x p :=
  iInf_le_of_le (positionalMin x).toStrategy (iSup_le fun σ => positionalMin_eventual_le rows x hx σ p)

theorem value_eq_lfp (rows : ι → Row ι) (p : Position ι) :
    value rows p = label (bellman rows).lfp p :=
  le_antisymm ((value_le_upperValue rows p).trans
    (upperValue_le_prefixed rows _ (bellman rows).map_lfp.le p)) (lfp_le_value rows p)

theorem value_eq_upperValue (rows : ι → Row ι) (p : Position ι) :
    value rows p = upperValue rows p := by
  refine le_antisymm (value_le_upperValue rows p) ?_
  rw [value_eq_lfp]
  exact upperValue_le_prefixed rows _ (bellman rows).map_lfp.le p

@[simp] theorem value_win (rows : ι → Row ι) : value rows (.inr true) = 1 := by
  rw [value_eq_lfp]; rfl

@[simp] theorem value_lose (rows : ι → Row ι) : value rows (.inr false) = 0 := by
  rw [value_eq_lfp]; rfl

/-- H4 §2, with real variables, explicit terminal labels, and the actual reachability
game value. The strict comparison includes arbitrary real thresholds. -/
theorem value_lt_iff_dualFeasible (rows : ι → Row ι) (s : ι) (t : ℝ) :
    (value rows (.inl s) : ℝ) < t ↔
      ∃ y : ι → ℝ, DualFeasible rows y ∧ 1 - t < y s := by
  rw [value_eq_lfp]
  change ((bellman rows).lfp s : ℝ) < t ↔ _
  constructor
  · intro h
    exact ⟨fun i => 1 - ((bellman rows).lfp i : ℝ),
      (prefixed_iff_dualFeasible rows _).mp (bellman rows).map_lfp.le, sub_lt_sub_left h 1⟩
  · rintro ⟨y, hy, hs⟩
    let x : Cube ι := fun i => unitInterval.symm ⟨y i, hy.1 i⟩
    have hc : (fun i => 1 - (x i : ℝ)) = y := by
      funext i
      change 1 - (1 - y i) = y i
      linarith
    have hpre : bellman rows x ≤ x := (prefixed_iff_dualFeasible rows x).mpr (hc ▸ hy)
    have hbound := (bellman rows).lfp_le hpre s
    change ((bellman rows).lfp s : ℝ) ≤ 1 - y s at hbound
    linarith

end

end StochasticGames.Source
