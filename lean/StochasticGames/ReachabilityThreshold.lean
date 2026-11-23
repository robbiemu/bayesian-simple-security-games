module

public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.FixedPoints
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith

/-!
# Strict threshold certificates for reachability Bellman equations

The value used below is the supremum of the finite-horizon Bellman iterates.
Complementing a supersolution gives a subsolution of the row-dual operator.
All statements allow cycles, including nonterminal self-loops.
-/

@[expose] public section

namespace StochasticGames.Reachability

noncomputable section

open Filter Topology

abbrev Cube (State : Type*) := State → unitInterval

variable {State : Type*}

def complement (x : Cube State) : Cube State := fun s => unitInterval.symm (x s)

@[simp] theorem complement_complement (x : Cube State) : complement (complement x) = x :=
  funext fun s => unitInterval.symm_symm (x s)

theorem complement_antitone : Antitone (complement : Cube State → Cube State) :=
  fun _ _ h s => unitInterval.symm_le_symm.mpr (h s)

def dual (F : Cube State →o Cube State) : Cube State →o Cube State where
  toFun y := complement (F (complement y))
  monotone' := complement_antitone.comp_monotone F.monotone |>.comp complement_antitone

theorem dual_subsolution_iff (F : Cube State →o Cube State) (y : Cube State) :
    y ≤ dual F y ↔ F (complement y) ≤ complement y := by
  exact forall_congr' fun _ => unitInterval.le_symm_comm

/-- A strict threshold failure has an existential dual certificate, including when the original
Bellman map has several fixed points. The threshold is any real number. -/
theorem lfp_lt_iff_dual_subsolution (F : Cube State →o Cube State) (s : State) (t : ℝ) :
    (F.lfp s : ℝ) < t ↔ ∃ y : Cube State, y ≤ dual F y ∧ 1 - t < (y s : ℝ) := by
  constructor
  · intro h
    refine ⟨complement F.lfp, (dual_subsolution_iff _ _).2 ?_, ?_⟩
    · simpa only [complement_complement] using F.map_lfp.le
    · exact sub_lt_sub_left h 1
  · rintro ⟨y, hy, hs⟩
    have h := F.lfp_le ((dual_subsolution_iff _ _).1 hy) s
    change (F.lfp s : ℝ) ≤ 1 - (y s : ℝ) at h
    linarith

/-- A state has two available successors or two equiprobable successors. -/
inductive Row (State : Type*) where
  | lose
  | win
  | max (left right : State)
  | min (left right : State)
  | chance (left right : State)

def midpoint (a b : unitInterval) : unitInterval :=
  ⟨((a : ℝ) + b) / 2, by
    constructor <;> linarith [a.property.1, a.property.2, b.property.1, b.property.2]⟩

def Row.eval (row : Row State) (x : Cube State) : unitInterval :=
  match row with
  | .lose => 0
  | .win => 1
  | .max i j => Max.max (x i) (x j)
  | .min i j => Min.min (x i) (x j)
  | .chance i j => midpoint (x i) (x j)

theorem Row.eval_monotone (row : Row State) : Monotone row.eval := by
  intro x y h
  cases row with
  | lose | win => exact le_rfl
  | max i j => exact max_le_max (h i) (h j)
  | min i j => exact min_le_min (h i) (h j)
  | chance i j =>
    exact div_le_div_of_nonneg_right (add_le_add (h i) (h j)) (by norm_num : (0 : ℝ) ≤ 2)

def bellman (rows : State → Row State) : Cube State →o Cube State where
  toFun x s := (rows s).eval x
  monotone' _ _ h s := (rows s).eval_monotone h

def Row.swap : Row State → Row State
  | .lose => .win
  | .win => .lose
  | .max i j => .min i j
  | .min i j => .max i j
  | .chance i j => .chance i j

theorem Row.eval_swap (row : Row State) (y : Cube State) :
    row.swap.eval y = unitInterval.symm (row.eval (complement y)) := by
  cases row with
  | lose | win => simp [Row.swap, Row.eval]
  | max i j => simp [Row.swap, Row.eval, unitInterval.strictAnti_symm.antitone.map_max, complement]
  | min i j => simp [Row.swap, Row.eval, unitInterval.strictAnti_symm.antitone.map_min, complement]
  | chance i j =>
    apply Subtype.ext
    change ((y i : ℝ) + y j) / 2 = 1 - ((1 - (y i : ℝ)) + (1 - (y j : ℝ))) / 2
    linarith

theorem bellman_swap (rows : State → Row State) :
    bellman (fun s => (rows s).swap) = dual (bellman rows) :=
  OrderHom.ext _ _ (funext fun y => funext fun s => (rows s).eval_swap y)

/-- In the dual certificate, the original losing terminal has value one and the
original winning terminal has value zero. -/
def DualTerminalValues (rows : State → Row State) (y : Cube State) : Prop :=
  (∀ s, rows s = .lose → y s = 1) ∧ (∀ s, rows s = .win → y s = 0)

theorem complement_lfp_terminal_values (rows : State → Row State) :
    DualTerminalValues rows (complement (bellman rows).lfp) := by
  have h (s : State) : (rows s).eval (bellman rows).lfp = (bellman rows).lfp s :=
    congrFun (bellman rows).map_lfp s
  constructor <;> intro s hs <;> rw [complement, ← h s, hs] <;> simp [Row.eval]

theorem Row.eval_continuous (row : Row State) : Continuous row.eval := by
  have coord (s : State) : Continuous (fun x : Cube State => x s) := continuous_apply s
  cases row with
  | lose | win => exact continuous_const
  | max i j => exact (coord i).max (coord j)
  | min i j => exact (coord i).min (coord j)
  | chance i j =>
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp (coord i)).add
      (continuous_subtype_val.comp (coord j))).div_const 2

theorem bellman_continuous (rows : State → Row State) : Continuous (bellman rows) :=
  continuous_pi fun s => (rows s).eval_continuous

/-- Starting with the zero vector, one applies the terminal, choice and chance rows once
per iteration. Their supremum is the least Bellman fixed point. -/
theorem bellman_lfp_eq_iSup_iterate (rows : State → Row State) :
    (bellman rows).lfp = ⨆ n : ℕ, (bellman rows)^[n] ⊥ := by
  let F := bellman rows
  let u : Cube State := ⨆ n : ℕ, F^[n] ⊥
  have hlim : Tendsto (fun n : ℕ => F^[n] ⊥) atTop (𝓝 u) :=
    tendsto_atTop_iSup (F.monotone.monotone_iterate_of_le_map bot_le)
  have hstep : Tendsto (fun n : ℕ => F (F^[n] ⊥)) atTop (𝓝 u) := by
    simpa only [Function.comp_def, Function.iterate_succ_apply'] using
      hlim.comp (tendsto_add_atTop_nat 1)
  have hfixed : F u = u :=
    tendsto_nhds_unique ((bellman_continuous rows).continuousAt.tendsto.comp hlim) hstep
  refine le_antisymm (F.lfp_le hfixed.le) (iSup_le fun n => ?_)
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (F.monotone ih).trans F.map_lfp.le

/-- The order-theoretic value from the finite-horizon iterates satisfies the strict NO
certificate with the actual swapped terminal and Bellman rows. -/
theorem horizon_value_lt_iff (rows : State → Row State) (s : State) (t : ℝ) :
    (((⨆ n : ℕ, (bellman rows)^[n] ⊥) s : unitInterval) : ℝ) < t ↔
      ∃ y : Cube State, y ≤ bellman (fun j => (rows j).swap) y ∧ 1 - t < (y s : ℝ) := by
  rw [← bellman_lfp_eq_iSup_iterate, bellman_swap]
  exact lfp_lt_iff_dual_subsolution _ _ _

theorem horizon_value_lt_iff_fixed_terminals (rows : State → Row State) (s : State) (t : ℝ) :
    (((⨆ n : ℕ, (bellman rows)^[n] ⊥) s : unitInterval) : ℝ) < t ↔
      ∃ y : Cube State, DualTerminalValues rows y ∧
        y ≤ bellman (fun j => (rows j).swap) y ∧ 1 - t < (y s : ℝ) := by
  constructor
  · intro h
    rw [← bellman_lfp_eq_iSup_iterate] at h
    let F := bellman rows
    refine ⟨complement F.lfp, complement_lfp_terminal_values rows, ?_, sub_lt_sub_left h 1⟩
    rw [bellman_swap, dual_subsolution_iff, complement_complement]
    exact F.map_lfp.le
  · rintro ⟨y, _, hy, hs⟩
    exact (horizon_value_lt_iff rows s t).2 ⟨y, hy, hs⟩

end

end StochasticGames.Reachability
