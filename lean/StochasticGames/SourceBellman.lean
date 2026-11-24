module

public import StochasticGames.SourceGame
public import StochasticGames.ReachabilityThreshold
public import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith

/-! The Bellman operator for finite nonempty menus, with fixed terminal values at every horizon. -/

@[expose] public section

namespace StochasticGames.Source

noncomputable section

open Reachability (Cube midpoint)

variable {ι : Type*} {n : ℕ}

/-- Supply winning probabilities at both terminals, including at horizon zero. -/
def label (x : Cube ι) : Position ι → unitInterval
  | .inl i => x i
  | .inr true => 1
  | .inr false => 0

theorem label_mono {x y : Cube ι} (h : x ≤ y) (p : Position ι) : label x p ≤ label y p := by
  cases p with
  | inl i => exact h i
  | inr b => cases b <;> exact le_rfl

theorem label_continuous (p : Position ι) : Continuous (fun x : Cube ι => label x p) := by
  cases p with
  | inl i => exact continuous_apply i
  | inr b => cases b <;> exact continuous_const

def upper (f : Fin (n + 1) → unitInterval) : unitInterval :=
  Finset.univ.sup' Finset.univ_nonempty f

def lower (f : Fin (n + 1) → unitInterval) : unitInterval :=
  Finset.univ.inf' Finset.univ_nonempty f

theorem le_upper (f : Fin (n + 1) → unitInterval) (k) : f k ≤ upper f :=
  Finset.le_sup' f (Finset.mem_univ k)

theorem lower_le (f : Fin (n + 1) → unitInterval) (k) : lower f ≤ f k :=
  Finset.inf'_le f (Finset.mem_univ k)

theorem upper_le_iff {f : Fin (n + 1) → unitInterval} {v} :
    upper f ≤ v ↔ ∀ k, f k ≤ v := by simp [upper]

theorem lower_le_iff {f : Fin (n + 1) → unitInterval} {v} :
    lower f ≤ v ↔ ∃ k, f k ≤ v := by simp [lower]

def argUpper (f : Fin (n + 1) → unitInterval) : Fin (n + 1) :=
  (Finset.exists_mem_eq_sup' Finset.univ_nonempty f).choose

def argLower (f : Fin (n + 1) → unitInterval) : Fin (n + 1) :=
  (Finset.exists_mem_eq_inf' Finset.univ_nonempty f).choose

theorem apply_argUpper (f : Fin (n + 1) → unitInterval) :
    f (argUpper f) = upper f :=
  (Finset.exists_mem_eq_sup' Finset.univ_nonempty f).choose_spec.2.symm

theorem apply_argLower (f : Fin (n + 1) → unitInterval) :
    f (argLower f) = lower f :=
  (Finset.exists_mem_eq_inf' Finset.univ_nonempty f).choose_spec.2.symm

/-- The index distinguishes occurrences even if different moves have the same successor. -/
abbrev move {α : Type*} (head : α) (tail : List α) (k : Fin (tail.length + 1)) : α :=
  (head :: tail).get k

def Row.eval (row : Row ι) (x : Cube ι) : unitInterval :=
  match row with
  | .max head tail => upper (fun k => label x (move head tail k))
  | .min head tail => lower (fun k => label x (move head tail k))
  | .chance left right => midpoint (label x left) (label x right)

theorem midpoint_mono {a b c d : unitInterval} (h : a ≤ c) (h' : b ≤ d) :
    midpoint a b ≤ midpoint c d := by
  change ((a : ℝ) + b) / 2 ≤ ((c : ℝ) + d) / 2
  exact div_le_div_of_nonneg_right (add_le_add (show (a : ℝ) ≤ c from h) h') (by norm_num)

theorem Row.eval_monotone (row : Row ι) : Monotone row.eval := by
  intro x y h
  cases row with
  | max head tail =>
    exact upper_le_iff.2 fun k =>
      (label_mono h _).trans (le_upper (fun j => label y (move head tail j)) k)
  | min head tail =>
    exact Finset.le_inf' Finset.univ_nonempty _ fun k _ =>
      (lower_le (fun j => label x (move head tail j)) k).trans (label_mono h _)
  | chance left right => exact midpoint_mono (label_mono h _) (label_mono h _)

theorem Row.eval_continuous (row : Row ι) : Continuous row.eval := by
  cases row with
  | max head tail =>
    exact Continuous.finset_sup'_apply (Finset.univ_nonempty (α := Fin (tail.length + 1)))
      fun k _ => label_continuous (move head tail k)
  | min head tail =>
    exact Continuous.finset_inf'_apply (Finset.univ_nonempty (α := Fin (tail.length + 1)))
      fun k _ => label_continuous (move head tail k)
  | chance left right =>
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp (label_continuous left)).add
      (continuous_subtype_val.comp (label_continuous right))).div_const 2

def bellman (rows : ι → Row ι) : Cube ι →o Cube ι where
  toFun x i := (rows i).eval x
  monotone' _ _ h i := (rows i).eval_monotone h

def iterate (rows : ι → Row ι) (n : ℕ) : Cube ι := (bellman rows)^[n] ⊥

@[simp] theorem iterate_zero (rows : ι → Row ι) : iterate rows 0 = ⊥ := rfl

theorem iterate_succ (rows : ι → Row ι) (n) :
    iterate rows (n+1) = bellman rows (iterate rows n) :=
  Function.iterate_succ_apply' _ _ _

theorem lfp_eq_iSup_iterate (rows : ι → Row ι) :
    (bellman rows).lfp = ⨆ n : ℕ, iterate rows n :=
  Reachability.lfp_eq_iSup_iterate_of_continuous _ (continuous_pi fun i => (rows i).eval_continuous)

theorem dualLabel_complement (x : Cube ι) (p : Position ι) :
    dualLabel (fun i => 1 - (x i : ℝ)) p = 1 - (label x p : ℝ) := by
  cases p with
  | inl i => rfl
  | inr b => cases b <;> simp [dualLabel, label]

theorem Row.eval_le_iff_dualConstraint (row : Row ι) (x : Cube ι) (i : ι) :
    row.eval x ≤ x i ↔ row.DualConstraint (fun j => 1 - (x j : ℝ)) i := by
  have reverse (p : Position ι) :
      (label x p ≤ x i) ↔ 1 - (x i : ℝ) ≤ dualLabel (fun j => 1 - (x j : ℝ)) p := by
    rw [dualLabel_complement]
    exact (sub_le_sub_iff_left (1 : ℝ)).symm
  cases row with
  | max head tail =>
    change upper _ ≤ _ ↔ ∀ j ∈ head :: tail, _
    rw [upper_le_iff]
    constructor
    · intro h j hj
      obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hj
      exact (reverse _).mp (h k)
    · intro h k
      exact (reverse _).mpr (h _ (List.get_mem (head :: tail) k))
  | min head tail =>
    change lower _ ≤ _ ↔ ∃ j ∈ head :: tail, _
    rw [lower_le_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨_, List.get_mem (head :: tail) k, (reverse _).mp hk⟩
    · rintro ⟨j, hj, h⟩
      obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hj
      exact ⟨k, (reverse _).mpr h⟩
  | chance left right =>
    change ((label x left : ℝ) + label x right) / 2 ≤ x i ↔ 1 - (x i : ℝ) ≤ (_ + _) / 2
    rw [dualLabel_complement, dualLabel_complement]
    constructor <;> intro h <;> linarith

theorem prefixed_iff_dualFeasible (rows : ι → Row ι) (x : Cube ι) :
    bellman rows x ≤ x ↔ DualFeasible rows (fun i => 1 - (x i : ℝ)) := by
  constructor
  · intro h
    exact ⟨fun i => ⟨sub_nonneg.mpr (x i).property.2, sub_le_self _ (x i).property.1⟩,
      fun i => ((rows i).eval_le_iff_dualConstraint x i).mp (h i)⟩
  · intro h i
    exact ((rows i).eval_le_iff_dualConstraint x i).mpr (h.2 i)

end

end StochasticGames.Source
