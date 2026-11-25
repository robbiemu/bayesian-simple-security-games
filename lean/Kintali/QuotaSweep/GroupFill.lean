module

public import Kintali.QuotaSweep.Contact
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Descending fill of a grouped private buyer

Split a purchase `p` among identical masses `w` in site-priority order.
The differences of successive capped prefix masses telescope. If a lower
position receives anything, every earlier position is full.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Grouping

def fill (w p : ℚ) (k : ℕ) : ℚ := min ((k+1 : ℕ)*w) p - min ((k : ℚ)*w) p

theorem fill_nonneg {w : ℚ} (hw : 0 ≤ w) (p : ℚ) (k : ℕ) : 0 ≤ fill w p k := by
  apply sub_nonneg.mpr (min_le_min_right _ ?_)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hw

theorem fill_le {w : ℚ} (hw : 0 ≤ w) (p : ℚ) (k : ℕ) : fill w p k ≤ w := by
  simp only [fill, Nat.cast_add, Nat.cast_one, add_mul, one_mul, min_def]
  split_ifs <;> linarith

theorem prior_full {w p : ℚ} {i j : ℕ} (hw : 0 ≤ w) (hij : i < j)
    (hpos : 0 < fill w p j) : fill w p i = w := by
  have hlow : (j : ℚ)*w < p := by
    by_contra! hn
    rw [fill, min_eq_right hn] at hpos
    exact (not_lt_of_ge (min_le_right _ _)) (sub_pos.mp hpos)
  have hnext : ((i+1 : ℕ) : ℚ)*w ≤ (j : ℚ)*w :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hw
  have hprev : (i : ℚ)*w ≤ ((i+1 : ℕ) : ℚ)*w :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hw
  rw [fill, min_eq_left (hnext.trans hlow.le), min_eq_left (hprev.trans (hnext.trans hlow.le))]
  push_cast
  ring

theorem prefix_sum {w p : ℚ} (hp : 0 ≤ p) (n : ℕ) :
    (∑ k ∈ Finset.range n, fill w p k) = min ((n : ℚ)*w) p := by
  induction n with
  | zero => simp [min_eq_left hp]
  | succ n ih => rw [Finset.sum_range_succ, ih, fill]; abel

theorem group_sum {w p : ℚ} {n : ℕ} (hp : 0 ≤ p) (hn : p ≤ (n : ℚ)*w) :
    (∑ k : Fin n, fill w p k.val) = p := by
  rw [Fin.sum_univ_eq_sum_range (fun k => fill w p k), prefix_sum hp, min_eq_right hn]

theorem outside_sum {w p : ℚ} {n : ℕ} (hp : 0 ≤ p) (hn : p ≤ (n : ℚ)*w) :
    (∑ k : Fin n, (w - fill w p k.val)) = (n : ℚ)*w - p := by
  simp [Finset.sum_sub_distrib, group_sum hp hn]

/-- A finite partition with members numbered from highest to lowest
site priority. Empty groups are permitted. -/
structure Partition (F H : Type*) where
  size : H → ℕ
  enumerate : F ≃ (h : H) × Fin (size h)

namespace Partition

variable {F H : Type*} (P : Partition F H)

def group (f : F) : H := (P.enumerate f).1

def index (f : F) : ℕ := (P.enumerate f).2.val

/-- Sum any function on the fine records by grouped buyer and rank. -/
theorem sum_fibers {A : Type*} [AddCommMonoid A] [Fintype F] [Fintype H] (f : F → A) :
    (∑ u, f u) = ∑ h : H, ∑ k : Fin (P.size h), f (P.enumerate.symm ⟨h,k⟩) := by
  calc
    _ = ∑ a : (h : H) × Fin (P.size h), f (P.enumerate.symm a) := (P.enumerate.symm.sum_comp f).symm
    _ = _ := Fintype.sum_sigma _

@[simp] theorem group_symm (h : H) (k : Fin (P.size h)) :
    P.group (P.enumerate.symm ⟨h,k⟩) = h := by simp [group]

@[simp] theorem index_symm (h : H) (k : Fin (P.size h)) :
    P.index (P.enumerate.symm ⟨h,k⟩) = k.val := by unfold index; rw [P.enumerate.apply_symm_apply]

end Partition
end Kintali.QuotaSweep.Grouping
