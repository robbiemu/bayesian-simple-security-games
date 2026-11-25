module

public import StochasticGames.CompilerRun
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! # Charged lists for sparse inventory construction -/

@[expose] public section

namespace Kintali.TrialWork.ListBuild

open StochasticGames.CompilerRun

variable {α : Type}

def retain (test : α → Run Bool) : List α → Run (List α)
  | [] => step 0 []
  | x::xs => do
    let keep ← test x
    let tail ← retain test xs
    step 0 (if keep then x::tail else tail)

@[simp] theorem retain_value (test : α → Run Bool) (xs : List α) :
    (retain test xs).value = xs.filter (fun x => (test x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (test x).value <;> simp [retain, h, ih]

theorem retain_work (test : α → Run Bool) (xs : List α) {c w : ℕ}
    (each : ∀ x ∈ xs, (test x).Bound c w) :
    (retain test xs).Bound (1+xs.length*(c+1)) w := by
  induction xs with
  | nil => simp [retain,Run.Bound]
  | cons x xs ih =>
    obtain ⟨s,w'⟩ := each x (by simp)
    obtain ⟨s',w''⟩ := ih (fun x' hx => each x' (by simp [hx]))
    constructor
    · simp only [retain, Run.bind_slots, step_slots, List.length_cons, Nat.succ_mul]
      omega
    · exact max_le w' (max_le w'' (Nat.zero_le _))

def insert (comparison : α → α → Run Ordering) (x : α) : List α → Run (List α)
  | [] => step 0 [x]
  | y::ys => do
    let order ← comparison x y
    match ← step 0 order with
    | .lt => step 0 (x::y::ys)
    | .eq => step 0 (y::ys)
    | .gt => do
      let tail ← insert comparison x ys
      step 0 (y::tail)

theorem insert_length (comparison : α → α → Run Ordering) (x : α) (ys : List α) :
    (insert comparison x ys).value.length ≤ ys.length+1 := by
  induction ys with
  | nil => simp [insert]
  | cons y ys ih =>
    cases hc : (comparison x y).value with
    | lt => simp [insert, hc]
    | eq => simp [insert, hc]
    | gt => simpa [insert, hc] using Nat.succ_le_succ ih

theorem insert_work (comparison : α → α → Run Ordering) (x : α) (ys : List α) {c w : ℕ}
    (each : ∀ y, (comparison x y).Bound c w) :
    (insert comparison x ys).Bound (1+ys.length*(c+2)) w := by
  induction ys with
  | nil => simp [insert,Run.Bound]
  | cons y ys ih =>
    obtain ⟨s,sw⟩ := each y
    obtain ⟨t,tw⟩ := ih
    cases hc : (comparison x y).value <;>
      constructor <;>
      simp [insert, hc, List.length_cons, Nat.succ_mul, max_le_iff, sw, tw] <;>
      omega

def sortedSet (comparison : α → α → Run Ordering) : List α → Run (List α)
  | [] => step 0 []
  | x::xs => do
    let ys ← sortedSet comparison xs
    let _ ← step 0 ()
    insert comparison x ys

theorem sortedSet_length (comparison : α → α → Run Ordering) (xs : List α) :
    (sortedSet comparison xs).value.length ≤ xs.length := by
  induction xs with
  | nil => simp [sortedSet]
  | cons x xs ih =>
    exact (insert_length comparison x (sortedSet comparison xs).value).trans (Nat.succ_le_succ ih)

theorem sortedSet_work (comparison : α → α → Run Ordering) (xs : List α) {c w : ℕ}
    (each : ∀ x y, (comparison x y).Bound c w) :
    (sortedSet comparison xs).Bound (1+xs.length*(xs.length+1)*(c+4)) w := by
  induction xs with
  | nil => simp [sortedSet,Run.Bound]
  | cons x xs ih =>
    have remaining := sortedSet_length comparison xs
    obtain ⟨s,sw⟩ := ih
    obtain ⟨t,tw⟩ := insert_work comparison x (sortedSet comparison xs).value (each x)
    have bound := Nat.mul_le_mul_right (c+2) remaining
    constructor
    · simp only [sortedSet, Run.bind_slots, step_slots, List.length_cons]
      have hs : xs.length*(xs.length+1)*(c+4)+xs.length*(c+2)+2 ≤
          (xs.length+1)*(xs.length+2)*(c+4) := by
        calc
          _ ≤ xs.length*((xs.length+1)*(c+4)) + (xs.length+2)*(c+4) := by
            rw [← Nat.mul_assoc]
            have z : xs.length*(c+2) ≤ xs.length*(c+4) :=
              Nat.mul_le_mul_left _ (by omega)
            rw [Nat.add_mul]
            omega
          _ ≤ _ := by
            rw [show (xs.length+1)*(xs.length+2)*(c+4) =
              xs.length*((xs.length+2)*(c+4)) + (xs.length+2)*(c+4) by ring]
            gcongr
            decide
      simp only [show xs.length+1+1 = xs.length+2 by omega]
      omega
    · exact max_le sw (max_le (Nat.zero_le _) tw)

section Ordered

variable [LinearOrder α] (comparison : α → α → Run Ordering)
variable (same : ∀ x y, (comparison x y).value = compare x y)

include same

theorem insert_mem (x v : α) (ys : List α) :
    v ∈ (insert comparison x ys).value ↔ v = x ∨ v ∈ ys := by
  induction ys with
  | nil => simp [insert]
  | cons y ys ih =>
    cases hc : compare x y with
    | lt => simp [insert, same, hc]
    | eq =>
      have eq := compare_eq_iff_eq.mp hc
      simp [insert, same, eq]
    | gt =>
      simp [insert, same, hc, ih, or_left_comm]

theorem insert_sorted (x : α) (ys : List α) (ordered : ys.Pairwise (· < ·)) :
    (insert comparison x ys).value.Pairwise (· < ·) := by
  induction ys with
  | nil => simp [insert]
  | cons y ys ih =>
    obtain ⟨first, after⟩ := List.pairwise_cons.mp ordered
    cases hc : compare x y with
    | lt =>
      have less := compare_lt_iff_lt.mp hc
      simp only [insert, Run.bind_value, same, hc, step_value]
      exact List.pairwise_cons.mpr ⟨fun v hv =>
        (List.mem_cons.mp hv).elim (fun eq => eq ▸ less) (fun inTail => less.trans (first v inTail)),
        ordered⟩
    | eq => simpa [insert, same, hc] using ordered
    | gt =>
      simp only [insert, Run.bind_value, same, hc, step_value]
      exact List.pairwise_cons.mpr ⟨fun v hv =>
        ((insert_mem comparison same x v ys).mp hv).elim
          (fun eq => eq ▸ compare_gt_iff_gt.mp hc) (fun inTail => first v inTail),
        ih after⟩

theorem sortedSet_spec (xs : List α) :
    (sortedSet comparison xs).value.Pairwise (· < ·) ∧
      ∀ v, v ∈ (sortedSet comparison xs).value ↔ v ∈ xs := by
  induction xs with
  | nil => simp [sortedSet]
  | cons x xs ih =>
    refine ⟨insert_sorted comparison same x _ ih.1, fun v => ?_⟩
    simp [sortedSet, insert_mem comparison same, ih.2]

theorem sortedSet_value (xs : List α) :
    (sortedSet comparison xs).value = xs.toFinset.sort (· ≤ ·) := by
  obtain ⟨left,mem⟩ := sortedSet_spec comparison same xs
  have s : (xs.toFinset.sort (· ≤ ·)).Pairwise (· < ·) := xs.toFinset.sortedLT_sort.pairwise
  have perm : List.Perm (sortedSet comparison xs).value (xs.toFinset.sort (· ≤ ·)) :=
    (List.perm_ext_iff_of_nodup (left.imp (fun h => h.ne))
      (s.imp (fun h => h.ne))).mpr fun z => by simp [mem]
  exact perm.eq_of_pairwise' (left.imp (fun h => h.le)) (s.imp (fun h => h.le))

end Ordered

end Kintali.TrialWork.ListBuild
