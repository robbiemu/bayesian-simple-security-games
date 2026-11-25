module

public import Kintali.InputOutput.DirectWorkPlan
import all Init.Data.List.MinMaxOn

/-! # Computing the pure best response at the selected defense endpoints -/

@[expose] public section
namespace Kintali.InputOutput.DirectWork

open Binary ContactSize StochasticGames.CompilerRun StochasticGames.BinarySize

def member {m : ℕ} (j : Fin m) : List (Fin m) → Run Bool
  | [] => step 0 false
  | k::ks => do
    let eq ← step (max j.val.size k.val.size) (j == k)
    if eq then step 0 true else member j ks

@[simp] theorem member_value {m : ℕ} (j : Fin m) (ks : List (Fin m)) :
    (member j ks).value = decide (j ∈ ks) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => by_cases e : j = k <;> simp [member,ih,e]

theorem member_work {m S : ℕ} (j : Fin m) (ks : List (Fin m)) (dim : m ≤ S) :
    (member j ks).Bound (ks.length+1) (width S) := by
  induction ks with
  | nil => exact (bound_step _ _).weaken le_rfl (Nat.zero_le _)
  | cons k ks ih =>
    have js := (size_le_self j.val).trans (j.isLt.le.trans dim)
    have is := (size_le_self k.val).trans (k.isLt.le.trans dim)
    by_cases h : j = k <;> simp [member,h,Run.Bound,width] at * <;> omega

def endpoint (a : Input) (d : List (Fin a.targets)) (i : Fin a.types) (j : Fin a.targets) : Run ℚ := do
  let p ← offer a i j
  let b ← member j d
  step 0 (if b then p.2 else p.1)

@[simp] theorem endpoint_value (a : Input) (d : List (Fin a.targets)) (i : Fin a.types) (j : Fin a.targets) :
    (endpoint a d i j).value = if j ∈ d then (a.attack i j).2 else (a.attack i j).1 := by
  simp [endpoint]

theorem endpoint_fits (a : Input) (v : a.Valid) (d : List (Fin a.targets)) (i : Fin a.types) (j : Fin a.targets) :
    Fits (lengthInput a) (endpoint a d i j).value := by
  rw [endpoint_value]
  split <;> first | exact (offer_fits a v i j).2 | exact (offer_fits a v i j).1

theorem endpoint_work (a : Input) (d : List (Fin a.targets)) (fit : d.length ≤ lengthInput a)
    (i : Fin a.types) (j : Fin a.targets) : (endpoint a d i j).Bound (3*lengthInput a+4) (width (lengthInput a)) := by
  have o := offer_work a i j
  have h := member_work j d (dimensions a).1
  simp only [endpoint,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width] at *
  omega

def coverage (a : Input) (j : Fin a.targets) : ℚ := if j ∈ a.game.earlyDefense then 1 else 0

theorem endpoint_cost (a : Input) (i : Fin a.types) (j : Fin a.targets) :
    a.game.cost i j (coverage a j) = -(endpoint a (chosen a) i j).value := by
  rw [a.cost_eq,endpoint_value]
  by_cases h : j ∈ a.game.earlyDefense <;> simp [coverage,Input.utility,chosen_mem,h]

/-- Retain the incumbent unless the challenger has strictly greater payoff. -/
def advance (a : Input) (d : List (Fin a.targets)) (i : Fin a.types) (j k : Fin a.targets) : Run (Fin a.targets) := do
  let old ← endpoint a d i j
  let new ← endpoint a d i k
  let better ← less old new
  step 0 (if better then k else j)

theorem advance_value (a : Input) (i : Fin a.types) (j k : Fin a.targets) :
    (advance a (chosen a) i j k).value = minOn (fun t => a.game.cost i t (coverage a t)) j k := by
  simp only [advance,Run.bind_value,less_value,step_value,minOn_eq_ite,endpoint_cost,neg_le_neg_iff,decide_eq_true_eq]
  split <;> rename_i h
  · rw [ite_eq_right (not_le.mpr h)]
  · rw [ite_eq_left (le_of_not_gt h)]

theorem advance_work (a : Input) (v : a.Valid) (i : Fin a.types) (j k : Fin a.targets) :
    (advance a (chosen a) i j k).Bound (6*lengthInput a+12) (width (lengthInput a)) := by
  have e := endpoint_work a _ (chosen_length a v) i j
  have f := endpoint_work a _ (chosen_length a v) i k
  have l := less_work _ _ (endpoint_fits a v (chosen a) i j) (endpoint_fits a v (chosen a) i k)
  simp only [advance,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width] at *
  omega

def scan (a : Input) (d : List (Fin a.targets)) (i : Fin a.types) :
    Fin a.targets → List (Fin a.targets) → Run (Fin a.targets)
  | j, [] => step 0 j
  | j, k::ks => do
    let best ← advance a d i j k
    scan a d i best ks

theorem scan_value (a : Input) (i : Fin a.types) (j : Fin a.targets) (ks : List (Fin a.targets)) :
    (scan a (chosen a) i j ks).value = ks.foldl (minOn (fun t => a.game.cost i t (coverage a t))) j := by
  induction ks generalizing j with
  | nil => rfl
  | cons k ks ih => simp [scan,ih,advance_value]

theorem scan_work (a : Input) (v : a.Valid) (i : Fin a.types) (j : Fin a.targets) (ks : List (Fin a.targets)) :
    (scan a (chosen a) i j ks).Bound (ks.length*(6*lengthInput a+12)+1) (width (lengthInput a)) := by
  induction ks generalizing j with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons k ks ih =>
    have h := advance_work a v i j k
    have t := ih (advance a (chosen a) i j k).value
    simp only [scan,Run.Bound,Run.bind_slots,Run.bind_width,List.length_cons,Nat.succ_mul] at *
    omega

def best (a : Input) (d : List (Fin a.targets)) (i : Fin a.types) : List (Fin a.targets) → Run (Option (Fin a.targets))
  | [] => step 0 none
  | k::ks => do
    let b ← scan a d i k ks
    step 0 (some b)

theorem best_value (a : Input) (hm : 0 < a.targets) (i : Fin a.types) :
    (best a (chosen a) i (List.finRange a.targets)).value = some (a.game.bestTarget hm (coverage a) i) := by
  have aux (js : List (Fin a.targets)) (ne : js ≠ []) :
      (best a (chosen a) i js).value = some (js.minOn (fun t => a.game.cost i t (coverage a t)) ne) := by
    cases js with
    | nil => contradiction
    | cons j js => simp [best,scan_value,List.minOn]
  exact aux _ (List.ne_nil_of_mem (List.mem_finRange ⟨0,hm⟩))

theorem best_work (a : Input) (v : a.Valid) (i : Fin a.types) {js : List (Fin a.targets)}
    (h : js.length ≤ lengthInput a) :
    (best a (chosen a) i js).Bound (lengthInput a*(6*lengthInput a+12)+2) (width (lengthInput a)) := by
  cases js with
  | nil => exact (bound_step _ _).weaken (by omega) (Nat.zero_le _)
  | cons j js =>
    have fit : js.length ≤ lengthInput a := by simpa using (Nat.le_trans (Nat.le_succ js.length) h)
    have s := (scan_work a v i j js).weaken (Nat.add_le_add_right (Nat.mul_le_mul_right _ fit) 1) le_rfl
    simp only [best,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width] at *
    omega

end Kintali.InputOutput.DirectWork
