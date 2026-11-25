module

public import Kintali.QuotaSweep.KeyTable
public import Kintali.TrialWork.Arithmetic

/-! # Addressed construction of the ordinal rows of a supplied sparse inventory -/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open Kintali.ExactRecovery
open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {V T X : Type}

def count (less : X → X → Run Bool) (limit : X) : List (T × X) → Run ℕ
  | [] => step 0 0
  | (t,x)::xs => do
    let cell ← step 0 (t,x)
    let hit ← less cell.2 limit
    let n ← count less limit xs
    if hit then natAdd n 1 else step 0 n

theorem count_value (less : X → X → Run Bool) (limit : X) (xs : List (T × X)) :
    (count less limit xs).value = xs.countP (fun e => (less e.2 limit).value) := by
  induction xs with
  | nil => rfl
  | cons item xs ih =>
    rcases item with ⟨t,x⟩
    cases h : (less x limit).value <;> simp [count,natAdd,h,ih]

theorem count_work (less : X → X → Run Bool) (limit : X) (xs : List (T × X)) {c w : ℕ}
    (each : ∀ e ∈ xs, (less e.2 limit).Bound c w) (width : xs.length.size+1 ≤ w) :
    (count less limit xs).Bound (1+xs.length*(c+2)) w := by
  induction xs with
  | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
  | cons item xs ih =>
    obtain ⟨t,x⟩ := item
    have tailW := Nat.succ_le_succ (Nat.size_le_size (Nat.le_succ xs.length))
    have tail := ih (fun e he => each e (by simp [he])) (tailW.trans width)
    have cmp := each (t,x) List.mem_cons_self
    have small : (count less limit xs).value.size ≤ w := by
      rw [count_value]
      exact (Nat.size_le_size List.countP_le_length).trans ((Nat.le_succ _).trans (tailW.trans width))
    have one : (1:ℕ).size ≤ w := by
      change 1 ≤ w
      omega
    cases h : (less x limit).value <;>
      simp only [count,Run.Bound,Run.bind_slots,Run.bind_width,step_width,step_slots,
        step_value,h,Bool.false_eq_true,↓reduceIte,natAdd,List.length_cons,Nat.add_mul,
        Nat.one_mul] at * <;> omega

def fed (f : T → Run X) (e : T) : Run (T × X) := do
  let v ← f e
  step 0 (e,v)

def row (less : X → X → Run Bool) (f : T → Run X) (records : List T) : Run (List (T × ℕ)) := do
  let keys ← StochasticGames.CompilerRun.mapM (fed f) records
  StochasticGames.CompilerRun.mapM (fun e => do
    let n ← count less e.2 keys
    step 0 (e.1,n)) keys

theorem row_value [LinearOrder X] (less : X → X → Run Bool)
    (ok : ∀ x y, (less x y).value = decide (x<y)) (f : T → Run X) (records : List T) :
    (row less f records).value = Sparse.ordinals (Sparse.keyed records (fun e => (f e).value)) := by
  simp [row,fed,count_value,ok,Sparse.ordinals,Sparse.keyed]

def rowSlots (r k c : ℕ) := (r*(k+3)+1)+(r*((1+r*(c+2))+3)+1)

theorem row_work (less : X → X → Run Bool) (f : T → Run X) (records : List T) {k c w : ℕ}
    (each : ∀ e ∈ records, (f e).Bound k w)
    (cmp : ∀ e ∈ records, ∀ q ∈ records, (less (f e).value (f q).value).Bound c w)
    (width : records.length.size+1 ≤ w) : (row less f records).Bound (rowSlots records.length k c) w := by
  let keys := (StochasticGames.CompilerRun.mapM (fed f) records).value
  have desc : keys = records.map (fun e => (e,(f e).value)) := by simp [keys,fed]
  have len : keys.length = records.length := by simp [desc]
  have data := mapM_bound (fed f) records (k+1) w (fun e he =>
    bound_bind (each e he) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))
  have entries := mapM_bound (fun e : T × X => do
    let n ← count less e.2 keys
    step 0 (e.1,n)) keys ((1+records.length*(c+2))+1) w (by
      intro e he
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (desc ▸ he)
      apply bound_bind
      · rw [← len]
        apply count_work
        · intro b hb
          obtain ⟨q,hq,rfl⟩ := List.mem_map.mp (desc ▸ hb)
          exact cmp _ hq _ ha
        · simpa only [len] using width
      · exact (bound_step 0 _).weaken le_rfl (Nat.zero_le _))
  rw [len] at entries
  exact bound_bind data entries

def table (vs : List V) (rs : List T) (make : V → T → Run X) (less : X → X → Run Bool) :
    Run (List (V × List (T × ℕ))) :=
  StochasticGames.CompilerRun.mapM (fun v => do
    let r ← row less (make v) rs
    step 0 (v,r)) vs

def slots (v r k c : ℕ) := v*(rowSlots r k c+3)+1

theorem table_value [LinearOrder X] (vs : List V) (rs : List T) (make : V → T → Run X)
    (less : X → X → Run Bool) (ok : ∀ x y, (less x y).value = decide (x<y)) :
    (table vs rs make less).value =
      vs.map (fun v => (v,Sparse.ordinals (Sparse.keyed rs (fun e => (make v e).value)))) := by
  simp [table,row_value less ok]

theorem table_bound (vs : List V) (rs : List T) (make : V → T → Run X) (less : X → X → Run Bool)
    {k c w : ℕ} (keys : ∀ v ∈ vs, ∀ e ∈ rs, (make v e).Bound k w)
    (cmps : ∀ v ∈ vs, ∀ e ∈ rs, ∀ q ∈ rs, (less (make v e).value (make v q).value).Bound c w)
    (width : rs.length.size+1 ≤ w) : (table vs rs make less).Bound (slots vs.length rs.length k c) w :=
  mapM_bound _ _ (rowSlots rs.length k c+1) w (fun v hv =>
    bound_bind (row_work less (make v) rs (keys v hv) (cmps v hv) width)
      ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))

end Kintali.QuotaSweep.RankRun
