module

public import Kintali.InputOutput.NormalizedFields

/-! # Enumerating the finite rational data used by exact recovery -/

@[expose] public section
namespace Kintali.InputOutput.DatumWork

open Binary NormalizedWork TrialWork ContactSize ExactRecovery StochasticGames.CompilerRun StochasticGames.BinarySize
variable {k m : ℕ}

def pair (d : Fields k m) (i : Fin k) (j : Fin m) : Run (List ℚ) := do
  let a ← d.intercept i j
  let b ← d.slope i j
  let tail ← step 0 [b]
  step 0 (a::tail)

def bidRow (d : Fields k m) (js : List (Fin m)) (i : Fin k) := flatMapM (pair d i) js

def enumerate (d : Fields k m) : Run (List ℚ) := do
  let js ← finRange m
  let is ← finRange k
  let priors ← StochasticGames.CompilerRun.mapM d.prior is
  let gains ← StochasticGames.CompilerRun.mapM d.gain js
  let bids ← flatMapM (bidRow d js) is
  let x ← StochasticGames.CompilerRun.append gains bids
  let y ← StochasticGames.CompilerRun.append priors x
  let r ← step (d.budget.size+1) (d.budget : ℚ)
  let z ← step 0 (r::y)
  step 0 (1::z)

def elements (d : Fields k m) :=
  (1 : ℚ) :: (d.game.resources : ℚ) :: ((List.ofFn d.game.prior) ++ (List.ofFn d.game.gain) ++
    (List.finRange k).flatMap (fun i => (List.finRange m).flatMap (fun j => [d.game.intercept i j,d.game.slope i j])))

theorem enumerate_value (d : Fields k m) : (enumerate d).value = elements d := by
  simp only [enumerate,elements,Run.bind_value,finRange_value,mapM_value,flatMapM_value,append_value,
    bidRow,pair,step_value,List.ofFn_eq_map,List.append_assoc]
  rfl

theorem elements_set (d : Fields k m) : (elements d).toFinset = data d.game := by
  ext q
  simp only [elements,List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_ofFn,List.mem_flatMap,
    List.mem_finRange,true_and,List.not_mem_nil,or_false,data,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_image,Finset.mem_univ,Prod.exists]
  aesop

@[simp] theorem row_length (d : Fields k m) (js : List (Fin m)) (i : Fin k) : (bidRow d js i).value.length = 2*js.length := by
  simp [bidRow,pair,List.length_flatMap,List.map_const',Nat.mul_comm]

theorem elements_length (d : Fields k m) : (elements d).length = 2+k+m+2*k*m := by
  simp [elements,List.length_flatMap,List.map_const']
  ring

theorem cell_work (d : Fields k m) {c w : ℕ} (h : FieldBound d c w) (i : Fin k) (j : Fin m) :
    (pair d i j).Bound (2*c+2) w := by
  have a := (h.intercept i j).1
  have b := (h.slope i j).1
  simp [pair,Run.Bound] at *
  omega

def listBound (S : ℕ) := 2+S+S+2*S*S
def rowSlots (S c : ℕ) := S*(2*c+6)+1
def enumSlots (S c : ℕ) := 2*(2*S+1)+2*(S*(c+2)+1)+(S*(rowSlots S c+2*S+2)+1)+2*(S+1)+3

theorem enumerate_work (d : Fields k m) {c w S : ℕ} (h : FieldBound d c w) (kd : k ≤ S) (md : m ≤ S)
    (budget : d.budget.size+1 ≤ w) : (enumerate d).Bound (enumSlots S c) w := by
  let is := List.finRange k
  let js := List.finRange m
  have klen : is.length ≤ S := by simpa [is] using kd
  have mlen : js.length ≤ S := by simpa [js] using md
  have unary {n : ℕ} (f : Fin n → Run ℚ) (lim : n ≤ S) (hf : ∀ i, (f i).Bound c w) :
      (StochasticGames.CompilerRun.mapM f (List.finRange n)).Bound (S*(c+2)+1) w := by
    exact (mapM_bound _ _ _ _ (fun i _ => hf i)).weaken (by simp; gcongr) le_rfl
  have prior := unary d.prior kd fun i => (h.prior i).1
  have gain := unary d.gain md fun j => (h.gain j).1
  have row (i : Fin k) : (bidRow d js i).Bound (rowSlots S c) w := by
    apply (flatMapM_bound _ js (2*c+2) 2 w (fun j _ => cell_work d h i j) (fun j _ => by simp [pair])).weaken _ le_rfl
    unfold rowSlots
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ mlen) 1
  have bids := (flatMapM_bound _ is (rowSlots S c) (2*S) w (fun i _ => row i) (fun i _ =>
    (row_length d js i).le.trans (Nat.mul_le_mul_left 2 mlen))).weaken
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ klen) 1) le_rfl
  let p := (StochasticGames.CompilerRun.mapM d.prior is).value
  let g := (StochasticGames.CompilerRun.mapM d.gain js).value
  let b := (flatMapM (bidRow d js) is).value
  have pl : p.length ≤ S := by simpa [p] using klen
  have gl : g.length ≤ S := by simpa [g] using mlen
  have ga := append_bound g b w
  have pa := append_bound p (g++b) w
  have ix := finRange_bound k
  have jx := finRange_bound m
  have iw := h.kSize
  have jw := h.mSize
  simp only [enumerate,Run.Bound,Run.bind_slots,Run.bind_width,finRange_value,step_slots,step_width,
    append_value,enumSlots] at *
  dsimp only [p,g,b,is,js] at *
  omega

def contains (q : ℚ) : List ℚ → Run Bool
  | [] => step 0 false
  | x::xs => do
    let eq ← eqRat q x
    if eq then step 0 true else contains q xs

@[simp] theorem contains_value (q : ℚ) (xs : List ℚ) : (contains q xs).value = decide (q ∈ xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases e : q = x <;> simp [contains,ih,e]

theorem contains_work {q : ℚ} {w : ℕ} (small : Fits w q) (xs : List ℚ) (fit : ∀ x ∈ xs, Fits w x) :
    (contains q xs).Bound (4*xs.length+1) (scalarWidth w) := by
  induction xs with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons x xs ih =>
    have test := eqRat_work small (fit x (by simp))
    have tail := ih (fun z hz => fit z (List.mem_cons_of_mem _ hz))
    by_cases h : q = x <;> simp [contains,Run.Bound,h] at * <;> omega

def unique : List ℚ → Run (List ℚ)
  | [] => step 0 []
  | x::xs => do
    let rest ← unique xs
    let yes ← contains x rest
    step 0 (if yes then rest else x::rest)

theorem unique_spec (xs : List ℚ) : (unique xs).value.toFinset = xs.toFinset ∧
    (unique xs).value.Nodup ∧ (unique xs).value.length ≤ xs.length := by
  induction xs with
  | nil => simp [unique]
  | cons x xs ih =>
    by_cases h : x ∈ (unique xs).value
    · have mem := List.mem_toFinset.mpr h
      rw [ih.1] at mem
      simp [unique,h,ih.1,ih.2.1,Finset.insert_eq_of_mem mem]
      omega
    · simp [unique,h,ih.1,ih.2.1,ih.2.2]

theorem unique_work (N w : ℕ) (xs : List ℚ) (len : xs.length ≤ N) (fit : ∀ q ∈ xs, Fits w q) :
    (unique xs).Bound (1+xs.length*(4*N+2)) (scalarWidth w) := by
  induction xs with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons x xs ih =>
    have small : xs.length ≤ N := by simp at len; omega
    have r := ih small (fun q h => fit q (List.mem_cons_of_mem _ h))
    have spec := unique_spec xs
    have c := contains_work (fit x (by simp)) (unique xs).value (fun q h => by
      have hm := List.mem_toFinset.mpr h
      rw [spec.1] at hm
      exact fit q (List.mem_cons_of_mem _ (List.mem_toFinset.mp hm)))
    simp only [unique,Run.Bound,Run.bind_slots,Run.bind_width,List.length_cons,Nat.succ_mul,step_slots,step_width] at *
    omega

end Kintali.InputOutput.DatumWork
