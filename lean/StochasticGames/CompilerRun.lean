module

public import StochasticGames.BinarySize
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.FinRange
import Mathlib.Tactic.GCongr

/-! # Executions of the binary compiler

A primitive transition records its operand width. Sequencing adds the
transition counts and keeps the maximum width. The word and address
bounds below price those observations for the binary cost model.
-/

@[expose] public section
namespace StochasticGames.CompilerRun

universe u

/-- A width-dependent bound for the elementary word operations in the cost model. -/
def wordCost (width : ℕ) : ℕ := 64 * (width + 1) ^ 3

theorem wordCost_mono : Monotone wordCost := by
  intro a b h
  unfold wordCost
  gcongr
  omega

/-- Space allowance for input and a cubic scratch area per transition. -/
def memoryCells (L slots width : ℕ) : ℕ := 128 * (L+1) * (slots+1) * (width+1)^3

def addressWidth (L slots width : ℕ) : ℕ :=
  (L+1).size + (slots+1).size + 3*(width+1).size + 8

theorem memory_address_fits (L slots width : ℕ) :
    (memoryCells L slots width).size ≤ addressWidth L slots width := by
  let w := width+1
  let m := 128*(L+1)*(slots+1)
  have unit : (128 : ℕ).size = 8 := by decide
  have lm := BinarySize.size_mul_le 128 (L+1)
  have sm := BinarySize.size_mul_le (128*(L+1)) (slots+1)
  have w₂ := BinarySize.size_mul_le w w
  have w₃ := BinarySize.size_mul_le (w*w) w
  have all := BinarySize.size_mul_le m ((w*w)*w)
  change (m * w^3).size ≤ addressWidth L slots width
  rw [show w^3 = w*w*w by simp [pow_succ]]
  unfold addressWidth
  dsimp only [w,m] at *
  omega

structure Work where
  slots : ℕ
  width : ℕ

namespace Work

def empty : Work := ⟨0, 0⟩

def one (w : ℕ) : Work := ⟨1, w⟩

def seq (a b : Work) : Work where
  slots := a.slots + b.slots
  width := max a.width b.width

end Work

structure Run (α : Type u) where
  value : α
  work : Work

namespace Run

def ret {α : Type u} (a : α) : Run α := ⟨a, Work.empty⟩

def seq {α β : Type u} (p : Run α) (f : α → Run β) : Run β :=
  let q := f p.value
  ⟨q.value, p.work.seq q.work⟩

instance : Monad Run where
  pure := ret
  bind := seq
  map f p := ⟨f p.value, p.work⟩

def Bound {α : Type u} (k w : ℕ) (p : Run α) : Prop :=
  p.work.slots ≤ k ∧ p.work.width ≤ w

theorem Bound.weaken {α : Type u} {p : Run α} {k w k' w' : ℕ}
    (h : p.Bound k w) (hk : k ≤ k') (hw : w ≤ w') : p.Bound k' w' :=
  ⟨h.1.trans hk, h.2.trans hw⟩

@[simp] theorem pure_value {α : Type u} (a : α) : (pure a : Run α).value = a := rfl

@[simp] theorem bind_value {α β : Type u} (p : Run α) (f : α → Run β) :
    (p >>= f).value = (f p.value).value := rfl

@[simp] theorem bind_slots {α β : Type u} (p : Run α) (f : α → Run β) :
    (p >>= f).work.slots = p.work.slots + (f p.value).work.slots := rfl

@[simp] theorem bind_width {α β : Type u} (p : Run α) (f : α → Run β) :
    (p >>= f).work.width = max p.work.width (f p.value).work.width := rfl

end Run

/-- Execute one primitive with the observed width of its binary operands. -/
def step {α : Type u} (w : ℕ) (value : α) : Run α := ⟨value, Work.one w⟩

@[simp] theorem step_value {α : Type u} (w : ℕ) (a : α) : (step w a).value = a := rfl

@[simp] theorem step_slots {α : Type u} (w : ℕ) (a : α) : (step w a).work.slots = 1 := rfl

@[simp] theorem step_width {α : Type u} (w : ℕ) (a : α) : (step w a).work.width = w := rfl

theorem bound_pure {α : Type u} (a : α) (w : ℕ) : (pure a : Run α).Bound 0 w :=
  ⟨le_rfl, Nat.zero_le _⟩

theorem bound_step {α : Type u} (w : ℕ) (a : α) : (step w a).Bound 1 w :=
  ⟨le_rfl, le_rfl⟩

theorem bound_bind {α β : Type u} {p : Run α} {f : α → Run β} {k l w : ℕ}
    (hp : p.Bound k w) (hf : (f p.value).Bound l w) : (p >>= f).Bound (k + l) w :=
  ⟨Nat.add_le_add hp.1 hf.1, max_le hp.2 hf.2⟩

/-- One addition or subtraction of unsigned or signed binary words. -/
def natAdd (a b : ℕ) : Run ℕ := step (max a.size b.size) (a + b)
def natSub (a b : ℕ) : Run ℕ := step (max a.size b.size) (a - b)
def natMul (a b : ℕ) : Run ℕ := step (max a.size b.size) (a * b)
def intAdd (a b : ℤ) : Run ℤ := step (max a.natAbs.size b.natAbs.size + 1) (a + b)
def intSub (a b : ℤ) : Run ℤ := step (max a.natAbs.size b.natAbs.size + 1) (a - b)
def intMul (a b : ℤ) : Run ℤ := step (max a.natAbs.size b.natAbs.size + 1) (a * b)

/-- Visit the cells of the first list and copy them onto the second list. -/
def append {α : Type u} : List α → List α → Run (List α)
  | [], ys => step 0 ys
  | x :: xs, ys => do
    let tail ← append xs ys
    step 0 (x :: tail)

@[simp] theorem append_value {α : Type u} (xs ys : List α) : (append xs ys).value = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [append]

theorem append_bound {α : Type u} (xs ys : List α) (w : ℕ) :
    (append xs ys).Bound (xs.length + 1) w := by
  induction xs with
  | nil => exact (bound_step 0 ys).weaken le_rfl (Nat.zero_le _)
  | cons x xs ih =>
    change ((append xs ys) >>= _).Bound (xs.length + 1 + 1) w
    exact bound_bind ih ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))

def mapM {α β : Type u} (f : α → Run β) : List α → Run (List β)
  | [] => step 0 []
  | x :: xs => do
    let _ ← step 0 (PUnit.unit : PUnit.{u+1})
    let y ← f x
    let ys ← mapM f xs
    step 0 (y :: ys)

@[simp] theorem mapM_value {α β : Type u} (f : α → Run β) (xs : List α) :
    (mapM f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [mapM]

theorem mapM_bound {α β : Type u} (f : α → Run β) (xs : List α) (k w : ℕ)
    (h : ∀ x ∈ xs, (f x).Bound k w) : (mapM f xs).Bound (xs.length * (k + 2) + 1) w := by
  induction xs with
  | nil => exact (bound_step 0 []).weaken (by simp) (Nat.zero_le _)
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have unitStep := (bound_step 0 (PUnit.unit : PUnit.{u+1})).weaken le_rfl (Nat.zero_le w)
    have appendStep (ys : List β) := (bound_step 0 ((f x).value :: ys)).weaken le_rfl (Nat.zero_le w)
    have htail := bound_bind (f := fun ys => step 0 ((f x).value :: ys))
      ht (appendStep (mapM f xs).value)
    have hhead := bound_bind (f := fun y => do
      let ys ← mapM f xs
      step 0 (y :: ys)) hx htail
    have hall := bound_bind (f := fun _ => do
      let y ← f x
      let ys ← mapM f xs
      step 0 (y :: ys)) unitStep hhead
    exact hall.weaken (by simp [Nat.add_mul]; omega) le_rfl

def flatMapM {α β : Type u} (f : α → Run (List β)) : List α → Run (List β)
  | [] => step 0 []
  | x :: xs => do
    let _ ← step 0 (PUnit.unit : PUnit.{u+1})
    let ys ← f x
    let zs ← flatMapM f xs
    append ys zs

@[simp] theorem flatMapM_value {α β : Type u} (f : α → Run (List β)) (xs : List α) :
    (flatMapM f xs).value = xs.flatMap (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [flatMapM]

theorem flatMapM_bound {α β : Type u} (f : α → Run (List β)) (xs : List α) (k len w : ℕ)
    (h : ∀ x ∈ xs, (f x).Bound k w) (hs : ∀ x ∈ xs, (f x).value.length ≤ len) :
    (flatMapM f xs).Bound (xs.length * (k + len + 2) + 1) w := by
  induction xs with
  | nil => exact (bound_step 0 []).weaken (by simp) (Nat.zero_le _)
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy)) (fun y hy => hs y (List.mem_cons_of_mem x hy))
    have hp := (append_bound (f x).value (flatMapM f xs).value w).weaken
      (Nat.add_le_add_right (hs x (by simp)) 1) le_rfl
    have htail := bound_bind (f := append (f x).value) ht hp
    have hhead := bound_bind (f := fun ys => do
      let zs ← flatMapM f xs
      append ys zs) hx htail
    have hbegin := (bound_step 0 (PUnit.unit : PUnit.{u+1})).weaken le_rfl (Nat.zero_le w)
    have hall := bound_bind (f := fun _ => do
      let ys ← f x
      let zs ← flatMapM f xs
      append ys zs) hbegin hhead
    exact hall.weaken (by simp [Nat.add_mul]; omega) le_rfl

/-- Indexed list access visits each preceding cell and the selected cell. -/
def get {α : Type u} : (xs : List α) → Fin xs.length → Run α
  | [], i => Fin.elim0 i
  | x :: _, ⟨0, _⟩ => step 0 x
  | _ :: xs, ⟨i+1, hi⟩ =>
    let tail := get xs ⟨i, by simpa using hi⟩
    ⟨tail.value, (Work.one (i+1).size).seq tail.work⟩

@[simp] theorem get_value {α : Type u} (xs : List α) (i : Fin xs.length) :
    (get xs i).value = xs.get i := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    rcases i with ⟨_ | i, hi⟩
    · rfl
    · simpa [get] using ih (⟨i, by simpa using hi⟩ : Fin xs.length)

theorem get_bound {α : Type u} (xs : List α) (i : Fin xs.length) :
    (get xs i).Bound (i.val+1) i.val.size := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    rcases i with ⟨_ | i, hi⟩
    · exact bound_step _ _
    · let j : Fin xs.length := ⟨i, by simpa using hi⟩
      have hrec := (ih j).weaken le_rfl (Nat.size_le_size (Nat.le_succ i))
      change 1 + (get xs j).work.slots ≤ i + 1 + 1 ∧
        max (i+1).size (get xs j).work.width ≤ (i+1).size
      have hs : (get xs j).work.slots ≤ i+1 := hrec.1
      exact ⟨by omega, max_le le_rfl hrec.2⟩

def length {α : Type u} : List α → Run ℕ
  | [] => step 0 0
  | _ :: xs => do
    let k ← length xs
    natAdd k 1

@[simp] theorem length_value {α : Type u} (xs : List α) : (length xs).value = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [length, natAdd, ih]

theorem length_bound {α : Type u} (xs : List α) :
    (length xs).Bound (xs.length+1) xs.length.size := by
  induction xs with
  | nil => exact bound_step _ _
  | cons x xs ih =>
    have wide : 1 ≤ (xs.length+1).size := Nat.size_pos.mpr (by omega)
    have tail := ih.weaken le_rfl (Nat.size_le_size (Nat.le_succ xs.length))
    have inc : (natAdd (length xs).value 1).Bound 1 (xs.length+1).size :=
      (bound_step _ _).weaken le_rfl (by
        rw [length_value, Nat.size_one]
        exact max_le (Nat.size_le_size (Nat.le_succ _)) wide)
    exact bound_bind (f := fun k => natAdd k 1) tail inc

def rangeFrom {n : ℕ} : (count start : ℕ) → start + count ≤ n → Run (List (Fin n))
  | 0, _, _ => step 0 []
  | k+1, i, hi => do
    let next ← step (max (k+1).size (max i.size 1)) (⟨i+1, by omega⟩ : {j : ℕ // j+k ≤ n})
    let tail ← rangeFrom k next.val next.property
    step 0 (⟨i, by omega⟩ :: tail)

private theorem rangeFrom_value {n : ℕ} (k i : ℕ) (hi : i + k ≤ n) :
    (rangeFrom k i hi).value = List.ofFn (fun j : Fin k => (⟨i+j.val, by omega⟩ : Fin n)) := by
  induction k generalizing i with
  | zero => simp [rangeFrom]
  | succ k ih =>
    simp only [rangeFrom, Run.bind_value, step_value, ih, List.ofFn_succ,
      Fin.val_zero, Nat.add_zero, Fin.val_succ]
    apply congrArg (List.cons (⟨i, by omega⟩ : Fin n))
    apply congrArg List.ofFn
    funext j
    apply Fin.ext
    change i + 1 + j.val = i + (j.val + 1)
    omega

private theorem rangeFrom_bound {n : ℕ} (k i : ℕ) (hi : i+k ≤ n) :
    (rangeFrom k i hi).Bound (2*k+1) n.size := by
  induction k generalizing i with
  | zero => exact (bound_step _ _).weaken le_rfl (Nat.zero_le _)
  | succ k ih =>
    let start : {j : ℕ // j+k ≤ n} := ⟨i+1, by omega⟩
    have first : (step (max (k+1).size (max i.size 1)) start).Bound 1 n.size :=
      (bound_step _ _).weaken le_rfl (max_le (Nat.size_le_size (by omega))
        (max_le (Nat.size_le_size (by omega)) (Nat.size_pos.mpr (by omega))))
    have rest := bound_bind (f := fun xs => step 0 ((⟨i, by omega⟩ : Fin n) :: xs))
      (ih start.val start.property) ((bound_step _ _).weaken le_rfl (Nat.zero_le _))
    have all := bound_bind (f := fun next : {j : ℕ // j+k ≤ n} => do
        let tail ← rangeFrom k next.val next.property
        step 0 ((⟨i, by omega⟩ : Fin n) :: tail)) first rest
    exact all.weaken (by omega) le_rfl

def finRange (n : ℕ) : Run (List (Fin n)) := rangeFrom n 0 (by simp)

@[simp] theorem finRange_value (n : ℕ) : (finRange n).value = List.finRange n := by
  simpa [finRange, List.finRange] using
    (rangeFrom_value (n := n) n 0 (by simp))

theorem finRange_bound (n : ℕ) : (finRange n).Bound (2*n+1) n.size :=
  rangeFrom_bound (n := n) n 0 (by simp)

end StochasticGames.CompilerRun
