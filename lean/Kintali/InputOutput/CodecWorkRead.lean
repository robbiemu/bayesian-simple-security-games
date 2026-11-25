module

public import Kintali.InputOutput.CodecWorkArithmetic

/-! # Traced delimiter, unsigned numeral, product, and list readers

The public natural codec accepts noncanonical digit strings. In particular
a final false digit doubles the positive decoder's empty-tail value of one.
The work statements cover these inputs and failing parses.
-/

@[expose] public section

namespace Kintali.InputOutput.CodecWork

open Binary Computability StochasticGames.CompilerRun StochasticGames.BinarySize

abbrev Stream := List Bool

def splitRun : Stream → Run (Option (Stream × Stream))
  | false :: tail => step 0 (some ([], tail))
  | true :: b :: tail => do
    let rest ← splitRun tail
    step 0 (rest.map fun p => (b :: p.1, p.2))
  | _ => step 0 none

theorem split_value (xs : Stream) : (splitRun xs).value = splitBlock xs := by
  fun_induction splitRun <;> simp_all [splitBlock]

theorem split_work (xs : Stream) : (splitRun xs).Bound (xs.length+1) 0 := by
  fun_induction splitRun <;> simp_all [Run.Bound]
  omega

theorem split_lengths {xs field tail : Stream} (h : splitBlock xs = some (field,tail)) :
    2*field.length+1+tail.length = xs.length := by
  fun_induction splitBlock xs generalizing field tail with
  | case1 => cases h; simp [Nat.add_comm]
  | case2 b rest ih =>
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨first,last⟩,hf,e⟩ := h
    cases e
    simp only [List.length_cons]
    have := ih hf
    omega
  | _ => contradiction

/-- Charge the width of the accumulator on each shift. -/
def positiveRun : Stream → Run ℕ
  | [] => step 1 1
  | b :: bs =>
    if b && bs.isEmpty then step 1 1 else do
      let n ← positiveRun bs
      step (n.size+1) (Nat.bit b n)

theorem positive_value (xs : Stream) : (positiveRun xs).value = (decodePosNum xs : ℕ) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> cases bs <;>
      simp_all [positiveRun,decodePosNum,PosNum.cast_bit0,PosNum.cast_bit1,
        Nat.bit_false_apply,Nat.bit_true_apply,two_mul]

theorem positive_width (xs : Stream) : (positiveRun xs).value.size ≤ xs.length+1 := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    by_cases h : (b && bs.isEmpty) = true
    · simp [positiveRun,h]
    simp [positiveRun,h]
    by_cases z : Nat.bit b (positiveRun bs).value = 0
    · simp [z]
    rw [Nat.size_bit z]
    omega

theorem positive_work (xs : Stream) : (positiveRun xs).Bound (xs.length+1) (xs.length+1) := by
  induction xs with
  | nil => exact bound_step _ _
  | cons b bs ih =>
    have hw := positive_width bs
    by_cases h : (b && bs.isEmpty) = true <;>
      simp [positiveRun,h,Run.Bound] at *
    omega

def numberRun : Stream → Run (Option ℕ)
  | [] => step 0 (some 0)
  | b::bs => do
    let n ← positiveRun (b::bs)
    step 0 (some n)

theorem number_value (xs : Stream) : (numberRun xs).value = natCodec.decode xs := by
  cases xs with
  | nil => rfl
  | cons b bs => simp [numberRun,positive_value,natCodec,decodeNat,decodeNum]

theorem number_width {xs : Stream} {n : ℕ} (h : natCodec.decode xs = some n) :
    n.size ≤ xs.length+1 := by
  rw [← number_value] at h
  cases xs with
  | nil => cases h; decide
  | cons b bs =>
    simp only [numberRun,Run.bind_value,step_value,Option.some.injEq] at h
    exact h ▸ positive_width (b::bs)

structure Reader {α : Type} (codec : Codec α) (limit : ℕ → ℕ) where
  run : Stream → Run (Option α)
  correct : ∀ xs, (run xs).value = codec.decode xs
  work : ∀ xs S, xs.length ≤ S → (run xs).Bound (limit S) (S+8)

def natReader : Reader natCodec (fun S => S+2) where
  run := numberRun
  correct := number_value
  work xs S fit := by
    cases xs with
    | nil => exact (bound_step _ _).weaken (by omega) (Nat.zero_le _)
    | cons b bs =>
      have h := positive_work (b::bs)
      simp only [numberRun,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width] at *
      omega

def next {α β : Type} (r : Run (Option α)) (f : α → Run (Option β)) : Run (Option β) := do
  let res ← r
  match ← step 0 res with
  | none => pure none
  | some a => f a

theorem next_value {α β : Type} (r : Run (Option α)) (f : α → Run (Option β)) :
    (next r f).value = r.value.bind (fun x => (f x).value) := by
  cases h : r.value <;> simp [next,h]

theorem next_work {α β : Type} {r : Run (Option α)} {f : α → Run (Option β)} {k j W : ℕ}
    (hr : r.Bound k W) (hf : ∀ x, r.value = some x → (f x).Bound j W) :
    (next r f).Bound (k+1+j) W := by
  cases h : r.value with
  | none =>
    simp only [next,Run.Bound,Run.bind_slots,h,step_value,step_slots,Run.bind_width,step_width]
    change _ + (1+0) ≤ _ ∧ max _ (max 0 0) ≤ _
    exact ⟨by have := hr.1; omega, by simpa using hr.2⟩
  | some x =>
    have hx := hf x h
    simp only [next,Run.Bound,Run.bind_slots,h,step_value,step_slots,Run.bind_width,step_width] at *
    omega

def pairLimit (c d : ℕ → ℕ) (S : ℕ) := S+5+c S+d S

def pairReader {α β : Type} {a : Codec α} {b : Codec β} {c d : ℕ → ℕ}
    (u : Reader a c) (v : Reader b d) : Reader (pairCodec a b) (pairLimit c d) where
  run xs := next (splitRun xs) fun p => next (u.run p.1) fun x =>
    next (v.run p.2) fun y => step 0 (some (x,y))
  correct xs := by simp [next_value,split_value,u.correct,v.correct,pairCodec]
  work xs S fit := by
    have hs := (split_work xs).weaken (Nat.add_le_add_right fit 1) (Nat.zero_le (S+8))
    refine (next_work hs (j := c S+1+(d S+1+1)) ?_).weaken (by unfold pairLimit; omega) le_rfl
    rintro ⟨f,t⟩ h
    have len := split_lengths (xs := xs) (field := f) (tail := t) (by simpa [split_value] using h)
    apply next_work (u.work f S (by omega))
    intro x _
    apply next_work (v.work t S (by omega))
    intro y _
    exact (bound_step _ _).weaken le_rfl (Nat.zero_le _)

def readList {α : Type} (parse : Stream → Run (Option α)) : ℕ → Stream → Run (Option (List α))
  | _, [] => step 0 (some [])
  | 0, _::_ => step 0 none
  | k+1, b::bs => do
    let _ ← step (k+1).size k
    next (splitRun (b::bs)) fun p => next (parse p.1) fun x =>
      next (readList parse k p.2) fun xs => step 0 (some (x::xs))

theorem readList_value {α : Type} {a : Codec α} {c : ℕ → ℕ} (u : Reader a c)
    (k : ℕ) (xs : Stream) : (readList u.run k xs).value = readMany a k xs := by
  induction k generalizing xs with
  | zero => cases xs <;> rfl
  | succ k ih => cases xs <;> simp [readList,readMany,next_value,split_value,u.correct,ih]

theorem readList_work {α : Type} {a : Codec α} {c : ℕ → ℕ} (u : Reader a c)
    (S k : ℕ) (xs : Stream) (fuel : k ≤ S) (fit : xs.length ≤ S) :
    (readList u.run k xs).Bound (k*(S+c S+6)+1) (S+8) := by
  induction k generalizing xs with
  | zero => cases xs <;> exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | succ k ih =>
    cases xs with
    | nil => exact (bound_step _ _).weaken (by omega) (Nat.zero_le _)
    | cons b bs =>
      have dec := (bound_step (k+1).size k).weaken le_rfl ((size_le_self _).trans (by omega : k+1 ≤ S+8))
      have hs := (split_work (b::bs)).weaken (Nat.add_le_add_right fit 1) (Nat.zero_le (S+8))
      refine (bound_bind (f := fun _ => _) dec (next_work hs (j := c S+1+(k*(S+c S+6)+1+1+1)) ?_)).weaken ?_ le_rfl
      · rintro ⟨f,t⟩ h
        have len := split_lengths (xs := b::bs) (field := f) (tail := t) (by simpa [split_value] using h)
        apply next_work (u.work f S (by omega))
        intro x _
        apply next_work (ih t (by omega) (by omega))
        intro tail _
        exact (bound_step _ _).weaken le_rfl (Nat.zero_le _)
      · rw [Nat.succ_mul]; omega

def listLimit (c : ℕ → ℕ) (S : ℕ) := S+1+(S*(S+c S+6)+1)

def listReader {α : Type} {a : Codec α} {c : ℕ → ℕ} (u : Reader a c) :
    Reader (listCodec a) (listLimit c) where
  run xs := do
    let n ← StochasticGames.CompilerRun.length xs
    readList u.run n xs
  correct xs := by simp [readList_value,listCodec]
  work xs S fit := by
    have hl := (length_bound xs).weaken (Nat.add_le_add_right fit 1)
      ((size_le_self _).trans (by omega : xs.length ≤ S+8))
    refine (bound_bind (f := fun n => readList u.run n xs) (l := xs.length*(S+c S+6)+1) hl ?_).weaken (k' := listLimit c S) ?_ le_rfl
    · rw [length_value]
      exact readList_work u S xs.length xs fit fit
    · unfold listLimit
      exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_right _ fit) 1) _

end Kintali.InputOutput.CodecWork
