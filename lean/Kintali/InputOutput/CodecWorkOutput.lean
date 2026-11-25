module

public import Kintali.InputOutput.Codec
public import StochasticGames.CostedBinary
import all StochasticGames.CostedBinary

/-! # Writing the compact equilibrium in its public delimiter format

The digits writer is shared with the addressed binary compiler. Each nested
delimiter charges its own pass over the inner field. Input rational numbers
are stored as their reduced numerator and denominator.
-/

@[expose] public section

namespace Kintali.InputOutput.CodecWork

open Binary Computability StochasticGames.CompilerRun StochasticGames.CostedBinary

private theorem encode_digits (n : ℕ) : encodeNat n = n.bits := by
  have pos (p : PosNum) : encodePosNum p = (p : ℕ).bits := by
    induction p with
    | one => rfl
    | bit0 p ih =>
      rw [PosNum.cast_bit0, ← two_mul, Nat.bit0_bits _ (PosNum.to_nat_pos p).ne']
      exact congrArg (false :: ·) ih
    | bit1 p ih =>
      rw [PosNum.cast_bit1, ← two_mul, Nat.bit1_bits]
      exact congrArg (true :: ·) ih
  have aux (v : Num) : encodeNum v = (v : ℕ).bits := by
    cases v with
    | zero => rfl
    | pos p => exact pos p
  simpa only [encodeNat, Num.to_of_nat] using aux (n : Num)

structure Writer {α : Type} (encode : α → Bits) (factor : ℕ) where
  run : α → Run Bits
  correct : ∀ x, (run x).value = encode x
  work : ∀ x, (run x).Bound (factor * ((encode x).length + 1)) ((encode x).length + 3)

def natWriter : Writer encodeNat 6 where
  run n := do
    let k ← step n.size n.size
    digitsRun n.size k n []
  correct n := by simpa [encode_digits] using (digits_spec n.size n []).out
  work n := by
    have h := (digits_spec n.size n []).cost
    simp only [Run.bind_slots, step_slots, step_value, Run.bind_width, step_width,
      Run.Bound, Binary.length_nat] at *
    omega

/-- Prepend an escaped field to a shared suffix. -/
def delimit : Bits → Bits → Run Bits
  | [], tail => step 0 (false :: tail)
  | b :: bs, tail => do
    let rest ← delimit bs tail
    let payload ← step 0 (b :: rest)
    step 0 (true :: payload)

theorem delimit_value (xs tail : Bits) : (delimit xs tail).value = block xs ++ tail := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [delimit, block, ih]

theorem delimit_work (xs tail : Bits) : (delimit xs tail).Bound (2 * xs.length + 1) 0 := by
  induction xs with
  | nil => exact bound_step _ _
  | cons b bs ih =>
    simp only [delimit, Run.Bound, Run.bind_slots, step_slots, Run.bind_width, step_width,
      List.length_cons] at *
    omega

def pairWriter {α β : Type} {f : α → Bits} {g : β → Bits} {c d : ℕ}
    (a : Writer f c) (b : Writer g d) : Writer (pair f g) (c+d+3) where
  run p := do
    let x ← a.run p.1
    let y ← b.run p.2
    delimit x y
  correct p := by simp [a.correct,b.correct,delimit_value,pair]
  work p := by
    have ha := a.work p.1
    have hb := b.work p.2
    have hd := delimit_work (f p.1) (g p.2)
    simp only [Run.Bound, Run.bind_slots, Run.bind_width, a.correct, b.correct, length_pair] at *
    constructor
    · calc
        _ ≤ c*((f p.1).length+1) + (d*((g p.2).length+1) + (2*(f p.1).length+1)) :=
          Nat.add_le_add ha.1 (Nat.add_le_add hb.1 hd.1)
        _ ≤ _ := by nlinarith only [Nat.zero_le (c*(g p.2).length), Nat.zero_le (d*(f p.1).length),
          Nat.zero_le (c*(f p.1).length)]
    · omega

def writeMany {α : Type} (w : α → Run Bits) : List α → Run Bits
  | [] => step 0 []
  | x::xs => do
    let head ← w x
    let tail ← writeMany w xs
    delimit head tail

def manyWriter {α : Type} {f : α → Bits} {c : ℕ} (w : Writer f c) :
    Writer (many f) (c+3) where
  run := writeMany w.run
  correct xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [writeMany,w.correct,ih,delimit_value,many] at *
  work xs := by
    have value (xs : List α) : (writeMany w.run xs).value = many f xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [writeMany,w.correct,ih,delimit_value,many] at *
    induction xs with
    | nil => exact (bound_step _ _).weaken (by simp [many]) (by simp)
    | cons x xs ih =>
      have head := w.work x
      have del := delimit_work (f x) (many f xs)
      have len : (many f (x::xs)).length = 2*(f x).length+1+(many f xs).length := by
        simp [many]
      simp only [writeMany, Run.Bound, Run.bind_slots, Run.bind_width, w.correct, value, len] at *
      constructor
      · calc
          _ ≤ c*((f x).length+1) + ((c+3)*((many f xs).length+1) + (2*(f x).length+1)) :=
            Nat.add_le_add head.1 (Nat.add_le_add ih.1 del.1)
          _ ≤ _ := by nlinarith only [Nat.zero_le (c*(f x).length)]
      · omega

def intWriter : Writer integer 20 where
  run z := do
    let pos ← step z.natAbs.size z.toNat
    let neg ← step z.natAbs.size (-z).toNat
    (pairWriter natWriter natWriter).run (pos,neg)
  correct z := by simp [Writer.correct, integer]
  work z := by
    have h := (pairWriter natWriter natWriter).work (z.toNat,(-z).toNat)
    change Run.Bound (15*((integer z).length+1)) ((integer z).length+3) _ at h
    have mag : z.natAbs.size ≤ (integer z).length := by
      cases z <;> simp [integer]
      omega
    simp only [Run.Bound,Run.bind_width,Run.bind_slots,step_width,step_slots,step_value] at *
    omega

def ratWriter : Writer rational 30 where
  run q := do
    let n ← step 0 q.num
    let d ← step 0 q.den
    (pairWriter intWriter natWriter).run (n,d)
  correct q := by simp [Writer.correct, rational]
  work q := by
    have h := (pairWriter intWriter natWriter).work (q.num,q.den)
    change Run.Bound (29*((rational q).length+1)) ((rational q).length+3) _ at h
    have hr : 1 ≤ (rational q).length := by simp [rational]; omega
    simp only [Run.Bound,Run.bind_width,Run.bind_slots,step_width,step_slots,step_value] at *
    omega

def outputWriter : Writer output 72 := pairWriter (manyWriter ratWriter) (manyWriter (manyWriter ratWriter))

theorem output_value (e : Output) : (outputWriter.run e).value = outputCodec.encode e :=
  outputWriter.correct e

theorem output_work (e : Output) :
    (outputWriter.run e).Bound (72*((output e).length+1)) ((output e).length+3) :=
  outputWriter.work e

end Kintali.InputOutput.CodecWork
