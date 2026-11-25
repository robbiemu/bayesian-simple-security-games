module

public import Kintali.InputOutput.Binary

/-! # Executable readers for the public binary tables

The delimiter convention is attributed in `Binary`. The reader consumes
a list of fields with fuel bounded by the number of input bits.
-/

@[expose] public section

namespace Kintali.InputOutput.Binary

open Computability

abbrev Codec (α : Type) := Encoding α Bool

def splitBlock : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => (splitBlock rest).map fun p => (b :: p.1, p.2)
  | _ => none

theorem split_block (bits tail : List Bool) : splitBlock (block bits ++ tail) = some (bits, tail) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [block, splitBlock, ih]

def pairCodec {α β : Type} (a : Codec α) (b : Codec β) : Codec (α × β) where
  encode := pair a.encode b.encode
  decode bits := do
    let (first, rest) ← splitBlock bits
    let x ← a.decode first
    let y ← b.decode rest
    return (x, y)
  decode_encode p := by simp [pair, split_block]

def readMany {α : Type} (codec : Codec α) : ℕ → List Bool → Option (List α)
  | _, [] => some []
  | 0, _ :: _ => none
  | n+1, b::bs => do
    let (next, rest) ← splitBlock (b::bs)
    let a ← codec.decode next
    let as ← readMany codec n rest
    return a :: as

theorem read_many {α : Type} (codec : Codec α) (xs : List α) (fuel : ℕ) (h : xs.length ≤ fuel) :
    readMany codec fuel (many codec.encode xs) = some xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons x xs ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have tail := ih fuel (by simpa using h)
      have split := split_block (codec.encode x) (many codec.encode xs)
      have dec := codec.decode_encode x
      change readMany codec (fuel+1) (block (codec.encode x) ++ many codec.encode xs) = _
      cases he : codec.encode x <;>
        simp only [he, block, List.cons_append, List.nil_append] at split ⊢ <;>
        simp [readMany, split, ← he, tail]

def listCodec {α : Type} (a : Codec α) : Codec (List α) where
  encode := many a.encode
  decode bits := readMany a bits.length bits
  decode_encode xs := read_many a xs _ (count_le_many _ _)

def natCodec : Codec ℕ where
  encode := encodeNat
  decode bits := some (decodeNat bits)
  decode_encode n := congrArg some (decode_encodeNat n)

def intCodec : Codec ℤ where
  encode := integer
  decode bits := ((pairCodec natCodec natCodec).decode bits).map (fun p => (p.1 : ℤ) - p.2)
  decode_encode z := by
    have dec := (pairCodec natCodec natCodec).decode_encode (z.toNat, (-z).toNat)
    change (pairCodec natCodec natCodec).decode (integer z) = _ at dec
    simp [dec]; omega

def ratCodec : Codec ℚ where
  encode := rational
  decode bits := ((pairCodec intCodec natCodec).decode bits).map (fun p => (p.1 : ℚ) / p.2)
  decode_encode q := by
    have dec := (pairCodec intCodec natCodec).decode_encode (q.num, q.den)
    change (pairCodec intCodec natCodec).decode (rational q) = _ at dec
    simp [dec, Rat.num_div_den]

def payoffCodec := pairCodec ratCodec ratCodec

def inputCodec : Codec Input :=
  pairCodec natCodec (pairCodec (listCodec payoffCodec) (listCodec (pairCodec ratCodec (listCodec payoffCodec))))

def outputCodec : Codec Output := pairCodec (listCodec ratCodec) (listCodec (listCodec ratCodec))

@[simp] theorem read_input (a : Input) : inputCodec.decode (input a) = some a := inputCodec.decode_encode a
@[simp] theorem read_output (e : Output) : outputCodec.decode (output e) = some e := outputCodec.decode_encode e

end Kintali.InputOutput.Binary
