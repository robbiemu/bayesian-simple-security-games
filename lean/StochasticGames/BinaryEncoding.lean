module

public import StochasticGames.CompilationCost
import Mathlib.Data.List.FinRange

/-!
# Binary readers for the H4 source and target

Each reader consumes one field and returns the unread suffix. The complete decoders
require an empty suffix. Natural numbers have a unary width followed by that many
least-significant-first digits. The source reader checks successor indices, move-list
lengths and the positive threshold denominator.
-/

@[expose] public section

namespace StochasticGames.BinaryEncoding

open CompilationCost

abbrev Reader (α : Type*) := List Bool → Option (α × List Bool)

/-- Count the leading ones and consume the terminating zero. -/
def readWidth : Reader ℕ
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => (readWidth xs).map (fun p => (p.1+1, p.2))

private theorem readWidth_replicate (k : ℕ) (xs : List Bool) :
    readWidth (List.replicate k true ++ false :: xs) = some (k, xs) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, readWidth, ih]

/-- Consume exactly the next `k` bits. A missing bit makes the read fail. -/
def readBlock : ℕ → Reader (List Bool)
  | 0, xs => some ([], xs)
  | _+1, [] => none
  | k+1, b::xs => (readBlock k xs).map (fun p => (b :: p.1, p.2))

private theorem readBlock_append (xs tail : List Bool) :
    readBlock xs.length (xs ++ tail) = some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [readBlock, ih]

private theorem fold_bits (a : ℕ) : a.bits.foldr Nat.bit 0 = a := by
  induction a using Nat.binaryRec' with
  | zero => rfl
  | bit b a ha ih => simp [Nat.bits_append_bit a b ha, ih]

def readNat (xs : List Bool) : Option (ℕ × List Bool) := do
  let (k, rest) ← readWidth xs
  let (digits, tail) ← readBlock k rest
  let value := digits.foldr Nat.bit 0
  if value.size = k then some (value, tail) else none

private theorem readNat_append (a : ℕ) (tail : List Bool) :
    readNat (natBits a ++ tail) = some (a, tail) := by
  have hblock : readBlock a.size (a.bits ++ tail) = some (a.bits, tail) := by
    simpa only [Nat.size_eq_bits_len] using readBlock_append a.bits tail
  simp [readNat, natBits, List.append_assoc, readWidth_replicate, hblock, fold_bits]

def readInt : Reader ℤ
  | [] => none
  | sign::rest => do
    let (a, tail) ← readNat rest
    if sign && a == 0 then none
    else some (if sign then -(a : ℤ) else (a : ℤ), tail)

private theorem readInt_append (z : ℤ) (tail : List Bool) :
    readInt (intBits z ++ tail) = some (z, tail) := by
  by_cases hz : z < 0
  · have hn : (z.natAbs : ℤ) = -z := (Int.natCast_natAbs z).trans (abs_of_neg hz)
    have hnz : z.natAbs ≠ 0 := (Int.natAbs_pos.mpr hz.ne).ne'
    simp [intBits, readInt, readNat_append, hz, hn, hnz]
  · have hn : (z.natAbs : ℤ) = z := (Int.natCast_natAbs z).trans (abs_of_nonneg (le_of_not_gt hz))
    simp [intBits, readInt, readNat_append, hz, hn]

def readPosition (n : ℕ) : Reader (Source.Position (Fin n))
  | true :: b :: tail => some (.inr b, tail)
  | false :: rest => do
    let (i, tail) ← readNat rest
    if hi : i < n then some (.inl ⟨i,hi⟩, tail) else none
  | _ => none

private theorem readPosition_append {n : ℕ} (p : Source.Position (Fin n)) (tail : List Bool) :
    readPosition n (positionBits p ++ tail) = some (p, tail) := by
  cases p with
  | inl i => simp [positionBits, readPosition, readNat_append, i.isLt]
  | inr b => rfl

def readMany {α : Type*} (read : Reader α) : ℕ → Reader (List α)
  | 0, xs => some ([], xs)
  | k+1, xs => do
    let (a, rest) ← read xs
    let (as, tail) ← readMany read k rest
    some (a::as, tail)

private theorem readMany_append {α : Type*} (read : Reader α) (encode : α → List Bool)
    (decode : ∀ x tail, read (encode x ++ tail) = some (x, tail)) (xs : List α) (tail : List Bool) :
    readMany read xs.length (xs.flatMap encode ++ tail) = some (xs, tail) := by
  induction xs generalizing tail with
  | nil => rfl
  | cons x xs ih => simp [readMany, List.append_assoc, decode, ih]

def readRow (n : ℕ) : Reader (Source.Row (Fin n))
  | true :: xs => do
    let (a, rest) ← readPosition n xs
    let (b, tail) ← readPosition n rest
    some (.chance a b, tail)
  | false :: isMin :: xs => do
    let (k, rest) ← readNat xs
    let (a::l, tail) ← readMany (readPosition n) k rest | none
    some ((if isMin then .min a l else .max a l), tail)
  | _ => none

private theorem readRow_append {n : ℕ} (row : Source.Row (Fin n)) (tail : List Bool) :
    readRow n (sourceRowBits row ++ tail) = some (row, tail) := by
  cases row with
  | max a l | min a l =>
    have h := readMany_append (readPosition n) positionBits readPosition_append (a::l) tail
    simp only [List.length_cons] at h
    simp only [sourceRowBits, List.append_assoc, List.cons_append, List.nil_append, readRow,
      readNat_append, Option.bind_eq_bind, Option.bind_some, h]
    rfl
  | chance a b => simp [sourceRowBits, List.append_assoc, readRow, readPosition_append]

def finish {α : Type*} (read : Reader α) (xs : List Bool) : Option α :=
  match read xs with
  | some (value, []) => some value
  | _ => none

def readInput (xs : List Bool) : Option ((Σ n, ThresholdInput n) × List Bool) := do
  let (n, rest) ← readNat xs
  let (rs, rest) ← readMany (readRow n) n rest
  if hr : rs.length = n then
    let (start, rest) ← readPosition n rest
    let (num, rest) ← readInt rest
    let (den, tail) ← readNat rest
    if hd : 0 < den then
      let rows : Vector (Source.Row (Fin n)) n := ⟨rs.toArray, by simpa using hr⟩
      some (⟨n, ⟨rows, start, num, den, hd⟩⟩, tail)
    else none
  else none

private theorem vector_rows {α : Type*} {n : ℕ} (v : Vector α n) :
    (List.finRange n).map v.get = v.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [Vector.get]

private theorem readInput_append {n : ℕ} (input : ThresholdInput n) (tail : List Bool) :
    readInput (inputBits input ++ tail) = some (⟨n,input⟩, tail) := by
  have hflat : (List.finRange n).flatMap (fun i => sourceRowBits (input.rows.get i)) =
      input.rows.toList.flatMap sourceRowBits := by
    rw [← vector_rows input.rows, List.flatMap_map]
  have hrows := readMany_append (readRow n) sourceRowBits readRow_append input.rows.toList
  simp only [Vector.length_toList] at hrows
  have hv : (⟨input.rows.toList.toArray, by simp⟩ : Vector _ n) = input.rows := by
    apply Vector.toArray_inj.mp
    simp [Vector.toList]
  simp [inputBits, List.append_assoc, hflat, readInput, readNat_append, hrows,
    readPosition_append, readInt_append, input.denominator_pos, hv]

/-- Read the state count together with its dependent source game. -/
def decodeInput : List Bool → Option (Σ n, ThresholdInput n) := finish readInput

@[simp] theorem decodeInput_inputBits {n : ℕ} (input : ThresholdInput n) :
    decodeInput (inputBits input) = some ⟨n,input⟩ := by
  have h : readInput (inputBits input) = some (⟨n,input⟩, []) := by
    simpa only [List.append_nil] using readInput_append input []
  rw [decodeInput, finish, h]

def readArc (xs : List Bool) : Option (ArenaEncoding.ArcRecord × List Bool) := do
  let (src, rest) ← readNat xs
  let (dst, rest) ← readNat rest
  let (weight, tail) ← readInt rest
  some (⟨src,dst,weight⟩, tail)

private theorem readArc_append (e : ArenaEncoding.ArcRecord) (tail : List Bool) :
    readArc (arcBits e ++ tail) = some (e, tail) := by
  cases e
  simp [readArc, arcBits, List.append_assoc, readNat_append, readInt_append]

def readTable (xs : List Bool) : Option (ArenaEncoding.Table × List Bool) := do
  let (start, rest) ← readNat xs
  let (n, rest) ← readNat rest
  let (owners, rest) ← readBlock n rest
  let (m, rest) ← readNat rest
  let (arcs, tail) ← readMany readArc m rest
  some (⟨start,owners,arcs⟩, tail)

private theorem readTable_append (t : ArenaEncoding.Table) (tail : List Bool) :
    readTable (tableBits t ++ tail) = some (t, tail) := by
  cases t with
  | mk start owners arcs =>
    simp [readTable, tableBits, List.append_assoc, readNat_append, readBlock_append,
      readMany_append readArc arcBits readArc_append]

def decodeTable : List Bool → Option ArenaEncoding.Table := finish readTable

@[simp] theorem decodeTable_tableBits (t : ArenaEncoding.Table) :
    decodeTable (tableBits t) = some t := by
  have h : readTable (tableBits t) = some (t, []) := by
    simpa only [List.append_nil] using readTable_append t []
  rw [decodeTable, finish, h]

theorem inputBits_injective : Function.Injective
    (fun x : Σ n, ThresholdInput n => inputBits x.2) := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  exact Option.some.inj (by simpa only [decodeInput_inputBits] using congrArg decodeInput h)

theorem tableBits_injective : Function.Injective tableBits := by
  intro x y h
  exact Option.some.inj (by simpa only [decodeTable_tableBits] using congrArg decodeTable h)

end StochasticGames.BinaryEncoding
