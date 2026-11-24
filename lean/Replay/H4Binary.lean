import StochasticGames.BinaryReduction
import Lean

/-! JSON-lines adapter for the binary compiler replay. -/

open Lean StochasticGames

structure Fixture where
  name : String
  rows : Array (String × List Int)
  start : Int
  numerator : Int
  denominator : Nat
  deriving FromJson

def position {n : Nat} (index : Int) : Except String (Source.Position (Fin n)) :=
  if index = -1 then .ok (.inr true)
  else if index = -2 then .ok (.inr false)
  else if h : 0 ≤ index ∧ index.toNat < n then .ok (.inl ⟨index.toNat, h.2⟩)
  else .error s!"invalid state index {index}"

def sourceRow {n : Nat} (spec : String × List Int) : Except String (Source.Row (Fin n)) := do
  let moves ← spec.2.mapM position
  match spec.1, moves with
  | "max", first :: rest => return .max first rest
  | "min", first :: rest => return .min first rest
  | "coin", [heads, tails] => return .chance heads tails
  | _, _ => throw s!"invalid source row {spec.1}"

def Fixture.asInput (fixture : Fixture) : Except String (ThresholdInput fixture.rows.size) := do
  let start ← position fixture.start
  let rows ← (List.finRange fixture.rows.size).mapM (fun i => sourceRow fixture.rows[i])
  if h : rows.toArray.size = fixture.rows.size then
    if hd : 0 < fixture.denominator then
      return ⟨⟨rows.toArray, h⟩, start, fixture.numerator, fixture.denominator, hd⟩
    else throw "zero threshold denominator"
  else throw "row count changed"

def Fixture.run (fixture : Fixture) : Except String Json := do
  let input ← fixture.asInput
  let inputBits := CompilationCost.inputBits input
  let some outputBits := ThresholdReduction.compileBinary inputBits
    | throw "binary compiler rejected encoded input"
  let some table := BinaryEncoding.decodeTable outputBits
    | throw "target decoder rejected compiler output"
  if fixture.name == "closed-third-equal" then
    if table != ThresholdReduction.compile input then
      throw "binary path changed the typed table"
    if (ThresholdReduction.compileBinary (inputBits ++ [true])).isSome then
      throw "source decoder accepted trailing bits"
    if (BinaryEncoding.decodeTable (outputBits ++ [true])).isSome then
      throw "target decoder accepted trailing bits"
  let arcs := table.arcs.map fun arc =>
    Json.arr #[toJson arc.src, toJson arc.dst, toJson arc.weight]
  return Json.mkObj [
    ("name", toJson fixture.name), ("start", toJson table.start),
    ("owners", toJson table.owners), ("arcs", toJson arcs)]

def main : IO Unit := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let parse := (Json.parse line).bind (fromJson? (α := Fixture))
    let fixture ← IO.ofExcept parse
    match fixture.run with
    | .ok graph => IO.println graph.compress
    | .error error => throw (IO.userError s!"{fixture.name}: {error}")
