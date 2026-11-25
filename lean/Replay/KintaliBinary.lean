import Kintali.InputOutput.MeasuredSolver

/-! Newline-delimited bitstreams for the public binary solver replay. -/

open Kintali.InputOutput

def solveBinaryLine (line : String) : Except String String := do
  unless line.endsWith "\n" do
    throw "expected a newline-terminated input bitstream"
  let bits ← (line.dropEnd 1).toString.toList.mapM fun digit =>
    match digit with
    | '0' => pure false
    | '1' => pure true
    | _ => throw "expected only 0 and 1 in the input bitstream"
  let some input := Binary.inputCodec.decode bits
    | throw "cannot decode the input bitstream"
  unless Binary.input input == bits do
    throw "expected a canonical input bitstream"
  let output := (MeasuredSolver.run bits).value
  return String.ofList (output.map fun bit => if bit then '1' else '0')

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result ← IO.ofExcept (solveBinaryLine line)
    stdout.putStrLn result
    stdout.flush
