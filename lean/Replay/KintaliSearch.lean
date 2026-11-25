import Kintali.Solver
import Kintali.InputOutput.MeasuredSolver

open Kintali

namespace KintaliReplay

/-- A failure reveals that the fixed witness quote lies in [3,4).
The count is large enough that this replay relies on compressed runs. -/
def oneWitness : QuoteSearch.Trial 1 ℕ := fun selected =>
  if 3 ∈ selected[0] then .cleared 3 else .blocked #v[⟨3, 4⟩]

#guard QuoteSearch.solve 1 (2 ^ 80) oneWitness #v[2 ^ 80] == some 3

def game : Game (Fin 1) (Fin 2) :=
  ⟨1, fun _ => 1, fun _ _ => 0, fun _ _ => 1, fun _ => 1⟩

def pattern : ExactRecovery.Pattern (Fin 1) (Fin 2) :=
  ⟨fun _ => 1, fun _ _ => true, fun _ => rfl, fun _ => .balanced⟩

def rounded : Strategy 1 2 :=
  let e := ExactRecovery.contactTolerance game
  let x (j : Fin 2) := if j = 0 then 1 / 2 + e / 4 else 1 / 2 - e / 4
  ExactRecovery.repair game pattern x (fun _ _ => 1 / 2) (1 / 2) e

#guard (List.ofFn rounded.coverage) == [1 / 2, 1 / 2]
#guard (List.ofFn (rounded.attacks 0)) == [1 / 2, 1 / 2]

/-- An interior-budget game goes through the grouped sweep, search and repair. -/
def flatCosts : Game (Fin 1) (Fin 2) :=
  { game with slope := fun _ _ => 0 }

#guard (flatCosts.solve (by decide)).map (fun s => List.ofFn s.coverage) == some [1, 0]

/-- A positive-slope trial with a large binary grid still enumerates
only its sparse selected quotes. -/
def affineCosts : Game (Fin 1) (Fin 2) :=
  { game with intercept := fun _ j => if j.val = 1 then 5 else 0 }

#guard 1000 < (MarketTrial.grid affineCosts).size
#guard (affineCosts.solve (by decide)).map (fun s =>
  (List.ofFn s.coverage, List.ofFn (s.attacks 0))) == some ([1, 0], [1, 0])

def zeroGain : Game (Fin 2) (Fin 2) :=
  ⟨1, fun i => if i = 0 then 1 else 0,
    fun i j => if i.val = j.val then 5 else 0, fun _ _ => 0, fun _ => 0⟩

#guard (zeroGain.solve (by decide)).map (fun s =>
  (List.ofFn s.coverage, List.ofFn fun i => List.ofFn (s.attacks i))) ==
    some ([1, 0], [[0, 1], [1, 0]])

open InputOutput

def measuredAffine : List Bool := Binary.input (writeGame affineCosts)
def measuredDirect : List Bool := Binary.input (writeGame { affineCosts with resources := 0 })

#guard (MeasuredSolver.run measuredAffine).value == Binary.output ([1, 0], [[1, 0]])
#guard (MeasuredSolver.run measuredDirect).value == Binary.output ([0, 0], [[1, 0]])
#guard (MeasuredSolver.run (Binary.input (0, [], []))).value == Binary.output ([], [])
#guard (MeasuredSolver.run []).value == []

end KintaliReplay
