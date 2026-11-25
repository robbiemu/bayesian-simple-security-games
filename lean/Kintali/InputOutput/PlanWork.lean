module

public import Kintali.InputOutput.PrepareWork
public import Kintali.InputOutput.CoreWork
public import Kintali.QuoteSearch.ClockWork

/-! # Attach the executable trial clock to the prepared quote counts -/

@[expose] public section

namespace Kintali.InputOutput.PlanWork

open StochasticGames.CompilerRun StochasticGames.BinarySize
open QuoteSearch.ClockWork CoreWork

def clock (a : Input) (P : PrepareWork.Prepared a.types a.targets) : Run (Prepared a) := do
  let q ← natMul 4 P.witness
  let log ← logRun P.scales.grid
  let rounds ← natAdd log 1
  let twice ← natMul 2 P.witness
  let fuel ← natMul twice rounds
  step 0 ⟨q, fuel, P.counts⟩

theorem clock_value (a : Input) (hm : 0 < a.targets) (P : PrepareWork.Prepared a.types a.targets)
    (hg : P.scales.grid = MarketTrial.grid a.game)
    (hw : P.witness = MarketTrial.witnessBound a.game)
    (hc : P.counts = MarketTrial.eligible a.game hm) :
    (clock a P).value = prepared a hm := by
  simp [clock, prepared, natMul, natAdd, hg, hw, hc]

def clockSlots (B : ℕ) := 6 + 3*B
def clockWidth (B H : ℕ) := B+H+4

theorem clock_work (a : Input) (P : PrepareWork.Prepared a.types a.targets) {B H : ℕ}
    (g : P.scales.grid.size ≤ B) (h : P.witness.size ≤ H) :
    (clock a P).Bound (clockSlots B) (clockWidth B H) := by
  let W := clockWidth B H
  have hg : P.scales.grid.size ≤ W := g.trans (by unfold W clockWidth; omega)
  have one : 1 ≤ W := by unfold W clockWidth; omega
  have lw := logRun_work P.scales.grid hg one
  have hw : P.witness.size ≤ W := h.trans (by unfold W clockWidth; omega)
  have log := (Nat.size_le_size (Nat.log2_le_self P.scales.grid)).trans g
  have grow := size_succ_le P.scales.grid.log2
  have log' : (P.scales.grid.log2+1).size ≤ W := by unfold W clockWidth; omega
  have twice := size_mul_le 2 P.witness
  have twice' : (2 * P.witness).size ≤ W := by
    unfold W clockWidth
    have : (2 : ℕ).size = 2 := rfl
    omega
  have hurdle : P.scales.grid.log2 ≤ B := by
    by_cases hz : P.scales.grid = 0
    · simp [hz]
    · exact ((Nat.log2_lt hz).mpr (Nat.lt_size_self _)).le.trans g
  constructor
  · simp only [clock, natMul, natAdd, Run.bind_slots, step_slots]
    have := lw.1
    unfold clockSlots
    omega
  · simp only [clock, natMul, natAdd, Run.bind_width, step_width, step_value, logRun_value, max_le_iff]
    change (3 ≤ W ∧ P.witness.size ≤ W) ∧ _ ∧ (_ ≤ W ∧ 1 ≤ W) ∧
      (2 ≤ W ∧ P.witness.size ≤ W) ∧ (_ ≤ W ∧ _ ≤ W) ∧ 0 ≤ W
    have logFit : P.scales.grid.log2.size ≤ W := log.trans (by unfold W clockWidth; omega)
    exact ⟨⟨by unfold W clockWidth; omega,hw⟩,lw.2,⟨logFit,one⟩,
      ⟨by unfold W clockWidth; omega,hw⟩,⟨twice',log'⟩,Nat.zero_le _⟩

end Kintali.InputOutput.PlanWork
