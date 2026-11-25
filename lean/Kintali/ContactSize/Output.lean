module

public import Kintali.ContactSize.Recovery
public import Kintali.InputOutput.Solver

/-! Binary output length of the public solver on valid encodings, including
the direct cases, the terminating trial and prior-zero attacker rows. -/

@[expose] public section
namespace Kintali.ContactSize

open ExactRecovery MarketTrial InputOutput QuoteSearch

def StrategyFits {k m : ℕ} (w : ℕ) (s : Strategy k m) :=
  (∀ j, Fits w (s.coverage j)) ∧ ∀ i j, Fits w (s.attacks i j)

private theorem cleared_fields (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (s : Selection (a.types*a.targets)) (hSelect : SelectionBound a s)
    (z : Strategy a.types a.targets) (success :
      MarketTrial.run a.game valid.1 (sparseView a.game valid.1) s = .cleared z) :
    StrategyFits (strategyWidth (Binary.lengthInput a)) z := by
  unfold MarketTrial.run at success
  dsimp only at success
  split at success
  · cases success
    exact repair_strategy a valid _ _ (sparse_view a valid normal s hSelect)
  · cases success

private theorem emitted {n : ℕ} {Answer : Type} {J : ℕ} (trial : Trial n Answer) (C : Answer → Prop)
    (hit : ∀ state z, trial (select J state) = .cleared z → C z)
    (fuel : ℕ) (state : WeightTable n) (z : Answer) (h : QuoteSearch.run J trial fuel state = some z) :
    C z := by
  induction fuel generalizing state with
  | zero => simp [QuoteSearch.run] at h
  | succ t ih =>
    cases step : trial (select J state) with
    | cleared y =>
      have eq : y = z := Option.some.inj (by simpa only [QuoteSearch.run,step] using h)
      exact eq ▸ hit state y step
    | blocked intervals => exact ih (double state intervals) (by simpa only [QuoteSearch.run,step] using h)

theorem solved_fields (a : Input) (valid : a.Valid) (z : Strategy a.types a.targets)
    (hit : a.game.solve valid.1 = some z) : StrategyFits (strategyWidth (Binary.lengthInput a)) z := by
  let b := strategyWidth (Binary.lengthInput a)
  have h1 : 1 ≤ b := by dsimp only [b,strategyWidth]; omega
  by_cases direct : a.game.DirectCase
  · have eq : a.game.earlyStrategy valid.1 = z := Option.some.inj
      (by simpa only [Game.solve,Game.solveWithTrials,dite_eq_left valid.1,ite_eq_left direct] using hit)
    rw [← eq]
    constructor
    · intro j
      change Fits b (if j ∈ a.game.earlyDefense then 1 else 0)
      split
      · exact Fits.one.mono h1
      · exact Fits.zero.mono h1
    · intro i j
      change Fits b (if j = _ then 1 else 0)
      split
      · exact Fits.one.mono h1
      · exact Fits.zero.mono h1
  · let g := a.game
    let trial := MarketTrial.run g valid.1 (sparseView g valid.1)
    have q : QuoteSearch.run (4*witnessBound g) trial (2*witnessBound g*((grid g).log2+1))
        (initialTable (eligible g valid.1)) = some z := by
      simpa only [Game.solve,Game.solveWithTrials,dite_eq_left valid.1,ite_eq_right direct,
        TrialSetup.run,prepare,QuoteSearch.solve] using hit
    exact emitted trial (StrategyFits b) (fun state x ok =>
      cleared_fields a valid direct _ (driver_selection a state) x ok) _ _ z q

def outputLength (L : ℕ) :=
  let row := L*(2*(5*strategyWidth L+3)+1)
  2*row+1+L*(2*row+1)

/-- Bit length of the actual public equilibrium output. -/
theorem solveBits_length (a : Input) (valid : a.Valid) :
    (solveBits (Binary.input a)).length ≤ outputLength (Binary.lengthInput a) := by
  let L := Binary.lengthInput a
  let B := strategyWidth L
  obtain ⟨z,hit,_⟩ := a.game.solve_correct ((Input.valid_iff a).mp valid).1
  obtain ⟨cov,attack⟩ := solved_fields a valid z hit
  have length := Binary.strategy_width z cov attack
  rw [solveBits_input]
  simp only [InputOutput.solve,dite_eq_left valid.1,hit,Option.map_some,Option.getD_some]
  apply length.trans
  change 2*(a.targets*(2*(5*B+3)+1))+1+a.types*(2*(a.targets*(2*(5*B+3)+1))+1) ≤
    2*(L*(2*(5*B+3)+1))+1+L*(2*(L*(2*(5*B+3)+1))+1)
  have dims := Binary.dimensions a
  gcongr <;> first | exact dims.1 | exact dims.2.1

end Kintali.ContactSize
