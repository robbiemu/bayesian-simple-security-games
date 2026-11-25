module

public import Kintali.Preprocessing
public import Kintali.QuoteSearch.Algorithm

/-!
# The structure of Theorem 1

Solve the direct cases of §1 first. For an interior budget, prepare
the restricted-market trial and run the bounded quote search of §3.
A successful trial already returns the compact exact strategies.

The theorem in this file takes the verified trial construction as an
explicit premise. The market sweep, quote witnesses, and exact recovery
provide the component proofs of that premise.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali

structure TrialSetup (Answer : Type*) where
  pairs : ℕ
  gridSize : ℕ
  witnessBound : ℕ
  eligibleQuotes : Vector ℕ pairs
  trial : QuoteSearch.Trial pairs Answer

namespace TrialSetup

variable {Answer : Type*}

def run (S : TrialSetup Answer) : Option Answer :=
  QuoteSearch.solve S.witnessBound S.gridSize S.trial S.eligibleQuotes

def Correct (S : TrialSetup Answer) (accept : Answer → Prop) : Prop :=
  0 < S.witnessBound ∧ (∀ p : Fin S.pairs, S.eligibleQuotes[p] ≤ S.gridSize) ∧
    ∃ W : Finset (QuoteSearch.BidIndex S.pairs),
      W.card ≤ S.witnessBound ∧
        QuoteSearch.TrialSpec (4 * S.witnessBound) S.eligibleQuotes S.trial W accept

theorem run_correct {S : TrialSetup Answer} {accept : Answer → Prop}
    (h : S.Correct accept) : ∃ a, S.run = some a ∧ accept a := by
  obtain ⟨hPositive, hGrid, W, hWitness, hTrial⟩ := h
  exact QuoteSearch.solve_correct hPositive hWitness hGrid hTrial

end TrialSetup

namespace Game

variable {k m : ℕ} (g : Game (Fin k) (Fin m))

structure Valid : Prop where
  targets : 0 < m
  budget : g.resources ≤ m
  prior_nonneg : ∀ i, 0 ≤ g.prior i
  prior_sum : (∑ i, g.prior i) = 1
  gain_nonneg : ∀ j, 0 ≤ g.gain j
  slope_nonneg : ∀ i j, 0 ≤ g.slope i j

def DirectCase : Prop :=
  g.resources = 0 ∨ g.resources = m ∨ g.positiveTargets.length ≤ g.resources

instance : Decidable g.DirectCase :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- First dispatch the §1 cases. At an interior budget the trial
constructor supplies the market behind §2 and §3. -/
def solveWithTrials (prepare : Unit → TrialSetup (Strategy k m)) : Option (Strategy k m) :=
  if hm : 0 < m then
    if g.DirectCase then some (g.earlyStrategy hm)
    else (prepare ()).run
  else none

theorem solveWithTrials_correct (prepare : Unit → TrialSetup (Strategy k m))
    (valid : g.Valid)
    (hInterior : ¬g.DirectCase →
      (prepare ()).Correct (fun s => g.IsBayesNash s.coverage s.attacks)) :
    ∃ s, g.solveWithTrials prepare = some s ∧ g.IsBayesNash s.coverage s.attacks := by
  by_cases hDirect : g.DirectCase
  · refine ⟨g.earlyStrategy valid.targets, ?_, ?_⟩
    · simp [solveWithTrials, valid.targets, hDirect]
    · exact g.earlyStrategy_correct valid.targets valid.budget valid.prior_nonneg valid.gain_nonneg hDirect
  · obtain ⟨s, hsolve, heq⟩ := TrialSetup.run_correct (hInterior hDirect)
    exact ⟨s, by simpa [solveWithTrials, valid.targets, hDirect] using hsolve, heq⟩

end Game
end Kintali
