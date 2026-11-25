module

public import Kintali.InputOutput.Solver
public import Kintali.SearchBounds
public import Kintali.QuoteSearch.DriverWork

/-! # Binary work of the interior-budget quote driver

This theorem composes the adaptive search with a charged implementation
of a restricted trial. The prepared grid, eligible counts and final
strategy conversion are outside the driver's work count.
-/

@[expose] public section

namespace Kintali.InputOutput

open StochasticGames.CompilerRun StochasticGames.BinarySize
open QuoteSearch MarketTrial

def searchWidth (L : ℕ) : ℕ :=
  L*L + 4*Binary.witnesses L + Binary.gridBitBound L + Binary.trialLimit L + 4

def searchSlots (L trialSlots : ℕ) : ℕ :=
  let pairs := L*L
  let j := 4 * Binary.witnesses L
  let t := Binary.trialLimit L
  1 + t * (2 + DriverWork.selectLimit pairs j t + trialSlots +
    DriverWork.updateLimit pairs t)

private theorem searchSlots_bound {L N J T B : ℕ} (dim : N ≤ L*L)
    (jBound : J ≤ 4 * Binary.witnesses L) (tBound : T ≤ Binary.trialLimit L) :
    1 + T * (2 + DriverWork.selectLimit N J T + B + DriverWork.updateLimit N T) ≤
      searchSlots L B := by
  have hs : DriverWork.selectLimit N J T ≤
      DriverWork.selectLimit (L*L) (4 * Binary.witnesses L) (Binary.trialLimit L) := by
    unfold DriverWork.selectLimit Runs.selectionSlots
    gcongr
  have hu : DriverWork.updateLimit N T ≤ DriverWork.updateLimit (L*L) (Binary.trialLimit L) := by
    unfold DriverWork.updateLimit
    gcongr
  unfold searchSlots
  dsimp only
  exact Nat.add_le_add_left (Nat.mul_le_mul tBound
    (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left hs 2) B) hu)) 1

def interiorRun (a : Input) (hm : 0 < a.targets)
    (measure : DriverWork.ChargedTrial (a.types * a.targets) (Strategy a.types a.targets)) :
    Run (Option (Strategy a.types a.targets)) :=
  let H := witnessBound a.game
  let G := grid a.game
  DriverWork.search (4*H) measure (2*H*(G.log2+1))
    (initialTable (eligible a.game hm))

theorem interior_value (a : Input) (hm : 0 < a.targets) (normal : ¬a.game.DirectCase)
    (measure : DriverWork.ChargedTrial (a.types * a.targets) (Strategy a.types a.targets))
    (exactTrial : ∀ s, (measure s).value = MarketTrial.run a.game hm (sparseView a.game hm) s) :
    (interiorRun a hm measure).value = a.game.solve hm := by
  have eq : (fun s => (measure s).value) = MarketTrial.run a.game hm (sparseView a.game hm) :=
    funext exactTrial
  simp only [interiorRun, DriverWork.search_value, eq, Game.solve, Game.solveWithTrials,
    dite_eq_left hm, ite_eq_right normal, TrialSetup.run, MarketTrial.prepare, QuoteSearch.solve]

theorem interior_work (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (measure : DriverWork.ChargedTrial (a.types * a.targets) (Strategy a.types a.targets))
    (exactTrial : ∀ s, (measure s).value = MarketTrial.run a.game valid.1 (sparseView a.game valid.1) s)
    {B W : ℕ} (each : ∀ s,
      ValidSelection (4*witnessBound a.game) (eligible a.game valid.1) s → (measure s).Bound B W) :
    (interiorRun a valid.1 measure).Bound (searchSlots (Binary.lengthInput a) B)
      (searchWidth (Binary.lengthInput a) + W) := by
  let L := Binary.lengthInput a
  let H := witnessBound a.game
  let G := grid a.game
  let J := 4*H
  let T := 2*H*(G.log2+1)
  let N := a.types*a.targets
  let Q := eligible a.game valid.1
  let w := searchWidth L + W
  have vg : a.game.Valid := ((a.valid_iff).mp valid).1
  have spec := prepare_correct a.game vg normal (sparseView a.game valid.1)
    (fun s _ => sparseView_matches a.game vg normal s)
  obtain ⟨_,gridFits,_,_,claims⟩ := spec
  have qBound (p : Fin N) : Q[p] ≤ G := gridFits p
  have d := Binary.dimensions a
  have dim : N ≤ L*L := Nat.mul_le_mul d.2.1 d.1
  have jBound : J ≤ 4 * Binary.witnesses L := Nat.mul_le_mul_left 4 (Binary.witness_bound a)
  have tBound : T ≤ Binary.trialLimit L := Binary.trials_bound a valid
  have nw := (size_le_self N).trans dim
  have jw := (size_le_self J).trans jBound
  have gw := Binary.grid_size a valid
  have fits : DriverWork.widthLimit N J G T ≤ w := by
    unfold DriverWork.widthLimit w searchWidth
    change G.size ≤ Binary.gridBitBound L at gw
    omega
  have intervals (s : Selection N) (ranges : Vector Interval N) (hs : ValidSelection J Q s)
      (hr : (measure s).value = .blocked ranges) (p : Fin N) :
      ranges[p].lo ≤ ranges[p].hi ∧ ranges[p].hi ≤ G := by
    have hc := (claims.blocked s ranges hs ((exactTrial s).symm.trans hr)).1 p
    exact ⟨hc.1, hc.2.1.trans (qBound p)⟩
  have trialFit (s : Selection N) (hs : ValidSelection J Q s) : (measure s).Bound B w :=
    (each s hs).weaken le_rfl (Nat.le_add_left W (searchWidth L))
  have circ := DriverWork.search_bound J G T measure Q qBound fits trialFit intervals
  have slots := searchSlots_bound (B := B) dim jBound tBound
  show (DriverWork.search J measure T (initialTable Q)).Bound (searchSlots L B) w
  exact ⟨circ.1.trans slots, circ.2⟩

end Kintali.InputOutput
