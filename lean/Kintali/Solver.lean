module

public import Kintali.TrialCorrectness
public import Kintali.QuotaSweep.SparseContact
public import Kintali.QuotaSweep.LayoutTables
public import Kintali.ExactRecovery.SparseView

/-!
# Exact Bayes–Nash equilibrium

Dispatch the direct cases. For an interior budget, run the restricted
market search with a grouped quota sweep in every trial. The trial
checks its relaxed point and repairs it to an exact strategy when
the check succeeds.
-/

@[expose] public section

namespace Kintali

open ExactRecovery QuotaSweep
open MarketTrial

variable {k m : ℕ}

/-- Reading a successful contact or testing a blocker uses the same saved
coverage and joint mass tables throughout the trial. -/
@[noinline] def MarketTrial.contactViewFromTables {G : ℕ}
    (pressure : ℚ) (coverage : Vector ℚ m) (joint : Vector (Vector ℚ m) k)
    (buyer : Fin k → Fin m → Quote G → Bool)
    (site : (Fin m → ℚ) → Fin k → Fin m → Quote G → Bool) :
    ContactView k m G :=
  let row := fun j : Fin m => coverage[j.val]
  ⟨pressure, row, fun i j => joint[i.val][j.val], buyer, site row⟩

def MarketTrial.sparseView (g : Game (Fin k) (Fin m)) (hm : 0 < m)
    (s : QuoteSearch.Selection (k * m)) : ContactView k m (grid g) :=
  let redirectTo := redirect g hm
  let σ := privateScale g
  let L := (Sparse.selectedLayout (G := grid g) g redirectTo s).stored
  let z := Sparse.selectedContact (G := grid g) g redirectTo s σ
  let coverage := Vector.ofFn (Sparse.siteCoverage g σ L z.allocation)
  let joint := Vector.ofFn fun i => Vector.ofFn (Sparse.attackJoint L redirectTo z.allocation i)
  contactViewFromTables z.pressure coverage joint
    (Sparse.buyerAcceptsQuote g Fin.val Fin.val L z.allocation)
    (fun x => Sparse.siteAcceptsQuote x Fin.val L z.allocation)

theorem MarketTrial.sparseView_eq (g : Game (Fin k) (Fin m)) (hm : 0 < m)
    (s : QuoteSearch.Selection (k * m)) :
    let redirectTo := redirect g hm
    let σ := privateScale g
    let L := Sparse.selectedLayout (G := grid g) g redirectTo s
    let z := Sparse.selectedContact (G := grid g) g redirectTo s σ
    let coverage := Sparse.siteCoverage g σ L z.allocation
    sparseView g hm s =
      ⟨z.pressure, coverage, Sparse.attackJoint L redirectTo z.allocation,
        Sparse.buyerAcceptsQuote g Fin.val Fin.val L z.allocation,
        Sparse.siteAcceptsQuote coverage Fin.val L z.allocation⟩ := by
  dsimp only
  simp only [sparseView, contactViewFromTables, Sparse.Layout.stored_eq, Vector.getElem_ofFn]

theorem MarketTrial.sparseView_matches (g : Game (Fin k) (Fin m)) (valid : g.Valid)
    (normal : ¬g.DirectCase) (s : QuoteSearch.Selection (k * m)) :
    ∃ X, Matches (g := g) valid.targets s (sparseView g valid.targets s) X := by
  let redirectTo := redirect g valid.targets
  let σ := privateScale g
  let L := Sparse.selectedLayout (G := grid g) g redirectTo s
  let P := Sparse.intervalGroups (Sparse.partition (G := grid g) g redirectTo s)
  let z := Sparse.selectedContact (G := grid g) g redirectTo s σ
  let X := Sparse.expandedAllocation g σ L P z.allocation
  have hσ : 0 < σ := sigma_pos g (contactTolerance_pos g)
  have hG : 0 < grid g := gridSize_pos g (contactTolerance g)
  have small (j : Fin m) : g.gain j * σ < 1 :=
    (gain_sigma_le g (contactTolerance_pos g).le j).trans_lt (contactTolerance_lt_one g)
  obtain ⟨_, hPressure, _, hStable, hCov, hBudget⟩ :=
    Sparse.selectedContact_correct g redirectTo s valid normal σ hσ hG small
  have hRep := Sparse.represents_expandedAllocation g σ L P z.allocation
  have hPhysical : (∑ j, (Expanded.holdings X).physical g σ j) = g.resources := by
    simpa only [hCov] using hBudget
  have hContact := Expanded.stableContact hStable hG hσ hPressure.le
    (redirect_min g valid.targets) hPhysical
  rw [sparseView_eq]
  refine ⟨X, ⟨hStable, hPressure.le, hPhysical, funext hCov,
    Sparse.attackJoint_eq hRep redirectTo, ?_, ?_⟩⟩
  · intro i j q _
    exact Sparse.buyerAcceptsQuote_iff g Fin.val Fin.val hRep i j q.castSucc
  · intro i j q hel
    exact Sparse.siteAcceptsQuote_iff Fin.val Fin.val Fin.val_injective hRep hContact
      (Sparse.siteCoverage g σ L z.allocation) (funext hCov) i j hel.1 q.castSucc

namespace Game

def solve (g : Game (Fin k) (Fin m)) (hm : 0 < m) : Option (Strategy k m) :=
  g.solveWithTrials (fun _ => prepare g hm (sparseView g hm))

/-- The executable algorithm computes exact compact equilibrium strategies
for every valid rational game. -/
theorem solve_correct (g : Game (Fin k) (Fin m)) (valid : g.Valid) :
    ∃ s, g.solve valid.targets = some s ∧ g.IsBayesNash s.coverage s.attacks :=
  g.solveWithTrials_correct _ valid fun normal =>
    prepare_correct g valid normal (sparseView g valid.targets)
      (fun s _ => sparseView_matches g valid normal s)

end Game
end Kintali
