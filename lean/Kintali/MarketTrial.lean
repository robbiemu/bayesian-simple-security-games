module

public import Kintali.Recovery
public import Kintali.Theorem1
public import Kintali.ExactRecovery.Pruning
public import Kintali.QuoteSearch.BlockingInterval

/-!
# One restricted market trial

Read the compact coverage and joint attack masses from a sparse contact.
Test the relaxed pattern from those values. If the test succeeds, repair
it to an exact strategy. Otherwise report the blocking quote interval
for each eligible buyer–site pair.
-/

@[expose] public section

namespace Kintali.MarketTrial

open ExactRecovery QuoteSearch

variable {k m : ℕ} (g : Game (Fin k) (Fin m))

def grid : ℕ := gridSize g (contactTolerance g)
def privateScale : ℚ := sigma g (contactTolerance g)

def redirect (hm : 0 < m) (i : Fin k) : Fin m :=
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  outsideTarget g i

theorem redirect_min (hm : 0 < m) (i : Fin k) (j : Fin m) :
    Holdings.outsideCost g (redirect g hm) i ≤ g.cost i j (Holdings.endpoint g j) := by
  let _ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact outsideTarget_min g i j

def witnessBound : ℕ :=
  k + g.positiveTargets.length + k * g.positiveTargets.length

def eligible (hm : 0 < m) : Vector ℕ (k * m) :=
  Vector.ofFn fun p =>
    let (i, j) := finProdFinEquiv.symm p
    eligibleCount g (redirect g hm) (grid g) i j

structure ContactView (k m G : ℕ) where
  pressure : ℚ
  coverage : Fin m → ℚ
  joint : Fin k → Fin m → ℚ
  buyerAccepts : Fin k → Fin m → Quote G → Bool
  siteAccepts : Fin k → Fin m → Quote G → Bool

def pattern (hm : 0 < m) (view : ContactView k m (grid g)) : Pattern (Fin k) (Fin m) :=
  contactPattern g view.coverage (g.bestTarget hm view.coverage) (contactTolerance g)
    (contactTolerance_pos g).le

def relaxedCheck (p : Pattern (Fin k) (Fin m)) (view : ContactView k m (grid g)) : Bool :=
  (List.finRange (exactRows k m)).all fun a =>
    match (rowIndex k m).symm a with
    | .inl r =>
      let c := comparison p r
      decide (c.left.value g view.coverage view.joint view.pressure (contactTolerance g) ≤
        c.right.value g view.coverage view.joint view.pressure (contactTolerance g))
    | .inr () => true

theorem relaxedCheck_spec (p : Pattern (Fin k) (Fin m)) (view : ContactView k m (grid g)) :
    relaxedCheck g p view = true ↔
      Relaxed g p view.coverage view.joint view.pressure (contactTolerance g) := by
  rw [← all_rows_iff]
  simp only [relaxedCheck, List.all_eq_true]
  constructor
  · intro h r
    simpa [Comparison.Holds] using h (rowIndex k m (.inl r)) (List.mem_finRange _)
  · intro h i _
    cases hr : (rowIndex k m).symm i with
    | inl r => simpa [hr, Comparison.Holds] using h r
    | inr u =>
      cases u
      simp

def atOptional {G : ℕ} (accepts : Quote G → Bool) (j : ℕ) : Bool :=
  if h : j < G then accepts (Fin.castSucc ⟨j, h⟩) else false

def blockerIntervals (hm : 0 < m) (view : ContactView k m (grid g)) :
    Vector Interval (k * m) :=
  Vector.ofFn fun p =>
    let (i, j) := finProdFinEquiv.symm p
    intervalFor (atOptional (view.buyerAccepts i j)) (atOptional (view.siteAccepts i j))
      (eligible g hm)[p]

def run (hm : 0 < m) (getContact : Selection (k * m) → ContactView k m (grid g)) :
    Trial (k * m) (Strategy k m) := fun s =>
  let view := getContact s
  let p := pattern g hm view
  if relaxedCheck g p view then
    .cleared (ExactRecovery.repair g p view.coverage view.joint view.pressure (contactTolerance g))
  else .blocked (blockerIntervals g hm view)

def prepare (hm : 0 < m) (getContact : Selection (k * m) → ContactView k m (grid g)) :
    TrialSetup (Strategy k m) :=
  ⟨k * m, grid g, witnessBound g, eligible g hm, run g hm getContact⟩

theorem cleared_correct (hm : 0 < m)
    (getContact : Selection (k * m) → ContactView k m (grid g)) {s : Selection (k * m)}
    {answer : Strategy k m} (h : run g hm getContact s = .cleared answer) :
    g.IsBayesNash answer.coverage answer.attacks := by
  unfold run at h
  dsimp only at h
  split at h
  next hOK =>
    cases h
    exact ExactRecovery.repair_correct g _ (contactTolerance_le g) ((relaxedCheck_spec g _ _).mp hOK)
  next => cases h

end Kintali.MarketTrial
