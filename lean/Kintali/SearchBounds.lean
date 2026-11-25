module

public import Kintali.InputOutput.Grid
public import Kintali.QuoteSearch.TraceBounds
public import Kintali.TrialSize

/-! # Polynomial sizes of the actual search states and restricted books -/

@[expose] public section

namespace Kintali.InputOutput.Binary

open ExactRecovery QuoteSearch MarketTrial

def witnesses (L : ℕ) : ℕ := 2 * L + L * L
def trialLimit (L : ℕ) : ℕ := 2 * witnesses L * (gridBitBound L + 1)
def realLimit (L : ℕ) : ℕ := L * L * (4 * witnesses L)
def recordLimit (L : ℕ) : ℕ := 3 * realLimit L + 4 * L

theorem witness_bound (a : Input) : witnessBound a.game ≤ witnesses (lengthInput a) := by
  let L := lengthInput a
  have atMost : a.game.positiveTargets.length ≤ a.targets := by
    exact (List.length_filter_le _ _).trans (by simp)
  have k := (dimensions a).2.1
  have m := atMost.trans (dimensions a).1
  unfold witnessBound witnesses
  change a.types + a.game.positiveTargets.length +
    a.types * a.game.positiveTargets.length ≤ 2 * L + L * L
  calc
    _ ≤ L + L + L * L := by gcongr
    _ = _ := by omega

theorem trials_bound (a : Input) (h : a.Valid) :
    2 * witnessBound a.game * ((grid a.game).log2 + 1) ≤ trialLimit (lengthInput a) := by
  have g := grid_size a h
  have log : (grid a.game).log2 ≤ (grid a.game).size := by
    by_cases hz : grid a.game = 0
    · simp [hz]
    · exact ((Nat.log2_lt hz).mpr (Nat.lt_size_self _)).le
  unfold trialLimit
  gcongr <;> first | exact witness_bound a | omega

theorem real_bound (a : Input) (hm : 0 < a.targets)
    (s : Selection (a.types * a.targets)) (J : ℕ) (hJ : 0 < J) (lim : J ≤ 4 * witnesses (lengthInput a))
    (sel : ∀ p : Fin (a.types * a.targets), s[p].length ≤ J - 1) :
    (Sparse.realBids (G := grid a.game) a.game (redirect a.game hm) s).card ≤ realLimit (lengthInput a) := by
  refine (Sparse.realBids_count a.game (redirect a.game hm) s hJ sel).trans ?_
  unfold realLimit
  gcongr <;> first | exact (dimensions a).1 | exact (dimensions a).2.1

theorem records_bound (a : Input) (hm : 0 < a.targets)
    (s : Selection (a.types * a.targets)) (J : ℕ) (hJ : 0 < J) (lim : J ≤ 4 * witnesses (lengthInput a))
    (sel : ∀ p : Fin (a.types * a.targets), s[p].length ≤ J - 1) :
    Fintype.card (Sparse.R (Fin a.types) (Fin a.targets)
      (Fin (Sparse.realOrder (G := grid a.game) a.game (redirect a.game hm) s).length)
      (Sparse.IntervalGroup (Sparse.partition (G := grid a.game) a.game (redirect a.game hm) s))) ≤
        recordLimit (lengthInput a) := by
  have real := real_bound a hm s J hJ lim sel
  have groups := Sparse.groups_count (G := grid a.game) a.game (redirect a.game hm) s
  rw [Sparse.record_count]
  simp only [Fintype.card_fin, Sparse.realOrder_length]
  unfold recordLimit
  have k := (dimensions a).2.1
  have m := (dimensions a).1
  omega

end Kintali.InputOutput.Binary
