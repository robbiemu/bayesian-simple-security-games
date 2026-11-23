module

public import StochasticGames.ReachabilityThreshold
public import StochasticGames.IntegerAtoms
public import StochasticGames.MeanPayoffGraph
public import StochasticGames.MeanPayoffThreshold
import all StochasticGames.IntegerAtoms

/-! # The reduction at the level of certificates

The Bellman module identifies the source's strict threshold certificate.
Here a bounded max-average system is compiled to integer weighted rows.
Choosing one term in each such row gives a graph with a potential precisely
when its closed walks are nonnegative. The final threshold module handles
the integer weight transformation that reverses a weak threshold.
-/

public section

namespace StochasticGames.Reduction

open AverageFeasibility AtomEncoding IntegerAtoms MeanPayoffGraph

variable {ν : Type*}

abbrev Row (rows : List (IntAtom ν)) := Fin rows.length

abbrev Selection (rows : List (IntAtom ν)) :=
  (i : Row rows) → Fin (rows.get i).terms.length

def selectedTerm (rows : List (IntAtom ν)) (choose : Selection rows) (i : Row rows) : ν × ℤ :=
  (rows.get i).terms.get (choose i)

def SelectedGraphNonnegative (rows : List (IntAtom ν)) (choose : Selection rows) : Prop :=
  ClosedRowWalks (fun i => (rows.get i).lhs)
    (fun i => (selectedTerm rows choose i).1)
    (fun i => (selectedTerm rows choose i).2)

/-- Allow arbitrary finite fan-in by choosing one term at each row position. -/
theorem feasible_iff_selected_graph [Fintype ν] (rows : List (IntAtom ν)) :
    (∃ p : ν → ℤ, IntegerAtoms.RowsHold rows p) ↔
      ∃ choose : Selection rows, SelectedGraphNonnegative rows choose := by
  constructor
  · rintro ⟨p, holds⟩
    have choiceExists (i : Row rows) :
        ∃ j : Fin (rows.get i).terms.length,
          p (rows.get i).lhs ≤ p ((rows.get i).terms.get j).1 + ((rows.get i).terms.get j).2 := by
      obtain ⟨term, termMem, satisfied⟩ := holds (rows.get i) (List.get_mem _ i)
      obtain ⟨j, equals⟩ := List.get_of_mem termMem
      exact ⟨j, by simpa only [equals] using satisfied⟩
    let choose : Selection rows := fun i => Classical.choose (choiceExists i)
    refine ⟨choose, (row_potential_iff _ _ _).1 ⟨p, fun i => ?_⟩⟩
    have term := Classical.choose_spec (choiceExists i)
    simpa only [choose, selectedTerm] using term.trans_eq (add_comm _ _)
  · rintro ⟨choose, graph⟩
    obtain ⟨p, potential⟩ := (row_potential_iff _ _ _).2 graph
    refine ⟨p, ?_⟩
    intro row member
    obtain ⟨i, rfl⟩ := List.get_of_mem member
    refine ⟨selectedTerm rows choose i, List.get_mem _ _, ?_⟩
    exact (potential i).trans_eq (add_comm _ _)

/-- The exact finite-quantity decision is equivalent to a positional
certificate of the selected integer graph produced by the compiler. -/
theorem exact_iff_selected_graph [Fintype ν] [DecidableEq ν] (system : System ν)
    {width : ℚ} (widthNonneg : 0 ≤ width) (inputWidths : system.InputsBounded width)
    (bounded : ∃ B : ℚ, ∀ x, system.HardRows x → ∀ i, |x i| ≤ B) :
    let rows := encode (allAtoms system width (Precision.rounds width (MaxAverageReduction.gap system)))
    (∃ x, system.Exact x) ↔ ∃ choose : Selection rows, SelectedGraphNonnegative rows choose :=
  (exact_iff_integer system widthNonneg inputWidths bounded).trans (feasible_iff_selected_graph _)

end StochasticGames.Reduction
