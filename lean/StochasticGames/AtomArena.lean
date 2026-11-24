module

public import StochasticGames.IntegerAtoms
public import StochasticGames.MeanPayoffGame
public import StochasticGames.MeanPayoffGraph
import all StochasticGames.MeanPayoffGame
import all StochasticGames.IntegerAtoms
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

/-! # A single deterministic game for the integer rows

The fresh start reaches any variable. At a variable Min picks a row, and at the
row Max picks a term. Distinct occurrences of a term give distinct arcs.
-/

@[expose] public section

namespace StochasticGames.AtomArena

open IntegerAtoms MeanPayoff

variable {ν : Type*}

abbrev Row (rows : List (IntAtom ν)) := Fin rows.length
abbrev Term (rows : List (IntAtom ν)) (r : Row rows) := Fin (rows.get r).terms.length
abbrev Vertex (rows : List (IntAtom ν)) := Option (ν ⊕ Row rows)
abbrev Isolated (rows : List (IntAtom ν)) :=
  {v : ν // ∀ r : Row rows, (rows.get r).lhs ≠ v}

abbrev Edge (rows : List (IntAtom ν)) :=
  ν ⊕ (Row rows ⊕ ((Σ r : Row rows, Term rows r) ⊕ Isolated rows))

def enter {rows : List (IntAtom ν)} (r : Row rows) : Edge rows := .inr (.inl r)
def reply {rows : List (IntAtom ν)} (r : Row rows) (j : Term rows r) : Edge rows :=
  .inr (.inr (.inl ⟨r, j⟩))
def idle {rows : List (IntAtom ν)} (v : Isolated rows) : Edge rows := .inr (.inr (.inr v))

def src {rows : List (IntAtom ν)} : Edge rows → Vertex rows
  | .inl _ => none
  | .inr (.inl r) => some (.inl (rows.get r).lhs)
  | .inr (.inr (.inl ⟨r, _⟩)) => some (.inr r)
  | .inr (.inr (.inr v)) => some (.inl v.val)

def dst {rows : List (IntAtom ν)} : Edge rows → Vertex rows
  | .inl v => some (.inl v)
  | .inr (.inl r) => some (.inr r)
  | .inr (.inr (.inl ⟨r, j⟩)) => some (.inl ((rows.get r).terms.get j).1)
  | .inr (.inr (.inr v)) => some (.inl v.val)

def weight {rows : List (IntAtom ν)} : Edge rows → ℤ
  | .inr (.inr (.inl ⟨r, j⟩)) => ((rows.get r).terms.get j).2
  | _ => 0

def isMax {rows : List (IntAtom ν)} : Vertex rows → Bool
  | some (.inr _) => true
  | _ => false

def game [Nonempty ν] (rows : List (IntAtom ν))
    (nonemptyTerms : ∀ r : Row rows, 0 < (rows.get r).terms.length) :
    Game (Vertex rows) (Edge rows) where
  src := src
  dst := dst
  weight := weight
  isMax := isMax
  outgoing := by
    rintro (_ | v | r)
    · exact ⟨.inl (Classical.arbitrary ν), rfl⟩
    · by_cases h : ∃ r : Row rows, (rows.get r).lhs = v
      · obtain ⟨r, hr⟩ := h
        exact ⟨enter r, by
          change (some (Sum.inl (rows.get r).lhs) : Vertex rows) = some (Sum.inl v)
          rw [hr]⟩
      · exact ⟨idle ⟨v, fun r hr => h ⟨r, hr⟩⟩, rfl⟩
    · exact ⟨reply r ⟨0, nonemptyTerms r⟩, rfl⟩

noncomputable instance edgeFintype [Fintype ν] (rows : List (IntAtom ν)) :
    Fintype (Edge rows) := by
  classical
  infer_instance

variable [Nonempty ν] {rows : List (IntAtom ν)}
variable (ok : ∀ r : Row rows, 0 < (rows.get r).terms.length)

private noncomputable def termPolicy (pick : ∀ r : Row rows, Term rows r) :
    (game rows ok).Policy
  | some (.inr r) => ⟨reply r (pick r), rfl⟩
  | none => ⟨.inl (Classical.arbitrary ν), rfl⟩
  | some (.inl v) =>
    ⟨Classical.choose ((game rows ok).outgoing (some (.inl v))),
      Classical.choose_spec ((game rows ok).outgoing (some (.inl v)))⟩

omit [Nonempty ν] in
private theorem reply_only {e : Edge rows} (r : Row rows) (h : src e = some (.inr r)) :
    ∃ j : Term rows r, e = reply r j := by
  rcases e with v | i | ⟨i, j⟩ | v
  · simp [src] at h
  · simp [src] at h
  · have hi : i = r := by simpa [src] using h
    subst i
    exact ⟨j, rfl⟩
  · simp [src] at h

/-- Feasible integer rows are exactly the positional potential certificates
in the constructed game at its fresh start. -/
theorem rows_iff_certificate [Finite ν] :
    (∃ x, RowsHold rows x) ↔ (game rows ok).Certificate none := by
  classical
  constructor
  · rintro ⟨x, holds⟩
    have supported (r : Row rows) : ∃ j : Term rows r,
        x (rows.get r).lhs ≤ x ((rows.get r).terms.get j).1 + ((rows.get r).terms.get j).2 := by
      obtain ⟨t, mem, le⟩ := holds (rows.get r) (List.get_mem _ r)
      obtain ⟨j, rfl⟩ := List.get_of_mem mem
      exact ⟨j, le⟩
    choose pick good using supported
    obtain ⟨floor, below⟩ := Finite.bddBelow_range x
    let h : Vertex rows → ℤ
      | none => floor
      | some (.inl v) => x v
      | some (.inr r) => x (rows.get r).lhs
    refine ⟨termPolicy ok pick, fun _ => True, h, trivial, fun e allowed _ => ⟨trivial, ?_⟩⟩
    rcases e with v | r | ⟨r, j⟩ | v
    · simpa [game, src, dst, weight, h] using below (Set.mem_range_self v)
    · simp [game, src, dst, weight, h]
    · have eq := allowed (by rfl)
      change reply r j = reply r (pick r) at eq
      have same : j = pick r := by simpa [reply] using eq
      subst j
      simpa [game, src, dst, weight, h, add_comm] using good r
    · simp [game, src, dst, weight, h]
  · rintro ⟨policy, region, h, start, stable⟩
    have allVariables (v : ν) : region (some (.inl v)) :=
      (stable (.inl v) (by simp [Game.Allowed, game, src, isMax]) start).1
    refine ⟨fun v => h (some (.inl v)), fun atom mem => ?_⟩
    obtain ⟨r, rfl⟩ := List.get_of_mem mem
    have previous := stable (enter r) (by simp [Game.Allowed, game, enter, src, isMax])
      (allVariables (rows.get r).lhs)
    let e := policy (some (.inr r))
    obtain ⟨j, eq⟩ := reply_only r e.property
    have allowed : (game rows ok).Allowed policy (reply r j) := by
      intro _
      exact eq.symm
    have next := (stable (reply r j) allowed previous.1).2
    refine ⟨(rows.get r).terms.get j, List.get_mem _ j, ?_⟩
    have entered := previous.2
    change h (some (.inl (rows.get r).lhs)) ≤ 0 + h (some (.inr r)) at entered
    change h (some (.inr r)) ≤
      ((rows.get r).terms.get j).2 + h (some (.inl ((rows.get r).terms.get j).1)) at next
    exact (by simpa only [zero_add] using entered :
      h (some (.inl (rows.get r).lhs)) ≤ h (some (.inr r))).trans
      (next.trans_eq (add_comm _ _))

end StochasticGames.AtomArena
