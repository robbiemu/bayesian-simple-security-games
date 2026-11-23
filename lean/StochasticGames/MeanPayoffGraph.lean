module

public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Order.Int.LeastGreatest
import Mathlib.Tactic.Linarith

/-!
# Potentials for a finite integer-weighted directed graph

A potential is feasible when it satisfies every directed edge inequality.
Telescoping gives one implication. For the converse, erase closed segments
of a walk before taking the minimum weight over all walks from a vertex.
The empty walk represents stopping immediately at a zero-cost sink.
-/

@[expose] public section

namespace StochasticGames.MeanPayoffGraph

open Quiver

variable {V : Type*} [Quiver V] (w : ∀ {i j : V}, (i ⟶ j) → ℤ)

def Feasible (p : V → ℤ) : Prop := ∀ {i j : V} (e : i ⟶ j), p i ≤ w e + p j

def NonnegativeClosedWalks : Prop := ∀ (i : V) (q : Path i i), 0 ≤ q.addWeight w

/-- A simple cycle consists of a walk with distinct vertices and a final edge
back to its starting vertex. Self-loops are included. -/
def NonnegativeSimpleCycles : Prop :=
  ∀ {i j : V} (q : Path i j) (e : j ⟶ i), q.vertices.Nodup → 0 ≤ (q.cons e).addWeight w

theorem simple_cycle_length_le_card [Fintype V] {i j : V} (q : Path i j) (e : j ⟶ i)
    (h : q.vertices.Nodup) : (q.cons e).length ≤ Fintype.card V := by
  simpa using h.length_le_card

/-- Summing feasible edge inequalities telescopes along any directed walk. -/
theorem feasible_path {p : V → ℤ} (h : Feasible w p) {i j : V} (q : Path i j) :
    p i ≤ q.addWeight w + p j := by
  induction q with
  | nil => simp
  | cons q e ih =>
    rw [Path.addWeight_cons]
    linarith [h e]

theorem feasible_closed {p : V → ℤ} (h : Feasible w p) : NonnegativeClosedWalks w := by
  intro i q
  linarith [feasible_path w h q]

/-- This bound is independent of walk length, as needed for the lower limiting
mean along arbitrary plays against the selected strategy. -/
theorem feasible_uniform_lower_bound [Finite V] {p : V → ℤ} (h : Feasible w p) :
    ∃ b : ℤ, ∀ {i j : V} (q : Path i j), b ≤ q.addWeight w := by
  obtain ⟨lo, hlo⟩ := Finite.bddBelow_range p
  obtain ⟨hi, hhi⟩ := Finite.bddAbove_range p
  refine ⟨lo - hi, ?_⟩
  intro i j q
  linarith [hlo (Set.mem_range_self i), hhi (Set.mem_range_self j), feasible_path w h q]

private theorem prefix_nodup {i j k : V} (a : Path i j) (b : Path j k)
    (h : (a.comp b).vertices.Nodup) : a.vertices.Nodup := by
  induction b with
  | nil => simpa using h
  | cons b e ih =>
    apply ih
    exact List.Nodup.of_append_left (by
      simpa only [Path.comp_cons, Path.vertices_cons, List.concat_eq_append] using h)

/-- Erasing a repeated vertex removes a closed walk of nonnegative weight. -/
theorem simple_path_le_of_cycles (h : NonnegativeSimpleCycles w) {i j : V} (q : Path i j) :
    ∃ a : Path i j, a.vertices.Nodup ∧ a.addWeight w ≤ q.addWeight w := by
  classical
  induction q with
  | nil => exact ⟨Path.nil, by simp, le_rfl⟩
  | @cons u v q e ih =>
    obtain ⟨a, ha, hcost⟩ := ih
    by_cases hv : v ∈ a.vertices
    · obtain ⟨b, c, rfl⟩ := a.exists_eq_comp_of_mem_vertices hv
      refine ⟨b, prefix_nodup b c ha, ?_⟩
      have hsuffix : c.vertices.Nodup := List.Nodup.of_append_right
        (by simpa only [Path.vertices_comp] using ha)
      have loop := h c e hsuffix
      rw [Path.addWeight_comp] at hcost
      rw [Path.addWeight_cons] at loop ⊢
      linarith
    · refine ⟨a.cons e, ?_, ?_⟩
      · simpa [Path.vertices_cons, List.concat_eq_append, List.nodup_append_comm, hv] using ha
      · simpa using add_le_add_right hcost (w e)

theorem closed_iff_simple_cycles : NonnegativeClosedWalks w ↔ NonnegativeSimpleCycles w := by
  constructor
  · exact fun h _ _ q e _ => h _ (q.cons e)
  · intro h i q
    obtain ⟨a, ha, hcost⟩ := simple_path_le_of_cycles w h q
    cases a with
    | nil => simpa using hcost
    | cons p e =>
      have hstart := p.start_mem_vertices
      simp [Path.vertices_cons, List.concat_eq_append, List.nodup_append_comm, hstart] at ha

theorem simple_path_le (h : NonnegativeClosedWalks w) {i j : V} (q : Path i j) :
    ∃ a : Path i j, a.vertices.Nodup ∧ a.addWeight w ≤ q.addWeight w :=
  simple_path_le_of_cycles w ((closed_iff_simple_cycles w).mp h) q

private theorem lower_bound_by_length (c : ℤ) (hc : ∀ {i j : V} (e : i ⟶ j), c ≤ w e)
    {i j : V} (q : Path i j) : (q.length : ℤ) * c ≤ q.addWeight w := by
  induction q with
  | nil => simp
  | cons q e ih =>
    simp only [Path.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, Path.addWeight_cons]
    exact add_le_add ih (hc e)

/-- With finitely many vertices, a uniform edge lower bound also bounds the
weight of the cheapest walk out of every vertex. Parallel arcs are permitted. -/
theorem potential_of_bounded_weights [Fintype V] (c : ℤ) (hc : c ≤ 0)
    (hw : ∀ {i j : V} (e : i ⟶ j), c ≤ w e) (h : NonnegativeClosedWalks w) :
    ∃ p : V → ℤ, Feasible w p := by
  classical
  let cost (i : V) (z : ℤ) := ∃ (j : V) (q : Path i j), q.addWeight w = z
  have minimum (i : V) : ∃ z, cost i z ∧ ∀ b, cost i b → z ≤ b := by
    apply Int.exists_least_of_bdd
    · refine ⟨(Fintype.card V : ℤ) * c, ?_⟩
      rintro z ⟨j, q, rfl⟩
      obtain ⟨a, ha, haz⟩ := simple_path_le w h q
      have hlength := ha.length_le_card
      rw [Path.vertices_length] at hlength
      have hcast : (a.length : ℤ) ≤ Fintype.card V := by exact_mod_cast (by omega : a.length ≤ _)
      exact (mul_le_mul_of_nonpos_right hcast hc).trans ((lower_bound_by_length w c hw a).trans haz)
    · exact ⟨0, i, Path.nil, by simp⟩
  choose p attained least using minimum
  refine ⟨p, ?_⟩
  intro i j e
  obtain ⟨k, q, hq⟩ := attained j
  exact least i _ ⟨k, e.toPath.comp q, by simp [Hom.toPath, hq]⟩

/-- A finite quiver admits an integer potential exactly when its closed walks
all have nonnegative total weight. No connectivity hypothesis is needed. -/
theorem potential_iff_closed [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] :
    (∃ p : V → ℤ, Feasible w p) ↔ NonnegativeClosedWalks w := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    exact feasible_closed w hp
  · intro h
    let allWeights (e : Σ i : V, Σ j : V, i ⟶ j) : ℤ := w e.2.2
    obtain ⟨b, hb⟩ := Finite.bddBelow_range allWeights
    refine potential_of_bounded_weights w (min b 0) (min_le_right _ _) ?_ h
    intro i j e
    exact (min_le_left _ _).trans (hb ⟨⟨i, j, e⟩, rfl⟩)

section MaxAtoms

variable {Vertex Row : Type*}

/-- A row is a separate arc, even if another row has the same endpoints. -/
@[instance_reducible] def rowQuiver (src dst : Row → Vertex) : Quiver Vertex where
  Hom i j := {r : Row // src r = i ∧ dst r = j}

def ClosedRowWalks (src dst : Row → Vertex) (weight : Row → ℤ) : Prop :=
  @NonnegativeClosedWalks Vertex (rowQuiver src dst)
    (fun {_ _} e => weight e.val)

/-- The graph certificate expressed in terms of the actual row indices. -/
theorem row_potential_iff [Fintype Vertex] [Fintype Row]
    (src dst : Row → Vertex) (weight : Row → ℤ) :
    (∃ p : Vertex → ℤ, ∀ r, p (src r) ≤ weight r + p (dst r)) ↔
      ClosedRowWalks src dst weight := by
  classical
  let edgeFinite (i j : Vertex) : Fintype ((rowQuiver src dst).Hom i j) :=
    inferInstanceAs (Fintype {r : Row // src r = i ∧ dst r = j})
  let edgeWeight : ∀ {i j : Vertex}, (rowQuiver src dst).Hom i j → ℤ := fun {_ _} e => weight e.val
  change _ ↔ @NonnegativeClosedWalks Vertex (rowQuiver src dst) edgeWeight
  rw [← @potential_iff_closed Vertex (rowQuiver src dst) edgeWeight _ edgeFinite]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro i j e
    obtain ⟨r, rfl, rfl⟩ := e
    exact hp r
  · rintro ⟨p, hp⟩
    exact ⟨p, fun r => hp (⟨r, rfl, rfl⟩ : (rowQuiver src dst).Hom (src r) (dst r))⟩

/-- A binary max-atom system is feasible exactly when Max can choose one term
per row so that all closed walks of the selected row graph are nonnegative. -/
theorem max_atoms_iff_selected_closed [Fintype Vertex] [Fintype Row]
    (src left right : Row → Vertex) (a b : Row → ℤ) :
    (∃ p : Vertex → ℤ, ∀ r, p (src r) ≤ max (a r + p (left r)) (b r + p (right r))) ↔
    ∃ choose : Row → Bool, ClosedRowWalks src
      (fun r => if choose r then left r else right r)
      (fun r => if choose r then a r else b r) := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    let choose (r : Row) := decide (b r + p (right r) ≤ a r + p (left r))
    refine ⟨choose, (row_potential_iff _ _ _).mp ⟨p, ?_⟩⟩
    intro r
    by_cases h : b r + p (right r) ≤ a r + p (left r)
    · simpa [choose, h, max_eq_left h] using hp r
    · simpa [choose, h, max_eq_right (not_le.mp h).le] using hp r
  · rintro ⟨choose, h⟩
    obtain ⟨p, hp⟩ := (row_potential_iff _ _ _).mpr h
    refine ⟨p, fun r => ?_⟩
    cases pick : choose r with
    | true =>
      have hh : p (src r) ≤ a r + p (left r) := by simpa [pick] using hp r
      exact hh.trans (le_max_left _ _)
    | false =>
      have hh : p (src r) ≤ b r + p (right r) := by simpa [pick] using hp r
      exact hh.trans (le_max_right _ _)

/-! The expanded arena has a fresh Min start, a Min vertex for each variable,
and a Max vertex for each row. After fixing the Max policy, each row vertex has
just its selected term. An isolated variable has the zero self-loop. -/

abbrev ArenaVertex (Vertex Row : Type*) := Option (Vertex ⊕ Row)

abbrev ArenaArc (src : Row → Vertex) :=
  Vertex ⊕ (Row ⊕ (Row ⊕ {v : Vertex // ∀ r, src r ≠ v}))

def arenaSrc (src : Row → Vertex) : ArenaArc src → ArenaVertex Vertex Row
  | .inl _ => none
  | .inr (.inl r) => some (.inl (src r))
  | .inr (.inr (.inl r)) => some (.inr r)
  | .inr (.inr (.inr v)) => some (.inl v.val)

def arenaDst (src dst : Row → Vertex) : ArenaArc src → ArenaVertex Vertex Row
  | .inl v => some (.inl v)
  | .inr (.inl r) => some (.inr r)
  | .inr (.inr (.inl r)) => some (.inl (dst r))
  | .inr (.inr (.inr v)) => some (.inl v.val)

def arenaWeight (src : Row → Vertex) (weight : Row → ℤ) : ArenaArc src → ℤ
  | .inr (.inr (.inl r)) => weight r
  | _ => 0

/-- Every vertex of the selected-policy graph is accessible directly, or through
a single variable vertex, from the fresh start. -/
theorem arena_start_reaches (src dst : Row → Vertex) (v : ArenaVertex Vertex Row) :
    Nonempty (@Path _ (rowQuiver (arenaSrc src) (arenaDst src dst)) none v) := by
  let graph := rowQuiver (arenaSrc src) (arenaDst src dst)
  let startArc (i : Vertex) : graph.Hom none (some (.inl i)) := ⟨.inl i, rfl, rfl⟩
  cases v with
  | none => exact ⟨@Path.nil _ graph none⟩
  | some v =>
    cases v with
    | inl i => exact ⟨@Hom.toPath _ graph _ _ (startArc i)⟩
    | inr r =>
      let second : graph.Hom (some (.inl (src r))) (some (.inr r)) := ⟨.inr (.inl r), rfl, rfl⟩
      exact ⟨(@Hom.toPath _ graph _ _ (startArc (src r))).cons second⟩

/-- Passing through the owned row vertices preserves the entire selected
potential certificate. The fresh start can use any lower bound of the prices. -/
theorem expanded_closed_iff [Fintype Vertex] [Fintype Row]
    (src dst : Row → Vertex) (weight : Row → ℤ) :
    ClosedRowWalks (arenaSrc src) (arenaDst src dst) (arenaWeight src weight) ↔
      ClosedRowWalks src dst weight := by
  classical
  rw [← row_potential_iff, ← row_potential_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨fun v => p (some (.inl v)), ?_⟩
    intro r
    have toRow := hp (.inr (.inl r))
    have fromRow := hp (.inr (.inr (.inl r)))
    simp only [arenaSrc, arenaDst, arenaWeight, zero_add] at toRow fromRow
    exact toRow.trans fromRow
  · rintro ⟨p, hp⟩
    obtain ⟨lower, hl⟩ := Finite.bddBelow_range p
    let q : ArenaVertex Vertex Row → ℤ
      | none => lower
      | some (.inl v) => p v
      | some (.inr r) => p (src r)
    refine ⟨q, ?_⟩
    rintro (v | r | r | v)
    · simpa [q, arenaSrc, arenaDst, arenaWeight] using hl (Set.mem_range_self v)
    · simp [q, arenaSrc, arenaDst, arenaWeight]
    · exact hp r
    · simp [q, arenaSrc, arenaDst, arenaWeight]

/-- Feasibility is the existence of a positional Max term selection under which
the actual expanded arena (including its fresh start) has no negative closed walk. -/
theorem max_atoms_iff_arena_certificate [Fintype Vertex] [Fintype Row]
    (src left right : Row → Vertex) (a b : Row → ℤ) :
    (∃ p : Vertex → ℤ, ∀ r, p (src r) ≤ max (a r + p (left r)) (b r + p (right r))) ↔
    ∃ choose : Row → Bool, ClosedRowWalks (arenaSrc src)
      (arenaDst src (fun r => if choose r then left r else right r))
      (arenaWeight src (fun r => if choose r then a r else b r)) := by
  simpa only [expanded_closed_iff] using max_atoms_iff_selected_closed src left right a b

end MaxAtoms

end StochasticGames.MeanPayoffGraph
