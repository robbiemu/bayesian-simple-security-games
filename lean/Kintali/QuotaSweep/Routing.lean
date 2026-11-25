module

public import Kintali.QuotaSweep.Choices
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

/-!
# Flow in the proposal graph

The terminal has no outgoing arc. Each injection follows its unique path.
A bounded return test detects periodic vertices. The separate cycle module
constructs a unit circulation on the single selected cycle.
-/

open scoped BigOperators
open Function

@[expose] public section
namespace Kintali.QuotaSweep.Routing

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Extend the routing function by an absorbing terminal. -/
def advance (next : V → Option V) (u : Option V) : Option V := u.bind next

/-- A bounded decidable test for a positive return time. -/
def cyclic (next : V → Option V) (u : V) : Bool :=
  decide (∃ n : Fin (Fintype.card (Option V)),
    (advance next)^[n.val + 1] (some u) = some u)

theorem cyclic_iff {next : V → Option V} {u : V} :
    cyclic next u = true ↔ some u ∈ periodicPts (advance next) := by
  simp only [cyclic, decide_eq_true_eq]
  constructor
  · rintro ⟨n, h⟩
    exact mk_mem_periodicPts (Nat.succ_pos _) h
  · intro h
    let p := minimalPeriod (advance next) (some u)
    have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts h
    have hb : p ≤ Fintype.card (Option V) := minimalPeriod_le_card
    refine ⟨⟨p - 1, by omega⟩, ?_⟩
    change (advance next)^[p - 1 + 1] (some u) = some u
    rw [Nat.sub_add_cancel hp]
    exact isPeriodicPt_minimalPeriod _ _

/-- After at most the number of vertices, any orbit is periodic, including
an orbit absorbed at the terminal. -/
theorem periodic_after_card {W : Type*} [Fintype W] (f : W → W) (a : W) :
    f^[Fintype.card W] a ∈ periodicPts f := by
  let N := Fintype.card W
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (N + 1) => f^[k.val] a) (by simp [N])
  have pair {i j : Fin (N + 1)} (hlt : i < j) (hij : f^[i.val] a = f^[j.val] a) :
      f^[N] a ∈ periodicPts f := by
    have hp : IsPeriodicPt f (j.val - i.val) (f^[i.val] a) := by
      change f^[j.val - i.val] (f^[i.val] a) = f^[i.val] a
      rw [← iterate_add_apply, Nat.sub_add_cancel hlt.le, ← hij]
    have hi : i.val ≤ N := by omega
    rw [← Nat.sub_add_cancel hi, iterate_add_apply]
    exact mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) (hp.apply_iterate _)
  rcases lt_or_gt_of_ne hne with h | h
  · exact pair h heq
  · exact pair h heq.symm

def incoming (next : V → Option V) (q : V → ℚ) (v : V) : ℚ :=
  ∑ u, if next u = some v then q u else 0

/-- The rate arriving after exactly `k` arcs. This formula visits each
initial vertex once for the requested destination. -/
def arrival (next : V → Option V) (inject : V → ℚ) (k : ℕ) (v : V) : ℚ :=
  ∑ u, if (advance next)^[k] (some u) = some v then inject u else 0

@[simp] theorem arrival_zero (next : V → Option V) (inject : V → ℚ) (v : V) :
    arrival next inject 0 v = inject v := by simp [arrival]

theorem incoming_arrival (next : V → Option V) (inject : V → ℚ) (k : ℕ) (v : V) :
    incoming next (arrival next inject k) v = arrival next inject (k + 1) v := by
  unfold incoming arrival
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [iterate_succ_apply']
  cases h : (advance next)^[k] (some a) with
  | none => simp [advance]
  | some b =>
    rw [Finset.sum_eq_single b]
    · by_cases hn : next b = some v <;> simp [advance, hn]
    · intro z _ hzb
      simp [Ne.symm hzb]
    · simp

/-- Total outgoing rates along the paths from each injection, evaluated
for at most the number of vertices including the terminal. -/
def pathRate (next : V → Option V) (inject : V → ℚ) (v : V) : ℚ :=
  ∑ k ∈ Finset.range (Fintype.card (Option V)), arrival next inject k v

theorem path_nonneg {next : V → Option V} {inject : V → ℚ} (h : ∀ u, 0 ≤ inject u) (v : V) :
    0 ≤ pathRate next inject v := by
  apply Finset.sum_nonneg
  intro k _
  exact Finset.sum_nonneg fun u _ => by split <;> simp_all

theorem path_conservation {next : V → Option V} (h : ∀ v, cyclic next v ≠ true)
    (inject : V → ℚ) (v : V) :
    pathRate next inject v = inject v + incoming next (pathRate next inject) v := by
  let N := Fintype.card (Option V)
  have hfinal (a : V) : (advance next)^[N] (some a) ≠ some v := by
    intro heq
    exact h v (cyclic_iff.mpr (heq ▸ periodic_after_card (advance next) (some a)))
  have hz : arrival next inject N v = 0 := by simp [arrival, hfinal]
  have hin : incoming next (pathRate next inject) v =
      ∑ k ∈ Finset.range N, arrival next inject (k + 1) v := by
    unfold incoming pathRate
    simp_rw [Finset.ite_sum_zero]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => incoming_arrival next inject k v
  rw [hin, add_comm, ← arrival_zero next inject v]
  change (∑ k ∈ Finset.range N, arrival next inject k v) = _
  rw [← Finset.sum_range_succ' (fun k => arrival next inject k v), Finset.sum_range_succ, hz,
    add_zero]

end Kintali.QuotaSweep.Routing
