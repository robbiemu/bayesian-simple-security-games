module

public import Kintali.QuotaSweep.Cycle
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Counted walks in the single-successor proposal graph

`visits` traverses a prefix once. Its first result counts occurrences of a
destination in the prefix, and its second result counts successor queries.
The acyclic flow, the positive return test and the selected-cycle test all
have evaluations with these same values as the sweep's definitions.
-/

open scoped BigOperators
open Function

@[expose] public section
namespace Kintali.QuotaSweep.Routing

variable {V : Type*} [DecidableEq V]

def visits (next : V → Option V) (dest : V) : ℕ → Option V → ℕ × ℕ
  | 0, _ => (0,0)
  | _+1, none => (0,0)
  | n+1, some v =>
    let rest := visits next dest n (next v)
    ((if v = dest then 1 else 0) + rest.1, rest.2+1)

omit [DecidableEq V] in
private theorem none_iterate (next : V → Option V) (n : ℕ) : (advance next)^[n] none = none :=
  Function.iterate_fixed (show advance next none = none from rfl) n

theorem visits_value (next : V → Option V) (dest : V) (n : ℕ) (u : Option V) :
    (visits next dest n u).1 =
      ∑ k ∈ Finset.range n, if (advance next)^[k] u = some dest then 1 else 0 := by
  induction n generalizing u with
  | zero => simp [visits]
  | succ n ih =>
    cases u with
    | none => simp [visits, none_iterate]
    | some v =>
      rw [Finset.sum_range_succ']
      simp only [visits, ih, iterate_succ_apply, iterate_zero_apply, Option.some.injEq]
      exact Nat.add_comm ..

theorem visits_work (next : V → Option V) (dest : V) (n : ℕ) (u : Option V) :
    (visits next dest n u).2 ≤ n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    cases u <;> simp [visits, ih]

theorem visits_pos (next : V → Option V) (dest : V) (n : ℕ) (u : Option V) :
    0 < (visits next dest n u).1 ↔ ∃ k : Fin n, (advance next)^[k.val] u = some dest := by
  rw [visits_value, Finset.sum_pos_iff]
  simp only [Finset.mem_range, Fin.exists_iff]
  apply exists_congr
  intro k
  by_cases he : (advance next)^[k] u = some dest <;> simp [he]

variable [Fintype V]

def cycleProbe (next : V → Option V) (u : V) : Bool × ℕ :=
  let h := visits next u (Fintype.card (Option V)) (next u)
  (decide (0 < h.1), h.2+1)

def orbitProbe (next : V → Option V) (u v : V) : Bool × ℕ :=
  let h := visits next v (Fintype.card (Option V)) (some u)
  (decide (0 < h.1), h.2)

theorem cycleProbe_value (next : V → Option V) (u : V) :
    (cycleProbe next u).1 = cyclic next u := by
  simp only [cycleProbe, cyclic]
  congr! 1
  rw [visits_pos]
  simp [iterate_succ_apply, advance]

theorem orbitProbe_value (next : V → Option V) (u v : V) :
    (orbitProbe next u v).1 = onCycle next u v := by
  unfold orbitProbe onCycle
  rw [decide_eq_decide]
  exact visits_pos next v _ (some u)

/-- Evaluate one destination's path rate by walking each injected vertex
once. The second coordinate counts actual successor queries. -/
def measuredPath (next : V → Option V) (inject : V → ℚ) (v : V) : ℚ × ℕ :=
  ∑ u, let h := visits next v (Fintype.card (Option V)) (some u)
       ((h.1 : ℚ) * inject u, h.2)

omit [Fintype V] in
private theorem weighted_visits (next : V → Option V) (a : ℚ) (v u : V) (n : ℕ) :
    ((visits next v n (some u)).1 : ℚ)*a =
      ∑ k ∈ Finset.range n, if (advance next)^[k] (some u) = some v then a else 0 := by
  rw [visits_value, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp

theorem measuredPath_value (next : V → Option V) (inject : V → ℚ) (v : V) :
    (measuredPath next inject v).1 = pathRate next inject v := by
  unfold measuredPath pathRate arrival
  rw [Prod.fst_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact weighted_visits next (inject u) v u _

theorem measuredPath_work (next : V → Option V) (inject : V → ℚ) (v : V) :
    (measuredPath next inject v).2 ≤ Fintype.card V * Fintype.card (Option V) := by
  rw [measuredPath, Prod.snd_sum]
  exact (Finset.sum_le_sum (fun u _ => visits_work next v (Fintype.card (Option V)) (some u))).trans
    (by simp)

theorem cycleProbe_work (next : V → Option V) (u : V) :
    (cycleProbe next u).2 ≤ Fintype.card (Option V) + 1 :=
  Nat.succ_le_succ (visits_work ..)

theorem orbitProbe_work (next : V → Option V) (u v : V) :
    (orbitProbe next u v).2 ≤ Fintype.card (Option V) := visits_work ..

end Kintali.QuotaSweep.Routing
