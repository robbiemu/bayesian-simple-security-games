module

public import Kintali.Equilibrium
public import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

/-!
# The direct cases in §1

Cover all targets with positive defender gain when the budget permits.
At the two endpoints the defender's allocation is fixed. Each attacker
type then chooses a best response by a scan in target order.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali

structure Strategy (k m : ℕ) where
  coverage : Fin m → ℚ
  attacks : Fin k → Fin m → ℚ

namespace Game

variable {k m : ℕ} (g : Game (Fin k) (Fin m))

def positiveTargets : List (Fin m) :=
  (List.finRange m).filter (fun j => decide (0 < g.gain j))

def defenseOrder : List (Fin m) :=
  g.positiveTargets ++ (List.finRange m).filter (fun j => !(decide (0 < g.gain j)))

private theorem defenseOrder_perm : g.defenseOrder.Perm (List.finRange m) := by
  exact List.filter_append_perm (fun j => decide (0 < g.gain j)) (List.finRange m)

def earlyDefense : Finset (Fin m) :=
  (g.defenseOrder.take g.resources).toFinset

theorem earlyDefense_card (hBudget : g.resources ≤ m) :
    g.earlyDefense.card = g.resources := by
  have hn : g.defenseOrder.Nodup := g.defenseOrder_perm.nodup_iff.mpr (List.nodup_finRange m)
  have hOrder : g.defenseOrder.length = m := by simpa using g.defenseOrder_perm.length_eq
  rw [earlyDefense, List.toFinset_card_of_nodup (hn.sublist (List.take_sublist _ _)),
    List.length_take, hOrder, Nat.min_eq_left hBudget]

theorem positive_mem_earlyDefense (hEnough : g.positiveTargets.length ≤ g.resources)
    {j : Fin m} (hGain : 0 < g.gain j) : j ∈ g.earlyDefense := by
  rw [earlyDefense, List.mem_toFinset, defenseOrder, List.take_append, List.take_of_length_le hEnough]
  exact List.mem_append_left _ (by simp [positiveTargets, hGain])

/-- The least-index minimizing target. `List.minOn` retains the first
minimizer in the supplied target order. -/
def bestTarget (hm : 0 < m) (x : Fin m → ℚ) (i : Fin k) : Fin m :=
  (List.finRange m).minOn (fun j => g.cost i j (x j))
    (List.ne_nil_of_mem (List.mem_finRange ⟨0, hm⟩))

theorem bestTarget_spec (hm : 0 < m) (x : Fin m → ℚ) (i : Fin k) (j : Fin m) :
    g.cost i (g.bestTarget hm x i) (x (g.bestTarget hm x i)) ≤ g.cost i j (x j) :=
  List.apply_minOn_le_of_mem (f := fun a => g.cost i a (x a)) (List.mem_finRange j)

def earlyStrategy (hm : 0 < m) : Strategy k m :=
  let x : Fin m → ℚ := fun j => if j ∈ g.earlyDefense then 1 else 0
  ⟨x, fun i j => if j = g.bestTarget hm x i then 1 else 0⟩

/-- The zero budget, full budget, and enough-to-cover-positive-gains
cases of the main algorithm. -/
theorem earlyStrategy_correct (hm : 0 < m) (hBudget : g.resources ≤ m)
    (hPrior : ∀ i, 0 ≤ g.prior i) (hGain : ∀ j, 0 ≤ g.gain j)
    (hEarly : g.resources = 0 ∨ g.resources = m ∨ g.positiveTargets.length ≤ g.resources) :
    g.IsBayesNash (g.earlyStrategy hm).coverage (g.earlyStrategy hm).attacks := by
  let x := (g.earlyStrategy hm).coverage
  let q := (g.earlyStrategy hm).attacks
  change g.IsBayesNash x q
  have hx (j : Fin m) : x j = if j ∈ g.earlyDefense then 1 else 0 := rfl
  have hq (i : Fin k) (j : Fin m) : q i j = if j = g.bestTarget hm x i then 1 else 0 := rfl
  have hqNonneg (i : Fin k) (j : Fin m) : 0 ≤ q i j := by
    rw [hq]
    split <;> simp
  constructor
  · simp only [hx, ← Finset.sum_filter, Finset.sum_const, nsmul_one]
    simp [earlyDefense_card g hBudget]
  · intro j
    rw [hx]
    split <;> simp
  · intro i
    refine ⟨?_, hqNonneg i⟩
    simp only [hq, ← Finset.sum_filter]
    rw [show Finset.univ.filter (fun j => j = g.bestTarget hm x i) =
      {g.bestTarget hm x i} from by ext j; simp, Finset.sum_singleton]
  · intro i j s hp
    have hj : j = g.bestTarget hm x i := by
      by_contra! hne
      simp [hq, hne] at hp
    exact hj.symm ▸ g.bestTarget_spec hm x i s
  · intro j s hj hs
    have hjIn : j ∈ g.earlyDefense := by
      by_contra h
      simp [hx, h] at hj
    have hsOut : s ∉ g.earlyDefense := by
      intro h
      simp [hx, h] at hs
    have hZero : g.gain s = 0 := by
      rcases hEarly with h0 | hFull | hEnough
      · simp [earlyDefense, h0] at hjIn
      · have hmOrder : g.defenseOrder.length ≤ g.resources := by
          rw [g.defenseOrder_perm.length_eq, List.length_finRange, hFull]
        have hsIn : s ∈ g.earlyDefense := by
          rw [earlyDefense, List.mem_toFinset, List.take_of_length_le hmOrder,
            g.defenseOrder_perm.mem_iff]
          exact List.mem_finRange _
        exact (hsOut hsIn).elim
      · exact le_antisymm (le_of_not_gt (fun hp => hsOut (g.positive_mem_earlyDefense hEnough hp)))
          (hGain s)
    rw [pressure, hZero, mul_zero]
    exact mul_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hPrior i) (hqNonneg i j))) (hGain j)

end Game
end Kintali
