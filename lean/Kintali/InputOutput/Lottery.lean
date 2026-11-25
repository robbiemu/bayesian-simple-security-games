module

public import Kintali.InputOutput.Breakpoints

/-!
# Sparse pure defenses realizing compact coverage (Kintali §1)

Sort the fractional parts of the interior prefix sums, take a midpoint in
each positive-width interval and emit its coverage set with that width.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.InputOutput.Lottery

variable {m : ℕ}

def increment (x : Fin m → ℚ) (u : ℚ) (j : Fin m) :=
  count (Fin.partialSum x j.succ) u - count (Fin.partialSum x j.castSucc) u

def allocation (x : Fin m → ℚ) (u : ℚ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => 0 < increment x u j)

theorem indicator_eq (x : Fin m → ℚ) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (u : ℚ) (j : Fin m) :
    (if j ∈ allocation x u then (1 : ℤ) else 0) = increment x u j := by
  let s := Fin.partialSum x j.castSucc
  have a : count s u ≤ count (s + x j) u :=
    Int.ceil_mono (by linarith [(hx j).1] : s-u ≤ s+x j-u)
  have b : count (s+x j) u ≤ count s u + 1 := by
    rw [count, count, ← Int.ceil_add_one]
    apply Int.ceil_mono
    linarith [(hx j).2]
  simp only [allocation, Finset.mem_filter, Finset.mem_univ, true_and, increment, Fin.partialSum_succ]
  change (if 0 < count (s+x j) u - count s u then 1 else 0) = _
  dsimp only [s] at *
  split <;> omega

private theorem last_sum (x : Fin m → ℚ) : Fin.partialSum x (Fin.last m) = ∑ j, x j := by
  simp [Fin.partialSum, List.take_of_length_le (by simp : (List.ofFn x).length ≤ m), List.sum_ofFn]

theorem allocation_card (x : Fin m → ℚ) (r : ℕ) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (hs : (∑ j, x j) = r) {u : ℚ} (hu : 0 ≤ u) (hu' : u < 1) : (allocation x u).card = r := by
  let f := fun i => count (Fin.partialSum x i) u
  have telescope (z : Fin (m+1) → ℤ) : (∑ j : Fin m, (z j.succ - z j.castSucc)) = z (Fin.last m) - z 0 := by
    rw [Finset.sum_sub_distrib]
    have a := Fin.sum_univ_succ z
    have b := Fin.sum_univ_castSucc z
    omega
  have total : (∑ j, increment x u j) = f (Fin.last m) - f 0 := by
    exact telescope f
  have atInt (n : ℕ) : count (n : ℚ) u = n := by
    apply Int.ceil_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have top : f (Fin.last m) = r := by simp only [f, last_sum, hs, atInt]
  have bot : f 0 = 0 := by simpa [f] using atInt 0
  rw [top, bot, sub_zero] at total
  have card : ((allocation x u).card : ℤ) = ∑ j, increment x u j := by
    calc
      _ = ∑ j, (if j ∈ allocation x u then (1 : ℤ) else 0) := by simp
      _ = _ := Finset.sum_congr rfl fun j _ => indicator_eq x hx u j
  exact_mod_cast card.trans total

section PositiveTargets

variable {n : ℕ} (x : Fin (n+1) → ℚ)

/-- There are n interior endpoints for n+1 targets. -/
def cuts := (List.ofFn fun j : Fin n => Int.fract (Fin.partialSum x j.succ.castSucc)).mergeSort

theorem cuts_ordered : Ordered 0 (cuts x) := by
  constructor
  · intro t ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_mergeSort.mp ht)
    exact Int.fract_nonneg _
  · intro t ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_mergeSort.mp ht)
    exact Int.fract_lt_one _
  · exact List.pairwise_mergeSort' (· ≤ ·) _

private theorem is_cut (r : ℕ) (hs : (∑ j, x j) = r) (j : Fin ((n+1)+1)) :
    Int.fract (Fin.partialSum x j) = 0 ∨ Int.fract (Fin.partialSum x j) ∈ cuts x := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [last_sum, hs]
  · refine Fin.cases ?_ (fun t => ?_) i
    · simp
    · exact Or.inr (List.mem_mergeSort.mpr (List.mem_ofFn.mpr ⟨t, rfl⟩))

theorem recovery_marginal (r : ℕ) (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1)
    (hs : (∑ j, x j) = r) (j : Fin (n+1)) :
    mean (samples 0 (cuts x)) (fun u => if j ∈ allocation x u then 1 else 0) = x j := by
  let c := fun (p : Fin ((n+1)+1)) (u : ℚ) => (count (Fin.partialSum x p) u : ℚ)
  have expect (p) : mean (samples 0 (cuts x)) (c p) = Fin.partialSum x p :=
    mean_count _ (cuts_ordered x) _ (is_cut x r hs p)
  calc
    _ = mean (samples 0 (cuts x)) (fun u => c j.succ u - c j.castSucc u) := by
      apply mean_congr
      intro p _
      have eq := congrArg (fun z : ℤ => (z : ℚ)) (indicator_eq x hx p.1 j)
      simpa [c, increment, apply_ite] using eq
    _ = x j := by rw [mean_sub, expect, expect, Fin.partialSum_succ]; ring

end PositiveTargets

/-- Each outcome is a concrete set of distinct targets and a positive rational probability. -/
abbrev Outcome (m : ℕ) := Finset (Fin m) × ℚ

def outcomes (x : Fin m → ℚ) (s : List Sample) : List (Outcome m) :=
  (s.filter fun p => 0 < p.2).map fun p => (allocation x p.1, p.2)

def expected (out : List (Outcome m)) (f : Finset (Fin m) → ℚ) := (out.map fun p => p.2 * f p.1).sum

theorem expected_outcomes (x : Fin m → ℚ) (s : List Sample) (h : ∀ p ∈ s, 0 ≤ p.2)
    (f : Finset (Fin m) → ℚ) :
    expected (outcomes x s) f = mean s (fun u => f (allocation x u)) := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    have pos := h p (by simp)
    have tail := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases hp : 0 < p.2
    · simpa [expected, outcomes, hp] using congrArg (p.2 * f (allocation x p.1) + ·) tail
    · have hz : p.2 = 0 := le_antisymm (le_of_not_gt hp) pos
      simpa [expected, outcomes, hp, hz] using tail

def recover : {m : ℕ} → (Fin m → ℚ) → List (Outcome m)
  | 0, _ => [(∅, 1)]
  | _+1, x => outcomes x (samples 0 (cuts x))

/-- Kintali's §1 realization, including support size and legal cardinality
for every emitted pure defense. -/
theorem recover_correct (x : Fin m → ℚ) (hm : 0 < m) (r : ℕ)
    (hx : ∀ j, 0 ≤ x j ∧ x j ≤ 1) (hs : (∑ j, x j) = r) :
    (recover x).length ≤ m ∧
    (∀ p ∈ recover x, p.1.card = r ∧ 0 < p.2) ∧
    expected (recover x) (fun _ => 1) = 1 ∧
    ∀ j, expected (recover x) (fun a => if j ∈ a then 1 else 0) = x j := by
  cases m with
  | zero => omega
  | succ n =>
    let s := samples 0 (cuts x)
    have b := fun p hp => samples_bounds (by decide : (0 : ℚ) < 1) (cuts_ordered x) p hp
    have exp := expected_outcomes x s (fun p hp => (b p hp).2.2)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [recover, outcomes, s, cuts] using (List.length_filter_le (fun p : Sample => decide (0 < p.2)) s)
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hq, pos⟩ := List.mem_filter.mp hq
      exact ⟨allocation_card x r hx hs (b q hq).1 (b q hq).2.1, of_decide_eq_true pos⟩
    · rw [recover, exp]
      simp [s, mean_const]
    · intro j
      rw [recover, exp]
      exact recovery_marginal x r hx hs j

end Kintali.InputOutput.Lottery
