module

public import Kintali.QuoteSearch.WeightUpdate
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The bounded quote search

Select quantiles, run one restricted trial, and double the blocking
intervals on failure. The trial provides the contact and recovery
steps. This module checks the executable outer loop, with explicit
requirements on those steps.
-/

@[expose] public section

namespace Kintali.QuoteSearch

structure Interval where
  lo : ℕ
  hi : ℕ

def Interval.Contains (i : Interval) (j : ℕ) : Prop :=
  i.lo ≤ j ∧ j < i.hi

instance (i : Interval) (j : ℕ) : Decidable (i.Contains j) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev WeightTable (pairs : ℕ) := Vector (List WeightRun) pairs
abbrev Selection (pairs : ℕ) := Vector (List ℕ) pairs
abbrev BidIndex (pairs : ℕ) := Fin pairs × ℕ

inductive Reply (pairs : ℕ) (Answer : Type*)
  | cleared (answer : Answer)
  | blocked (intervals : Vector Interval pairs)

abbrev Trial (pairs : ℕ) (Answer : Type*) := Selection pairs → Reply pairs Answer

variable {pairs : ℕ} {Answer : Type*}

def initialTable (quotes : Vector ℕ pairs) : WeightTable pairs :=
  Vector.ofFn (fun p => Runs.initial quotes[p])

def select (J : ℕ) (state : WeightTable pairs) : Selection pairs :=
  Vector.ofFn (fun p => Runs.selected state[p] J)

def double (state : WeightTable pairs) (intervals : Vector Interval pairs) : WeightTable pairs :=
  Vector.ofFn (fun p => Runs.doubleInterval intervals[p].lo intervals[p].hi state[p])

def turn (J : ℕ) (trial : Trial pairs Answer) (state : WeightTable pairs) : WeightTable pairs :=
  match trial (select J state) with
  | .cleared _ => state
  | .blocked intervals => double state intervals

/-- The transcript states used in the proof. The executable loop below
stops as soon as a trial clears. -/
def stateAt (J : ℕ) (trial : Trial pairs Answer) (init : WeightTable pairs) :
    ℕ → WeightTable pairs
  | 0 => init
  | t + 1 => turn J trial (stateAt J trial init t)

def run (J : ℕ) (trial : Trial pairs Answer) : ℕ → WeightTable pairs → Option Answer
  | 0, _ => none
  | t + 1, state =>
    match trial (select J state) with
    | .cleared answer => some answer
    | .blocked intervals => run J trial t (double state intervals)

def solve (h G : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs) : Option Answer :=
  run (4 * h) trial (2 * h * (G.log2 + 1)) (initialTable quotes)

structure ValidSelection (J : ℕ) (quotes : Vector ℕ pairs) (s : Selection pairs) : Prop where
  count : ∀ p : Fin pairs, s[p].length ≤ J - 1
  index : ∀ (p : Fin pairs) j, j ∈ s[p] → j < quotes[p]

/-- A failed trial reports intervals missing all selected quotes. The
same witness set hits one of those intervals in every failed trial. -/
structure TrialSpec (J : ℕ) (quotes : Vector ℕ pairs) (trial : Trial pairs Answer)
    (witness : Finset (BidIndex pairs)) (correct : Answer → Prop) : Prop where
  eligible : ∀ b ∈ witness, b.2 < quotes[b.1]
  cleared : ∀ s a, ValidSelection J quotes s → trial s = .cleared a → correct a
  blocked : ∀ s ranges, ValidSelection J quotes s → trial s = .blocked ranges →
    (∀ p : Fin pairs, ranges[p].lo ≤ ranges[p].hi ∧ ranges[p].hi ≤ quotes[p] ∧
      ∀ j ∈ s[p], ¬ranges[p].Contains j) ∧
    ∃ b ∈ witness, ranges[b.1].Contains b.2

private theorem initial_count (quotes : Vector ℕ pairs) (p : Fin pairs) :
    Runs.quoteCount (initialTable quotes)[p] = quotes[p] := by
  rw [← Runs.expand_length]
  simp [initialTable]

private theorem double_count (state : WeightTable pairs) (intervals : Vector Interval pairs)
    (p : Fin pairs) : Runs.quoteCount (double state intervals)[p] = Runs.quoteCount state[p] := by
  simp [double, Runs.doubleInterval_quoteCount]

theorem stateAt_count (J : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (t : ℕ) (p : Fin pairs) :
    Runs.quoteCount (stateAt J trial (initialTable quotes) t)[p] = quotes[p] := by
  induction t with
  | zero => exact initial_count quotes p
  | succ t ih =>
    cases hr : trial (select J (stateAt J trial (initialTable quotes) t)) with
    | cleared a => simpa [stateAt, turn, hr] using ih
    | blocked ranges =>
      simp only [stateAt, turn, hr]
      exact (double_count _ ranges p).trans ih

theorem select_valid (J : ℕ) (quotes : Vector ℕ pairs) (state : WeightTable pairs)
    (hState : ∀ p : Fin pairs, Runs.quoteCount state[p] = quotes[p]) :
    ValidSelection J quotes (select J state) := by
  constructor
  · intro p
    simpa [select] using Runs.selected_count state[p] J
  · intro p j hj
    have hm : j ∈ Runs.selected state[p] J := by simpa [select] using hj
    unfold Runs.selected at hm
    split at hm
    · simp at hm
    next hNonempty =>
      obtain ⟨s, hs, hj⟩ := List.mem_map.mp hm
      have hsRange := List.mem_range.mp hs
      rw [← hj, ← hState p]
      exact (Runs.quantile_spec state[p] (by omega : 0 < s + 1)
        (by omega : s + 1 < J) (Nat.pos_of_ne_zero hNonempty)).1

private theorem run_correct {J : ℕ} {quotes : Vector ℕ pairs} {trial : Trial pairs Answer}
    {witness : Finset (BidIndex pairs)} {correct : Answer → Prop}
    (hTrial : TrialSpec J quotes trial witness correct)
    {fuel : ℕ} {state : WeightTable pairs} {a : Answer}
    (hState : ∀ p : Fin pairs, Runs.quoteCount state[p] = quotes[p])
    (hRun : run J trial fuel state = some a) : correct a := by
  induction fuel generalizing state with
  | zero => simp [run] at hRun
  | succ fuel ih =>
    cases hr : trial (select J state) with
    | cleared b =>
      have he : b = a := Option.some.inj (by simpa [run, hr] using hRun)
      exact he ▸ hTrial.cleared _ b (select_valid J quotes state hState) hr
    | blocked ranges =>
      exact ih (fun p => (double_count state ranges p).trans (hState p))
        (by simpa [run, hr] using hRun)

private theorem run_none_implies_blocked
    {J T : ℕ} {trial : Trial pairs Answer} {init : WeightTable pairs}
    (hNone : run J trial T init = none) :
    ∀ t < T, ∃ ranges, trial (select J (stateAt J trial init t)) = .blocked ranges := by
  have hSuffix (t : ℕ) (ht : t ≤ T) :
      run J trial (T - t) (stateAt J trial init t) = none := by
    induction t with
    | zero => simpa [stateAt] using hNone
    | succ t ih =>
      have hs := ih (by omega)
      rw [show T - t = T - (t + 1) + 1 from by omega] at hs
      cases hra : trial (select J (stateAt J trial init t)) with
      | cleared a => simp [run, hra] at hs
      | blocked ranges => simpa [run, stateAt, turn, hra] using hs
  intro t ht
  have hs := hSuffix t ht.le
  rw [show T - t = (T - t - 1) + 1 from by omega] at hs
  cases hr : trial (select J (stateAt J trial init t)) with
  | cleared a => simp [run, hr] at hs
  | blocked ranges => exact ⟨ranges, rfl⟩

/-- The executable loop returns a verified answer within the trial
bound. No iteration enumerates the full set of quotes. -/
theorem solve_correct {h G : ℕ} {trial : Trial pairs Answer}
    {quotes : Vector ℕ pairs} {witness : Finset (BidIndex pairs)} {correct : Answer → Prop}
    (hh : 0 < h) (hSize : witness.card ≤ h) (hGrid : ∀ p : Fin pairs, quotes[p] ≤ G)
    (hTrial : TrialSpec (4 * h) quotes trial witness correct) :
    ∃ answer, solve h G trial quotes = some answer ∧ correct answer := by
  cases hs : solve h G trial quotes with
  | some a =>
    exact ⟨a, rfl, run_correct hTrial (initial_count quotes) hs⟩
  | none =>
    let J := 4 * h
    let T := 2 * h * (G.log2 + 1)
    let states := stateAt J trial (initialTable quotes)
    have hCount (t : ℕ) (p : Fin pairs) : Runs.quoteCount (states t)[p] = quotes[p] :=
      stateAt_count J trial quotes t p
    let rangeAt (t : ℕ) (p : Fin pairs) : Interval :=
      match trial (select J (states t)) with
      | .cleared _ => ⟨0, 0⟩
      | .blocked ranges => ranges[p]
    let marked (t : ℕ) := witness.filter (fun b => (rangeAt t b.1).Contains b.2)
    let total (p : Fin pairs) (t : ℕ) : ℚ := Runs.weight (states t)[p]
    have hFailed := run_none_implies_blocked (J := J) (T := T) hs
    have hStep (t : ℕ) (ht : t < T) :
        (∀ p : Fin pairs, (rangeAt t p).lo ≤ (rangeAt t p).hi ∧
          (rangeAt t p).hi ≤ quotes[p] ∧
          ∀ j ∈ (select J (states t))[p], ¬(rangeAt t p).Contains j) ∧
        (∃ b ∈ witness, b ∈ marked t) ∧
        ∀ p : Fin pairs, (states (t + 1))[p] =
          Runs.doubleInterval (rangeAt t p).lo (rangeAt t p).hi (states t)[p] := by
      obtain ⟨ranges, hr⟩ := hFailed t ht
      change trial (select J (states t)) = .blocked ranges at hr
      obtain ⟨hRanges, b, hb, hi⟩ :=
        hTrial.blocked _ ranges (select_valid J quotes (states t) (hCount t)) hr
      refine ⟨?_, ⟨b, hb, Finset.mem_filter.mpr ⟨hb, ?_⟩⟩, ?_⟩
      · simpa [rangeAt, hr] using hRanges
      · simpa [rangeAt, hr] using hi
      · intro p
        have hn : states (t + 1) = double (states t) ranges := by
          change turn J trial (states t) = _
          simp [turn, hr]
        simp [hn, double, rangeAt, hr]
    have hExponent (b : BidIndex pairs) (hb : b ∈ witness) (t : ℕ) (ht : t ≤ T) :
        Runs.exponentAt (states t)[b.1] b.2 = hits marked b t := by
      induction t with
      | zero => simp [states, stateAt, initialTable, hits]
      | succ t ih =>
        obtain ⟨hRanges, _, hState⟩ := hStep t (by omega)
        rw [hState, Runs.exponentAt_doubleInterval _ (by rw [hCount]; exact (hRanges b.1).2.1)
          (by rw [hCount]; exact hTrial.eligible b hb), ih (by omega), hits]
        have hMem : b ∈ marked t ↔ (rangeAt t b.1).Contains b.2 := by
          change b ∈ witness.filter _ ↔ _
          rw [Finset.mem_filter]
          simp [hb]
        simp only [hMem, Interval.Contains]
    have hInitial (p : Fin pairs) : total p 0 ≤ G := by
      have hu : Runs.weight (initialTable quotes)[p] = quotes[p] := by
        rw [Runs.weight_eq_expand]
        simp [initialTable]
      dsimp only [total, states, stateAt]
      exact_mod_cast hu.le.trans (hGrid p)
    have hWeight (b : BidIndex pairs) (hb : b ∈ witness) (t : ℕ) (ht : t ≤ T) :
        weight marked b t ≤ total b.1 t := by
      have hq : b.2 < Runs.quoteCount (states t)[b.1] := (hCount t b.1).symm ▸ hTrial.eligible b hb
      rw [weight, ← hExponent b hb t ht]
      dsimp only [total]
      exact_mod_cast Runs.exponentWeight_le (states t)[b.1] hq
    have hGrow (t : ℕ) (ht : t < T) (p : Fin pairs) :
        total p (t + 1) ≤ total p t * (1 + 1 / (4 * (h : ℚ))) := by
      obtain ⟨hRanges, _, hState⟩ := hStep t ht
      let rs := (states t)[p]
      let i := rangeAt t p
      let d := Runs.prefixWeight rs i.hi - Runs.prefixWeight rs i.lo
      have hMiss : ∀ j ∈ Runs.selected rs J, ¬i.Contains j := by
        dsimp only [rs, i]
        simpa [select] using (hRanges p).2.2
      have hc : J * d ≤ Runs.weight rs :=
        Runs.selected_interval_bound rs J i.lo i.hi (hRanges p).1 hMiss
      have hc' : (d : ℚ) * (4 * (h : ℚ)) ≤ Runs.weight rs := by
        rw [mul_comm]
        dsimp only [J] at hc
        exact_mod_cast hc
      have hFrac : (d : ℚ) ≤ (Runs.weight rs : ℚ) / (4 * (h : ℚ)) :=
        (le_div_iff₀ (by positivity)).mpr hc'
      change ((Runs.weight (states (t + 1))[p] : ℕ) : ℚ) ≤ _
      rw [hState, Runs.weight_doubleInterval _ (hRanges p).1, Nat.cast_add]
      calc
        _ ≤ (Runs.weight rs : ℚ) + (Runs.weight rs : ℚ) / (4 * (h : ℚ)) :=
          add_le_add_right hFrac _
        _ = _ := by dsimp [total, rs]; ring
    exact (Nat.lt_irrefl T (failure_bound_of_growth marked witness Prod.fst total
      hh hSize hInitial hWeight (fun t ht => (hStep t ht).2.1) hGrow)).elim

end Kintali.QuoteSearch
