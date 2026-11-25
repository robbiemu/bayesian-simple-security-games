module

public import Kintali.QuoteSearch.SelectionWork
public import Kintali.QuoteSearch.UpdateWork
public import Kintali.LinearProgramming.ArithmeticRun

/-! # Cost composition across adaptive quote-search rounds

The outer run has a polynomial budget for its own operations. Each
restricted trial supplies its own cost, including the query at the
particular selection reached by this run.
-/

@[expose] public section

namespace Kintali.QuoteSearch.DriverWork

open StochasticGames.CompilerRun StochasticGames.BinarySize
open Kintali.LinearProgramming.ArithmeticRun

variable {pairs : ℕ} {Answer : Type}

abbrev ChargedTrial (pairs : ℕ) (Answer : Type) := Selection pairs → Run (Reply pairs Answer)

def selectTable (J : ℕ) (state : WeightTable pairs) : Run (Selection pairs) :=
  tabulate pairs fun p => do
    let row ← step pairs.size state[p.val]
    Runs.selectedWork row J

@[simp] theorem selectTable_value (J : ℕ) (state : WeightTable pairs) :
    (selectTable J state).value = select J state := by
  simp [selectTable, select]

def updateTable (state : WeightTable pairs) (ranges : Vector Interval pairs) :
    Run (WeightTable pairs) :=
  tabulate pairs fun p => do
    let row ← step pairs.size state[p.val]
    let r ← step pairs.size ranges[p.val]
    Runs.updateWork r.lo r.hi row

@[simp] theorem updateTable_value (state : WeightTable pairs) (ranges : Vector Interval pairs) :
    (updateTable state ranges).value = double state ranges := by
  simp [updateTable, double]

def search (J : ℕ) (trial : ChargedTrial pairs Answer) :
    ℕ → WeightTable pairs → Run (Option Answer)
  | 0, _ => step 0 none
  | fuel+1, state => do
    let s ← selectTable J state
    let reply ← trial s
    let result ← step 0 reply
    match result with
    | .cleared answer => step 0 (some answer)
    | .blocked ranges =>
      let next ← updateTable state ranges
      search J trial fuel next

@[simp] theorem search_value (J : ℕ) (trial : ChargedTrial pairs Answer)
    (fuel : ℕ) (state : WeightTable pairs) :
    (search J trial fuel state).value = run J (fun s => (trial s).value) fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases hr : (trial (select J state)).value <;> simp [search, run, hr, ih]

def widthLimit (pairs J G T : ℕ) :=
  pairs.size + J.size + G.size + T + 4

def selectLimit (pairs J T : ℕ) :=
  3*(pairs+1) + pairs*(1 + Runs.selectionSlots (1+2*T) J T)

def updateLimit (pairs T : ℕ) := 3*(pairs+1) + pairs*(2 + 32*(2+2*T))

theorem selectTable_bound (J G T : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (t : ℕ) (ht : t ≤ T) (hQ : ∀ p : Fin pairs, quotes[p] ≤ G) :
    (selectTable J (stateAt J trial (initialTable quotes) t)).Bound
      (selectLimit pairs J T) (widthLimit pairs J G T) := by
  let state := stateAt J trial (initialTable quotes) t
  let W := widthLimit pairs J G T
  have wIndex : pairs.size ≤ W := by unfold W widthLimit; omega
  apply tabulate_bound _ wIndex
  intro p
  let row := state[p]
  have exps (r : WeightRun) (hr : r ∈ row) : r.doublings ≤ T :=
    (runExponent_bound J trial quotes p t r hr).trans ht
  have hq : (Runs.quoteCount row + 1).size ≤ W := by
    change (Runs.quoteCount (stateAt J trial (initialTable quotes) t)[p] + 1).size ≤ W
    rw [stateAt_count]
    have h := size_succ_le quotes[p]
    have hG := Nat.size_le_size (hQ p)
    unfold W widthLimit
    omega
  have weight := weightWidth_bound J trial quotes p t
  have bits := Nat.size_le_size (hQ p)
  have hWeight : (Runs.weight row).size + J.size + 1 ≤ W := by
    change (Runs.weight row).size ≤ quotes[p].size + t at weight
    unfold W widthLimit
    omega
  have hWide : T+2 ≤ W := by unfold W widthLimit; omega
  have runs := runCount_bound J trial quotes p t
  have lim : Runs.selectionSlots row.length J T ≤ Runs.selectionSlots (1+2*T) J T := by
    unfold Runs.selectionSlots
    have h : row.length ≤ 1+2*T := runs.trans (by omega)
    gcongr
  have b := (Runs.selectedWork_bound row J exps hq hWeight hWide).weaken lim le_rfl
  exact bound_bind (f := fun row => Runs.selectedWork row J)
    ((bound_step _ _).weaken le_rfl wIndex) b

theorem updateTable_bound (J G T : ℕ) (trial : Trial pairs Answer) (quotes : Vector ℕ pairs)
    (t : ℕ) (ht : t ≤ T) (hQ : ∀ p : Fin pairs, quotes[p] ≤ G)
    (ranges : Vector Interval pairs) (bounds : ∀ p : Fin pairs, ranges[p].lo ≤ ranges[p].hi ∧
      ranges[p].hi ≤ G) :
    (updateTable (stateAt J trial (initialTable quotes) t) ranges).Bound
      (updateLimit pairs T) (widthLimit pairs J G T) := by
  let state := stateAt J trial (initialTable quotes) t
  let W := widthLimit pairs J G T
  have wIndex : pairs.size ≤ W := by unfold W widthLimit; omega
  have wGrid : G.size ≤ W := by unfold W widthLimit; omega
  apply tabulate_bound _ wIndex
  intro p
  let row := state[p]
  let r := ranges[p]
  have exps (q : WeightRun) (hq : q ∈ row) : q.doublings ≤ T :=
    (runExponent_bound J trial quotes p t q hq).trans ht
  have count : (Runs.quoteCount row).size ≤ W := by
    change (Runs.quoteCount (stateAt J trial (initialTable quotes) t)[p]).size ≤ W
    rw [stateAt_count]
    exact (Nat.size_le_size (hQ p)).trans wGrid
  have hi := (Nat.size_le_size (bounds p).2).trans wGrid
  have lo := (Nat.size_le_size ((bounds p).1.trans (bounds p).2)).trans wGrid
  have nw : T+1 ≤ W := by unfold W widthLimit; omega
  have rowLength : row.length ≤ 1+2*T :=
    (runCount_bound J trial quotes p t).trans (by omega)
  have upd := (Runs.updateWork_bound r.lo r.hi row lo hi count exps nw).weaken
    (Nat.mul_le_mul_left _ (by omega : row.length+1 ≤ 2+2*T)) le_rfl
  constructor
  · change 1 + (1 + (Runs.updateWork r.lo r.hi row).work.slots) ≤ _
    have := upd.1
    omega
  · exact max_le wIndex (max_le wIndex upd.2)

theorem search_bound (J G T : ℕ) (trial : ChargedTrial pairs Answer) (quotes : Vector ℕ pairs)
    (hGrid : ∀ p : Fin pairs, quotes[p] ≤ G)
    {calls width : ℕ} (fits : widthLimit pairs J G T ≤ width)
    (trialBound : ∀ s, ValidSelection J quotes s → (trial s).Bound calls width)
    (intervalBound : ∀ s ranges, ValidSelection J quotes s → (trial s).value = .blocked ranges →
      ∀ p : Fin pairs, ranges[p].lo ≤ ranges[p].hi ∧ ranges[p].hi ≤ G) :
    (search J trial T (initialTable quotes)).Bound
      (1 + T*(2 + selectLimit pairs J T + calls + updateLimit pairs T)) width := by
  let pureTrial : Trial pairs Answer := fun s => (trial s).value
  let states := stateAt J pureTrial (initialTable quotes)
  let cost := 2 + selectLimit pairs J T + calls + updateLimit pairs T
  have go (remaining t : ℕ) (h : t + remaining ≤ T) :
      (search J trial remaining (states t)).Bound (1 + remaining*cost) width := by
    induction remaining generalizing t with
    | zero => simp [search, Run.Bound]
    | succ n ih =>
      let state := states t
      let s := select J state
      have cs := (selectTable_bound J G T pureTrial quotes t (by omega) hGrid).weaken le_rfl fits
      have valid : ValidSelection J quotes s :=
        select_valid J quotes state (stateAt_count J pureTrial quotes t)
      have ct := trialBound s valid
      cases ht : (trial s).value with
      | cleared answer =>
        have slots : (selectTable J state).work.slots ≤ selectLimit pairs J T := cs.1
        have trialSlots := ct.1
        constructor
        · simp [search, show states t = state from rfl, show select J state = s from rfl, ht]
          rw [Nat.succ_mul]
          dsimp only [cost]
          omega
        · simpa [search, show states t = state from rfl, show select J state = s from rfl, ht,
            max_le_iff] using And.intro cs.2 ct.2
      | blocked ranges =>
        have H := intervalBound s ranges valid ht
        have cd := (updateTable_bound J G T pureTrial quotes t (by omega) hGrid ranges H).weaken le_rfl fits
        have next : states (t+1) = double state ranges := by
          change turn J pureTrial state = _
          simp [turn, pureTrial, show select J state = s from rfl, ht]
        have remaining := ih (t+1) (by omega)
        rw [next] at remaining
        have slots : (selectTable J state).work.slots ≤ selectLimit pairs J T := cs.1
        have trialSlots := ct.1
        have updateSlots : (updateTable state ranges).work.slots ≤ updateLimit pairs T := cd.1
        have nextSlots := remaining.1
        dsimp only [cost] at nextSlots
        constructor
        · simp [search, show states t = state from rfl, show select J state = s from rfl, ht]
          rw [Nat.succ_mul]
          dsimp only [cost]
          omega
        · simp only [search, Run.bind_width, selectTable_value,
            show states t = state from rfl, show select J state = s from rfl,
            step_value, ht, step_width, updateTable_value, max_le_iff]
          exact ⟨cs.2, ct.2, Nat.zero_le _, cd.2, remaining.2⟩
  exact go T 0 (by omega)

end Kintali.QuoteSearch.DriverWork
