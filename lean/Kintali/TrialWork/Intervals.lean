module

public import Kintali.TrialWork.Blockers
public import Kintali.TrialWork.RowRules
public import Kintali.QuoteSearch.PrefixWork
public import Kintali.QuoteSearch.ClockWork

/-! Both endpoints use the charged binary search, sharing the logarithmic
fuel computed from the eligible count. The trial stores one result per
type and target. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery QuoteSearch LinearProgramming.ArithmeticRun

variable {k m G : ℕ}

def optional (test : Quote G → Run Bool) (q : ℕ) : Run Bool :=
  let inside := step (max q.size G.size) (decide (q<G))
  if h : inside.value = true then
    let a : Fin G := ⟨q,of_decide_eq_true h⟩
    let z := test a.castSucc
    ⟨z.value,inside.work.seq z.work⟩
  else ⟨false,inside.work⟩

@[simp] theorem optional_value (t : Quote G → Run Bool) (q : ℕ) :
    (optional t q).value = MarketTrial.atOptional (fun z => (t z).value) q := by
  by_cases h : q < G <;> simp [optional,MarketTrial.atOptional,h]

theorem optional_work (t : Quote G → Run Bool) {c w : ℕ} (work : ∀ z, (t z).Bound c w)
    (grid : G.size ≤ w) {q : ℕ} (hq : q < G) : (optional t q).Bound (1+c) w := by
  have qs := (Nat.size_le_size hq.le).trans grid
  have h := work (Fin.castSucc (⟨q,hq⟩ : Fin G))
  simpa [optional,hq,Run.Bound,Work.seq,qs,grid,max_le_iff] using h

def interval (buyer site : ℕ → Run Bool) (eligible : ℕ) : Run Interval := do
  let l ← ClockWork.logRun eligible
  let fuel ← natAdd l 1
  let lo ← PrefixWork.search (fun q => do let x ← site q; step 1 (!x)) fuel 0 eligible
  let hi ← PrefixWork.search buyer fuel 0 eligible
  let lower ← step (max lo.size hi.size) (min lo hi)
  step 0 ⟨lower,hi⟩

@[simp] theorem interval_value (buyer site : ℕ → Run Bool) (eligible : ℕ) :
    (interval buyer site eligible).value =
      intervalFor (fun q => (buyer q).value) (fun q => (site q).value) eligible := by
  simp [interval,intervalFor,prefixLength,PrefixWork.search_value,natAdd]

private theorem locate_le (test : ℕ → Bool) (fuel lo hi : ℕ) (bound : lo ≤ hi) :
    locate test fuel lo hi ≤ hi := by
  induction fuel generalizing lo hi with
  | zero => exact bound
  | succ fuel ih =>
    unfold locate
    split
    · exact bound
    · dsimp only
      split
      · apply ih; omega
      · exact (ih _ _ (by omega)).trans (by omega)

private theorem log_le_size (n : ℕ) : n.log2 ≤ n.size := by
  by_cases h : n = 0
  · subst n; decide
  · exact ((Nat.log2_lt h).mpr (Nat.lt_size_self _)).le

def intervalSlots (c w : ℕ) := 1+3*w+1+2*(1+(w+1)*(c+7))+2

theorem interval_work (buyer site : ℕ → Run Bool) {e c w : ℕ} (idx : e.size ≤ w)
    (small : 2 ≤ w) (b : ∀ q < e, (buyer q).Bound c w) (s : ∀ q < e, (site q).Bound c w) :
    (interval buyer site e).Bound (intervalSlots c w) w := by
  let fuel := e.log2+1
  let test := fun q => do let x ← site q; step 1 (!x)
  have log := (log_le_size e).trans idx
  have bits := (Nat.size_le_size (Nat.log2_le_self e)).trans idx
  have fw : fuel ≤ w+1 := by dsimp [fuel]; omega
  have one : 1 ≤ w := by omega
  have low := PrefixWork.search_bound test fuel 0 e (Nat.zero_le e) le_rfl idx small
    (fun q hq => bound_bind (s q hq) ((bound_step 1 _).weaken le_rfl one))
  have high := PrefixWork.search_bound buyer fuel 0 e (Nat.zero_le e) le_rfl idx small b
  have sl := Nat.mul_le_mul_right ((c+1)+6) fw
  have unit : (c+1)+6 = c+7 := by omega
  rw [unit] at sl
  have sh := Nat.mul_le_mul_right (c+6) fw
  have up : (w+1)*(c+6) ≤ (w+1)*(c+7) := Nat.mul_le_mul_left _ (by omega)
  have last (f : ℕ → Run Bool) : (PrefixWork.search f fuel 0 e).value.size ≤ w := by
    rw [PrefixWork.search_value]
    exact (Nat.size_le_size (locate_le _ _ _ _ (Nat.zero_le e))).trans idx
  unfold interval
  apply Run.Bound.weaken (k := (1+3*e.log2)+(1+
    ((1+fuel*((c+1)+6))+((1+fuel*(c+6))+(1+1))))) (w := w) ?_ (by rw [unit]; unfold intervalSlots; omega) le_rfl
  apply bound_bind (ClockWork.logRun_work e idx one)
  rw [ClockWork.logRun_value]
  apply bound_bind (show (natAdd e.log2 1).Bound 1 w from ⟨le_rfl,max_le bits one⟩)
  apply bound_bind low
  apply bound_bind high
  apply bound_bind ((bound_step _ _).weaken le_rfl (max_le (last test) (last buyer)))
  exact (bound_step 0 _).weaken le_rfl (Nat.zero_le _)

def intervals (buy site : Fin k → Fin m → Quote G → Run Bool) (counts : Vector ℕ (k*m)) :
    Run (Vector Interval (k*m)) := tabulate (k*m) fun i => do
  let p ← splitProd i
  let e ← step (k*m).size counts[i.val]
  interval (optional (buy p.1 p.2)) (optional (site p.1 p.2)) e

theorem intervals_value {g : Game (Fin k) (Fin m)} (hm : 0 < m) (view : MarketTrial.ContactView k m (MarketTrial.grid g))
    (buy site : Fin k → Fin m → Quote (MarketTrial.grid g) → Run Bool)
    (buyer : ∀ i j z, (buy i j z).value = view.buyerAccepts i j z)
    (seller : ∀ i j z, (site i j z).value = view.siteAccepts i j z) :
    (intervals buy site (MarketTrial.eligible g hm)).value = MarketTrial.blockerIntervals g hm view := by
  simp [intervals,MarketTrial.blockerIntervals,buyer,seller]

def intervalsSlots (pairs c w : ℕ) := 3*(pairs+1)+pairs*(2+(1+intervalSlots (c+1) w))

theorem intervals_work (buy site : Fin k → Fin m → Quote G → Run Bool) (counts : Vector ℕ (k*m))
    {c w : ℕ} (pairSize : (k*m).size ≤ w) (sites : m.size ≤ w) (grid : G.size ≤ w) (small : 2 ≤ w)
    (count : ∀ i : Fin (k*m), counts[i.val] ≤ G)
    (buyer : ∀ i j z, (buy i j z).Bound c w) (seller : ∀ i j z, (site i j z).Bound c w) :
    (intervals buy site counts).Bound (intervalsSlots (k*m) c w) w := by
  apply tabulate_bound _ pairSize
  intro i
  apply bound_bind (splitProd_work i pairSize sites)
  apply bound_bind ((bound_step _ _).weaken le_rfl pairSize)
  exact interval_work _ _ ((Nat.size_le_size (count i)).trans grid) small
    (fun _ hq => (optional_work _ (buyer _ _) grid (hq.trans_le (count i))).weaken (by omega) le_rfl)
    (fun _ hq => (optional_work _ (seller _ _) grid (hq.trans_le (count i))).weaken (by omega) le_rfl)

end Kintali.TrialWork
