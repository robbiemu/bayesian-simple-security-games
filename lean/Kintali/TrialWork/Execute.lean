module

public import Kintali.TrialWork.SelectedChecks
public import Kintali.TrialWork.StoredPattern
public import Kintali.TrialWork.Repair
public import Kintali.TrialWork.Intervals

/-! # The restricted trial after reading its sparse contact -/

@[expose] public section

namespace Kintali.TrialWork

open StochasticGames.CompilerRun
open ExactRecovery QuoteSearch MarketTrial

variable {k m G : ℕ}

def reply (f : Fields k m) (z : Selected.Snapshot k m G) (r : RuleFields k m)
    (counts : Vector ℕ (k*m)) (d h : ℕ) : Run (Reply (k*m) (Strategy k m)) := do
  let good ← relaxed f z.point r
  let found ← step 0 good
  if found then
    let a ← repairRun f z.point r d h
    step 0 (.cleared a)
  else
    let ranges ← intervals z.buyer z.seller counts
    step 0 (.blocked ranges)

def execute (f : Fields k m) (z : Selected.Snapshot k m G) (hm : 0 < m)
    (tol : 0 ≤ z.point.tolerance) (counts : Vector ℕ (k*m)) (d h : ℕ) :
    Run (Reply (k*m) (Strategy k m)) := do
  let p ← preparePattern f z.point hm tol
  reply f z p.2 counts d h

theorem execute_value (f : Fields k m) (z : Selected.Snapshot k m (grid f.game))
    (hm : 0 < m) (tol : 0 ≤ z.point.tolerance)
    (contact : Selection (k*m) → ContactView k m (grid f.game)) (s : Selection (k*m))
    (agree : Selected.Agrees z (contact s)) (eps : z.point.tolerance = contactTolerance f.game) :
    (execute f z hm tol (eligible f.game hm) (denominator f.game) (coefficientHeight f.game)).value =
      MarketTrial.run f.game hm contact s := by
  let p := (preparePattern f z.point hm tol).value.1
  let r := (preparePattern f z.point hm tol).value.2
  have rd : RuleReads r p := preparePattern_reads ..
  have pa : p = MarketTrial.pattern f.game hm (contact s) :=
    Selected.pattern_agrees f rfl hm agree tol eps
  have pass := relaxed_value f z.point rd (contact s) agree.coverage agree.joint agree.pressure eps
  have after := repairRun_value f z.point rd
  have reject := intervals_value hm (contact s) z.buyer z.seller agree.buyer agree.seller
  simp only [execute, Run.bind_value]
  change (reply f z r (eligible f.game hm) (denominator f.game) (coefficientHeight f.game)).value = _
  cases good : (relaxed f z.point r).value
  · simp [reply, MarketTrial.run, ← pa, ← pass, good, reject]
  · simp [reply, MarketTrial.run, ← pa, ← pass, good, after,
      agree.coverage, agree.joint, agree.pressure, eps]

theorem reply_work (f : Fields k m) (z : Selected.Snapshot k m G) (r : RuleFields k m)
    (counts : Vector ℕ (k*m)) (d h : ℕ) {K A B W : ℕ}
    (check : (relaxed f z.point r).Bound K W)
    (yes : (relaxed f z.point r).value = true → (repairRun f z.point r d h).Bound A W)
    (no : (relaxed f z.point r).value = false → (intervals z.buyer z.seller counts).Bound B W) :
    (reply f z r counts d h).Bound (K+A+B+2) W := by
  obtain ⟨sc,wc⟩ := check
  cases hgood : (relaxed f z.point r).value with
  | false =>
    obtain ⟨s, w⟩ := no hgood
    constructor
    · simp [reply, hgood]
      omega
    · simp [reply, hgood, max_le_iff, wc, w]
  | true =>
    obtain ⟨s, w⟩ := yes hgood
    constructor
    · simp [reply, hgood]
      omega
    · simp [reply, hgood, max_le_iff, wc, w]

theorem execute_work (f : Fields k m) (z : Selected.Snapshot k m G) (hm : 0 < m)
    (tol : 0 ≤ z.point.tolerance) (counts : Vector ℕ (k*m)) (d h : ℕ) {P K A B W : ℕ}
    (prep : (preparePattern f z.point hm tol).Bound P W)
    (check : let r := (preparePattern f z.point hm tol).value.2
      (relaxed f z.point r).Bound K W)
    (yes : let r := (preparePattern f z.point hm tol).value.2
      (relaxed f z.point r).value = true → (repairRun f z.point r d h).Bound A W)
    (no : let r := (preparePattern f z.point hm tol).value.2
      (relaxed f z.point r).value = false → (intervals z.buyer z.seller counts).Bound B W) :
    (execute f z hm tol counts d h).Bound (P+K+A+B+2) W := by
  let r := (preparePattern f z.point hm tol).value.2
  have cr : (reply f z r counts d h).Bound (K+A+B+2) W := reply_work f z r counts d h check yes no
  constructor
  · change (preparePattern f z.point hm tol).work.slots + (reply f z r counts d h).work.slots ≤ _
    have := prep.1
    have := cr.1
    omega
  · exact max_le prep.2 cr.2

end Kintali.TrialWork
