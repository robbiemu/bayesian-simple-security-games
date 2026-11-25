module

public import Kintali.TrialWork.SelectedProjection
public import Kintali.TrialWork.Relaxed

/-! Bind the successful and blocked checks to the cached sparse snapshot.
The two prefix searches per pair use the eligible counts prepared before
the first trial. -/

@[expose] public section
namespace Kintali.TrialWork.Selected

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery MarketTrial QuoteSearch
open QuotaSweep ContactSize InputOutput

variable {k m G : ℕ}

def Snapshot.blocked (z : Snapshot k m G) (counts : Vector ℕ (k*m)) := intervals z.buyer z.seller counts

theorem Snapshot.blocked_value {g : Game (Fin k) (Fin m)} (hm : 0 < m)
    {z : Snapshot k m (grid g)} {v : ContactView k m (grid g)} (ag : Agrees z v)
    {counts : Vector ℕ (k*m)} (eq : counts = eligible g hm) :
    (z.blocked counts).value = blockerIntervals g hm v := by
  subst counts
  exact intervals_value hm v z.buyer z.seller ag.buyer ag.seller

theorem pattern_agrees {g : Game (Fin k) (Fin m)} (d : Fields k m) (dg : d.game = g) (hm : 0 < m)
    {z : Snapshot k m (grid g)} {v : ContactView k m (grid g)} (ag : Agrees z v)
    (tol : 0 ≤ z.point.tolerance) (t : z.point.tolerance = contactTolerance g) :
    (preparePattern d z.point hm tol).value.1 = MarketTrial.pattern g hm v := by
  subst g
  rw [preparePattern_value]
  simp only [MarketTrial.pattern,ag.coverage,t]

theorem relaxed_agrees {g : Game (Fin k) (Fin m)} (d : Fields k m) (dg : d.game = g)
    {z : Snapshot k m (grid g)} {v : ContactView k m (grid g)} (ag : Agrees z v)
    {r : RuleFields k m} {p : Pattern (Fin k) (Fin m)} (rd : RuleReads r p)
    (t : z.point.tolerance = contactTolerance g) : (relaxed d z.point r).value = relaxedCheck g p v := by
  subst g
  exact relaxed_value d z.point rd v ag.coverage ag.joint ag.pressure t

theorem checked_fields (a : Input) {d : Fields a.types a.targets}
    (fd : FieldBound d 2 (fieldsWidth (Binary.lengthInput a))) :
    FieldBound d 2 (inputWidth (Binary.lengthInput a)) :=
  fd.mono (by unfold inputWidth scalarWidth; omega)

theorem prepared_bound (a : Input) {d : Fields a.types a.targets} {v : Point a.types a.targets}
    (fd : FieldBound d 2 (fieldsWidth (Binary.lengthInput a)))
    (pt : PointBound v (inputWidth (Binary.lengthInput a))) (hm : 0 < a.targets)
    (tol : 0 ≤ v.tolerance) :
    let L := Binary.lengthInput a
    (preparePattern d v hm tol).Bound (patternSlots L L 2 (inputWidth L)) (patternWidth (inputWidth L)) ∧
      RuleBound (preparePattern d v hm tol).value.2 2 (inputWidth L) := by
  let L := Binary.lengthInput a
  obtain ⟨p,r⟩ := preparePattern_bound d (checked_fields a fd) pt hm tol
  have k : a.types ≤ L := (Binary.dimensions a).2.1
  have m : a.targets ≤ L := (Binary.dimensions a).1
  exact ⟨p.weaken (by unfold patternSlots tableSlots referenceSlots; gcongr) le_rfl,r⟩

theorem checked_bound (a : Input) {d : Fields a.types a.targets} {v : Point a.types a.targets}
    {r : RuleFields a.types a.targets} (fd : FieldBound d 2 (fieldsWidth (Binary.lengthInput a)))
    (pt : PointBound v (inputWidth (Binary.lengthInput a))) (rb : RuleBound r 2 (inputWidth (Binary.lengthInput a))) :
    let L := Binary.lengthInput a
    (relaxed d v r).Bound (relaxSlots L L L 2 2 (inputWidth L)) (relaxWidth L L L (inputWidth L)) := by
  let L := Binary.lengthInput a
  have k : a.types ≤ L := (Binary.dimensions a).2.1
  have m : a.targets ≤ L := (Binary.dimensions a).1
  have rr : exactRows a.types a.targets ≤ exactRows L L := by unfold exactRows; gcongr
  exact (relaxed_work d (checked_fields a fd) pt rb k m).weaken
    (by unfold relaxSlots; gcongr) (by unfold relaxWidth indexWidth; gcongr)

def blockedWidth (L : ℕ) := blockWidth (inputWidth L)+L*L+L+Binary.gridBitBound L+2
def blockedSlots (L : ℕ) := intervalsSlots (L*L) (predicateSlots L) (blockedWidth L)

theorem Snapshot.blocked_work (a : Input) (valid : a.Valid)
    (z : Snapshot a.types a.targets (grid a.game)) (counts : Vector ℕ (a.types*a.targets))
    (eq : counts = eligible a.game valid.1)
    (pred : ∀ i j q, (z.buyer i j q).Bound (predicateSlots (Binary.lengthInput a)) (blockWidth (inputWidth (Binary.lengthInput a))) ∧
      (z.seller i j q).Bound (predicateSlots (Binary.lengthInput a)) (blockWidth (inputWidth (Binary.lengthInput a)))) :
    (z.blocked counts).Bound (blockedSlots (Binary.lengthInput a)) (blockedWidth (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  let W := blockedWidth L
  have pairs : a.types*a.targets ≤ L*L := Nat.mul_le_mul (Binary.dimensions a).2.1 (Binary.dimensions a).1
  have idx : (a.types*a.targets).size ≤ W := (size_le_self _).trans (pairs.trans (by unfold W blockedWidth; omega))
  have sites : a.targets.size ≤ W := (size_le_self _).trans ((Binary.dimensions a).1.trans
    (show L ≤ W by unfold W blockedWidth; omega))
  have grid := (Binary.grid_size a valid).trans (show Binary.gridBitBound L ≤ W by unfold W blockedWidth; omega)
  have small : 2 ≤ W := by unfold W blockedWidth; omega
  have wide : blockWidth (inputWidth L) ≤ W := by unfold W blockedWidth; omega
  have count (p : Fin (a.types*a.targets)) : counts[p.val] ≤ MarketTrial.grid a.game := by
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective p
    rw [eq]
    exact (eligible_at a.game valid.1 i j).le.trans (eligibleCount_le ..)
  have h := intervals_work z.buyer z.seller counts idx sites grid small count
    (fun i j q => (pred i j q).1.weaken le_rfl wide) (fun i j q => (pred i j q).2.weaken le_rfl wide)
  apply h.weaken _ le_rfl
  unfold intervalsSlots blockedSlots
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.succ_le_succ pairs)) (Nat.mul_le_mul_right _ pairs)

end Kintali.TrialWork.Selected
