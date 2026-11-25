module

public import Kintali.TrialWork.Execute
public import Kintali.TrialWork.SelectedChecks
public import Kintali.ContactSize.Recovery
public import Kintali.InputOutput.InitializationWork
import all Kintali.InputOutput.Grid

/-! A prepared restricted trial on the public input. Bids and cut lists
are supplied once by the retained-inventory constructor. The contact is
stored once, its projection is shared, and the matching reply executes
the exact repair or the two blocker searches. -/

@[expose] public section
namespace Kintali.TrialWork.Selected

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery MarketTrial QuoteSearch
open QuotaSweep ContactSize InputOutput LinearProgramming

variable {k m : ℕ}

def route (st : InitializationWork.State k m) (i : Fin k) : Fin m := st.prepared.directory.toSite[i.val]

def after (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (s : Selection (a.types*a.targets))
    (l : Lists a (route st) s) (z : StoredLookup.SelectedStored a (route st) s) :
    Run (Reply (a.types*a.targets) (Strategy a.types a.targets)) :=
  let snap := projectAt st.prepared.scales.grid correct.grid l st.tables.fields st.prepared.directory.toSite
    z st.prepared.scales.privateScale st.tolerance
  let tol : 0 ≤ snap.value.point.tolerance := by
    dsimp only [snap]
    rw [projectAt_eq]
    change 0 ≤ st.tolerance
    rw [correct.tolerance]
    exact (contactTolerance_pos _).le
  let out := execute st.tables.fields snap.value hm tol st.prepared.counts st.denominator st.coefficient
  ⟨out.value,snap.work.seq out.work⟩

/-- The contact sweep is charged to the same `Stored` value used by the
allocation lookups in projection and in both branches. -/
def trial (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (s : Selection (a.types*a.targets))
    (l : Lists a (route st) s) : Run (Reply (a.types*a.targets) (Strategy a.types a.targets)) :=
  ContactCharge.selected a (route st) s >>= after a hm st correct s l

private theorem execute_for {g : Game (Fin k) (Fin m)} (f : Fields k m) (fg : f.game = g)
    (z : Snapshot k m (grid g)) (hm : 0 < m) (tol : 0 ≤ z.point.tolerance)
    (s : Selection (k*m)) (agree : Agrees z (sparseView g hm s))
    (eps : z.point.tolerance = contactTolerance g) :
    (execute f z hm tol (eligible g hm) (denominator g) (coefficientHeight g)).value =
      MarketTrial.run g hm (sparseView g hm) s := by
  subst g
  exact execute_value f z hm tol _ s agree eps

theorem trial_value (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (s : Selection (a.types*a.targets))
    (l : Lists a (route st) s) : (trial a hm st correct s l).value =
    MarketTrial.run a.game hm (sparseView a.game hm) s := by
  let f := st.tables.fields
  let dir := st.prepared.directory.toSite
  let z := (ContactCharge.selected a (route st) s).value
  let snap := (project l f dir z (privateScale a.game) (contactTolerance a.game)).value
  have fg : f.game = a.game := correct.game
  have routed : route st = redirect a.game hm := funext correct.targets
  have agree := project_agrees l f fg dir (fun _ => rfl) hm routed (contactTolerance a.game)
  have eps : snap.point.tolerance = contactTolerance a.game := rfl
  have tol : 0 ≤ snap.point.tolerance := (contactTolerance_pos a.game).le
  have h := execute_for f fg snap hm tol s agree eps
  simpa only [trial,Run.bind_value,after,projectAt_eq,correct.privateScale,correct.tolerance,
    correct.counts,correct.denominator,correct.coefficient] using h

def repairWidth (L : ℕ) := inputWidth L+indexWidth L L+exactVars L L+Binary.repairBound L+
  2*RationalInput.widthLimit (repairLength L)+1

def repairSlots (L : ℕ) := RepairWork.solveSlots L L (repairLength L) (repairWidth L) 3 (12+(2*2+2)) 2 2 2

def executeSlots (L : ℕ) := patternSlots L L 2 (inputWidth L)+relaxSlots L L L 2 2 (inputWidth L)+
  repairSlots L+blockedSlots L+2

def executeWidth (L : ℕ) := patternWidth (inputWidth L)+relaxWidth L L L (inputWidth L)+
  scalarWidth (repairWidth L)+blockedWidth L

def trialSlots (L : ℕ) := ContactCharge.slots L+(projectSlots L+executeSlots L)
def trialWidth (L : ℕ) := ContactCharge.width L+projectWidth L+executeWidth L
def afterSlots (L : ℕ) := projectSlots L+executeSlots L
def afterWidth (L : ℕ) := projectWidth L+executeWidth L

private theorem repairSlots_le {k m N n w : ℕ} (hk : k ≤ N) (hm : m ≤ N) :
    RepairWork.solveSlots k m n w 3 (12+(2*2+2)) 2 2 2 ≤
      RepairWork.solveSlots N N n w 3 (12+(2*2+2)) 2 2 2 := by
  have rr : exactRows k m ≤ exactRows N N := by unfold exactRows; gcongr
  have vv : exactVars k m ≤ exactVars N N := by unfold exactVars; gcongr
  unfold RepairWork.solveSlots RowWork.denseSlots RowWork.rowSlots OutputWork.strategySlots OutputWork.attackRowSlots
  gcongr

set_option maxHeartbeats 1200000 in
private theorem repair_bound (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s)
    (d : Fields a.types a.targets) (dg : d.game = a.game)
    (fd : FieldBound d 2 (fieldsWidth (Binary.lengthInput a))) (z : Snapshot a.types a.targets (grid a.game))
    (ag : Agrees z (sparseView a.game valid.1 s)) (eps : z.point.tolerance = contactTolerance a.game)
    {p : Pattern (Fin a.types) (Fin a.targets)} {r : RuleFields a.types a.targets}
    (reads : RuleReads r p) (rules : RuleBound r 2 (inputWidth (Binary.lengthInput a))) :
    let L := Binary.lengthInput a
    (repairRun d z.point r (denominator a.game) (coefficientHeight a.game)).Bound (repairSlots L)
      (scalarWidth (repairWidth L)) := by
  let L := Binary.lengthInput a
  let w := repairWidth L
  let len := repairLength L
  have k : a.types ≤ L := (Binary.dimensions a).2.1
  have m : a.targets ≤ L := (Binary.dimensions a).1
  have num : exactRows a.types a.targets ≤ exactRows L L := by unfold exactRows; gcongr
  have vars : exactVars a.types a.targets ≤ exactVars L L := by unfold exactVars; gcongr
  have wi : inputWidth L ≤ w := by unfold w repairWidth; omega
  have row : indexWidth a.types a.targets ≤ w := by unfold indexWidth; unfold w repairWidth indexWidth; omega
  have var : (exactVars a.types a.targets).size ≤ w := (size_le_self _).trans (by unfold w repairWidth; omega)
  have data : tableBits a.game ≤ Binary.repairBound L := (Binary.repair_bounds a valid).2.2.2
  have raw := denominator_size a.game
  have den : (denominator d.game).size ≤ w := by rw [dg]; unfold w repairWidth; omega
  have wp : 2*RationalInput.widthLimit len ≤ w := by unfold w repairWidth len; omega
  have length : RationalInput.inputLength (recoveryInput d.game p)
      (recoveryPoint z.point.x z.point.q z.point.threshold z.point.tolerance) (coefficientHeight d.game) ≤ len := by
    rw [dg,ag.coverage,ag.joint,ag.pressure,eps]
    exact sparse_recovery_length a valid normal s hs p
  have rr : RuleBound r 2 w := ⟨fun i => (rules.ref i).weaken le_rfl wi,
    fun i j => (rules.marked i j).weaken le_rfl wi,fun j => (rules.status j).weaken le_rfl wi⟩
  have h := repairRun_work d z.point reads ((checked_fields a fd).mono wi) rr row var den wp length
  rw [dg] at h
  apply h.weaken _ le_rfl
  exact repairSlots_le k m

theorem after_work (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (st : InitializationWork.State a.types a.targets) (correct : InitializationWork.Correct a valid.1 st)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) (l : Lists a (route st) s) :
    let L := Binary.lengthInput a
    let contact := (Sparse.selectedRun (G := grid a.game) a.game (route st) s (privateScale a.game)).1
    (after a valid.1 st correct s l contact).Bound (afterSlots L) (afterWidth L) := by
  let L := Binary.lengthInput a
  let f := st.tables.fields
  let dir := st.prepared.directory.toSite
  let z := (ContactCharge.selected a (route st) s).value
  let measured := project l f dir z (privateScale a.game) (contactTolerance a.game)
  let snap := measured.value
  have fg : f.game = a.game := correct.game
  have fs : FieldBound f 2 (fieldsWidth L) := correct.fields
  have eq : route st = redirect a.game valid.1 := funext correct.targets
  have agr : Agrees snap (sparseView a.game valid.1 s) :=
    project_agrees l f fg dir (fun _ => rfl) _ eq _
  have pt := point_bound l f fg dir (fun _ => rfl) valid normal hs eq
  have eps : snap.point.tolerance = contactTolerance a.game := rfl
  have tol : 0 ≤ snap.point.tolerance := (contactTolerance_pos a.game).le
  let pat := preparePattern f snap.point valid.1 tol
  let r := pat.value.2
  have read : RuleReads r pat.value.1 := preparePattern_reads ..
  have prep := prepared_bound a fs pt valid.1 tol
  have chk := checked_bound a fs pt prep.2
  have rep := repair_bound a valid normal s hs f fg fs snap agr eps read prep.2
  have preds := predicates_work l f fg dir (fun _ => rfl) valid normal hs fs eq
  have rejected := Snapshot.blocked_work a valid snap st.prepared.counts correct.counts preds
  have wc : patternWidth (inputWidth L) ≤ executeWidth L := by unfold executeWidth; omega
  have wt : relaxWidth L L L (inputWidth L) ≤ executeWidth L := by unfold executeWidth; omega
  have wr : scalarWidth (repairWidth L) ≤ executeWidth L := by unfold executeWidth; omega
  have wb : blockedWidth L ≤ executeWidth L := by unfold executeWidth; omega
  have run : (execute f snap valid.1 tol st.prepared.counts (denominator a.game) (coefficientHeight a.game)).Bound
      (executeSlots L) (executeWidth L) :=
    execute_work f snap valid.1 tol st.prepared.counts _ _ (prep.1.weaken le_rfl wc)
      (chk.weaken le_rfl wt) (fun _ => rep.weaken le_rfl wr) (fun _ => rejected.weaken le_rfl wb)
  have projection : measured.Bound (projectSlots L) (projectWidth L) :=
    project_work l f dir valid normal hs fs _
  let answer := execute f snap valid.1 tol st.prepared.counts (denominator a.game) (coefficientHeight a.game)
  simp only [after,projectAt_eq,correct.privateScale,correct.tolerance,correct.denominator,correct.coefficient]
  change measured.work.slots+answer.work.slots ≤ projectSlots L+executeSlots L ∧
    max measured.work.width answer.work.width ≤ afterWidth L
  exact ⟨Nat.add_le_add projection.1 run.1,(max_le_max projection.2 run.2).trans (by unfold afterWidth; omega)⟩

/-- Accepts the stored output of any charged implementation of the
selected contact on this inventory. Construction of the caller's
contact contributes its own work to the total. -/
def trialWith (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (s : Selection (a.types*a.targets))
    (l : Lists a (route st) s) (contact : Run (StoredLookup.SelectedStored a (route st) s)) :
    Run (Reply (a.types*a.targets) (Strategy a.types a.targets)) :=
  contact >>= after a hm st correct s l

theorem trialWith_value (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (s : Selection (a.types*a.targets))
    (l : Lists a (route st) s) (contact : Run (StoredLookup.SelectedStored a (route st) s))
    (value : contact.value = (Sparse.selectedRun (G := grid a.game) a.game (route st) s (privateScale a.game)).1) :
    (trialWith a hm st correct s l contact).value = MarketTrial.run a.game hm (sparseView a.game hm) s := by
  simp only [trialWith,Run.bind_value,value]
  exact trial_value a hm st correct s l

theorem trialWith_work (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (st : InitializationWork.State a.types a.targets) (correct : InitializationWork.Correct a valid.1 st)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) (l : Lists a (route st) s)
    (contact : Run (StoredLookup.SelectedStored a (route st) s))
    (value : contact.value = (Sparse.selectedRun (G := grid a.game) a.game (route st) s (privateScale a.game)).1)
    {c w : ℕ} (work : contact.Bound c w) :
    let L := Binary.lengthInput a
    (trialWith a valid.1 st correct s l contact).Bound (c+afterSlots L) (max w (afterWidth L)) := by
  let L := Binary.lengthInput a
  apply bound_bind (work.weaken le_rfl (Nat.le_max_left w (afterWidth L)))
  rw [value]
  exact (after_work a valid normal st correct s hs l).weaken le_rfl (Nat.le_max_right ..)

theorem trial_work (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (st : InitializationWork.State a.types a.targets) (correct : InitializationWork.Correct a valid.1 st)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) (l : Lists a (route st) s) :
    let L := Binary.lengthInput a
    (trial a valid.1 st correct s l).Bound (trialSlots L) (trialWidth L) := by
  let L := Binary.lengthInput a
  have h := trialWith_work a valid normal st correct s hs l (ContactCharge.selected a (route st) s)
    (ContactCharge.selected_value ..) (ContactCharge.selected_work a (route st) s hs)
  exact h.weaken le_rfl (show max (ContactCharge.width L) (afterWidth L) ≤ trialWidth L by
    unfold trialWidth afterWidth; omega)

end Kintali.TrialWork.Selected
