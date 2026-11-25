module

public import Kintali.TrialWork.SelectedAccess

/-! Materialize both projected tables once from the selected stored
allocation. The buyer and site oracles capture its bid labels and holdings,
and the site also reads the stored coverage at each test quote. -/

@[expose] public section
namespace Kintali.TrialWork.Selected

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery MarketTrial QuoteSearch
open QuotaSweep ContactSize InputOutput QuotaSweep.StoredLookup

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

structure Snapshot (k m G : ℕ) where
  point : Point k m
  buyer : Fin k → Fin m → Quote G → Run Bool
  seller : Fin k → Fin m → Quote G → Run Bool

structure Agrees {k m G : ℕ} (z : Snapshot k m G) (v : ContactView k m G) : Prop where
  coverage : z.point.x = v.coverage
  joint : z.point.q = v.joint
  pressure : z.point.threshold = v.pressure
  buyer : ∀ i j q, (z.buyer i j q).value = v.buyerAccepts i j q
  seller : ∀ i j q, (z.seller i j q).value = v.siteAccepts i j q

/-- The scalar grid denominator comes from the prepared state. Reindexing
the quote type and the sparse accessor is erased by compilation. -/
@[noinline] def atGrid {k m G N : ℕ} {A H : Type} (same : N = G) (d : Fields k m)
    (ac : Access k m G A H) (rs : List A) (v : Point k m) : Snapshot k m G :=
  let current : Access k m N A H := same.symm ▸ ac
  let snap : Snapshot k m N := ⟨v,current.buyer d rs,current.siteTest v rs⟩
  same ▸ snap

theorem atGrid_eq {k m G N : ℕ} {A H : Type} (same : N = G) (d : Fields k m)
    (ac : Access k m G A H) (rs : List A) (v : Point k m) :
    atGrid same d ac rs v = ⟨v,ac.buyer d rs,ac.siteTest v rs⟩ := by subst N; rfl

def projectAt (N : ℕ) (eq : N = grid a.game) (l : Lists a toSite s) (d : Fields a.types a.targets)
    (dir : Vector (Fin a.targets) a.types) (z : SelectedStored a toSite s) (σ tol : ℚ) :
    Run (Snapshot a.types a.targets (grid a.game)) :=
  let real := l.reals
  let groups := l.groups
  let ac := access l d dir z
  let tab := ac.tables groups.value real.value σ
  let v : Point a.types a.targets := ⟨tab.value.1,tab.value.2,z.pressure,tol⟩
  ⟨atGrid eq d ac real.value v,real.work.seq (groups.work.seq (tab.work.seq (Work.one 0)))⟩

def project (l : Lists a toSite s) (d : Fields a.types a.targets)
    (dir : Vector (Fin a.targets) a.types) (z : SelectedStored a toSite s) (σ tol : ℚ) :
    Run (Snapshot a.types a.targets (grid a.game)) :=
  projectAt (grid a.game) rfl l d dir z σ tol

theorem projectAt_eq (N : ℕ) (eq : N = grid a.game) (l : Lists a toSite s) (d : Fields a.types a.targets)
    (dir : Vector (Fin a.targets) a.types) (z : SelectedStored a toSite s) (σ tol : ℚ) :
    projectAt N eq l d dir z σ tol = project l d dir z σ tol := by subst N; rfl

theorem project_agrees (l : Lists a toSite s) (d : Fields a.types a.targets) (dg : d.game = a.game)
    (dir : Vector (Fin a.targets) a.types) (dt : ∀ i : Fin a.types, dir[i.val] = toSite i)
    (hm : 0 < a.targets) (route : toSite = redirect a.game hm) (tol : ℚ) :
    let z := (ContactCharge.selected a toSite s).value
    Agrees (project l d dir z (privateScale a.game) tol).value (sparseView a.game hm s) := by
  subst toSite
  dsimp only
  rw [sparseView_eq]
  let g := a.game
  let k := a.types
  let m := a.targets
  let f := redirect g hm
  let z := (ContactCharge.selected a f s).value
  let ac := access l d dir z
  let layout := Sparse.selectedLayout (G := grid g) g f s
  let x := z.encodedView.allocation
  let reals := l.reals.value
  let gs := l.groups.value
  let v := (project l d dir z (privateScale g) tol).value.point
  have rd := access_reads l d dg dir dt z
  have rD : Reads ac d.game layout x f := by rw [dg]; exact rd
  have ru : reals.Nodup := by rw [show reals = _ from l.reals_value]; exact List.nodup_finRange _
  have all (q) : q ∈ reals := by rw [show reals = _ from l.reals_value]; exact List.mem_finRange _
  have table := ac.tables_value rd gs reals l.groups_unique l.groups_complete ru all (privateScale g)
  have cov : v.x = Sparse.siteCoverage g (privateScale g) layout x := by
    funext j
    change (ac.tables gs reals (privateScale g)).value.1[j.val] = _
    rw [table]; simp only [Vector.getElem_ofFn]; rfl
  have jt : v.q = Sparse.attackJoint layout f x := by
    funext i j
    change (ac.tables gs reals (privateScale g)).value.2[i.val][j.val] = _
    rw [table]; simp only [Vector.getElem_ofFn]; rfl
  refine ⟨cov,jt,rfl,?_,?_⟩
  · intro i j q
    exact (ac.buyer_value d rD reals all i j q).trans (by rw [dg]; rfl)
  · intro i j q
    exact (ac.siteTest_value v rd reals all i j q).trans (by rw [cov]; rfl)

def projectSlots (L : ℕ) := Lists.labelsSlots L+
  Access.projectionSlots (sizeLimit L) (inputWidth L) (accessSlots L)+1

def projectWidth (L : ℕ) := Lists.labelsWidth L+Access.projectionWidth (sizeLimit L) (inputWidth L)

def predicateSlots (L : ℕ) := Access.blockSlots (sizeLimit L) 2 (accessSlots L) (inputWidth L)

theorem project_work (l : Lists a toSite s) (d : Fields a.types a.targets) (dir : Vector (Fin a.targets) a.types)
    (valid : a.Valid) (normal : ¬a.game.DirectCase) (hs : SelectionBound a s)
    (fd : FieldBound d 2 (fieldsWidth (Binary.lengthInput a))) (tol : ℚ) :
    let L := Binary.lengthInput a
    let z := (ContactCharge.selected a toSite s).value
    (project l d dir z (privateScale a.game) tol).Bound (projectSlots L) (projectWidth L) := by
  let L := Binary.lengthInput a
  let W := inputWidth L
  let N := sizeLimit L
  let z := (ContactCharge.selected a toSite s).value
  let ac := access l d dir z
  have rw : recordLimit L ≤ N := Nat.le_add_right ..
  have lw : L ≤ N := Nat.le_add_left ..
  have hsiz : scaleWidth L ≤ W := by unfold W inputWidth; omega
  have re : l.reals.value.length ≤ N := by
    rw [l.reals_value,List.length_finRange,← l.bidOrder]
    exact (l.bid_count hs).trans rw
  have tb := ac.tables_work (access_bound l d dir valid normal hs fd) l.groups.value l.reals.value
    ((l.groups_length hs).trans rw) re ((Binary.dimensions a).2.1.trans lw) ((Binary.dimensions a).1.trans lw)
    ((scale_fits a valid).mono hsiz)
  have labels := l.labels_work hs
  change (l.reals.work.slots+(l.groups.work.slots+(_+1)) ≤ projectSlots L) ∧
    max l.reals.work.width (max l.groups.work.width (max _ 0)) ≤ projectWidth L
  change l.reals.work.slots+l.groups.work.slots ≤ Lists.labelsSlots L ∧
    max l.reals.work.width l.groups.work.width ≤ Lists.labelsWidth L at labels
  obtain ⟨ts,tw⟩ := tb
  constructor
  · unfold projectSlots; dsimp only [W,N,L,ac,z] at *; omega
  · unfold projectWidth; dsimp only [W,N,L,ac,z] at *; omega

theorem point_bound (l : Lists a toSite s) (d : Fields a.types a.targets) (dg : d.game = a.game)
    (dir : Vector (Fin a.targets) a.types) (dt : ∀ i : Fin a.types, dir[i.val] = toSite i)
    (valid : a.Valid) (normal : ¬a.game.DirectCase) (hs : SelectionBound a s)
    (route : toSite = redirect a.game valid.1) :
    let z := (ContactCharge.selected a toSite s).value
    let v := (project l d dir z (privateScale a.game) (contactTolerance a.game)).value.point
    PointBound v (inputWidth (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  have hv : viewWidth L ≤ inputWidth L := by unfold inputWidth; omega
  have ht : toleranceWidth L ≤ inputWidth L := by unfold inputWidth; omega
  have agr := project_agrees l d dg dir dt valid.1 route (contactTolerance a.game)
  have v := sparse_view a valid normal s hs
  constructor
  · intro j; rw [agr.coverage]; exact (v.coverage j).mono hv
  · intro i j; rw [agr.joint]; exact (v.joint i j).mono hv
  · rw [agr.pressure]; exact v.pressure.mono hv
  · exact (tolerance_fits a valid).mono ht

theorem predicates_work (l : Lists a toSite s) (d : Fields a.types a.targets) (dg : d.game = a.game)
    (dir : Vector (Fin a.targets) a.types) (dt : ∀ i : Fin a.types, dir[i.val] = toSite i)
    (valid : a.Valid) (normal : ¬a.game.DirectCase) (hs : SelectionBound a s)
    (fd : FieldBound d 2 (fieldsWidth (Binary.lengthInput a))) (route : toSite = redirect a.game valid.1) :
    let L := Binary.lengthInput a
    let z := (ContactCharge.selected a toSite s).value
    let snap := (project l d dir z (privateScale a.game) (contactTolerance a.game)).value
    ∀ i j q, (snap.buyer i j q).Bound (predicateSlots L) (blockWidth (inputWidth L)) ∧
      (snap.seller i j q).Bound (predicateSlots L) (blockWidth (inputWidth L)) := by
  let L := Binary.lengthInput a
  let W := inputWidth L
  let z := (ContactCharge.selected a toSite s).value
  let ac := access l d dir z
  have af := access_bound l d dir valid normal hs fd
  have fw : fieldsWidth L ≤ W := by unfold W inputWidth scalarWidth; omega
  have grid : 2*((MarketTrial.grid a.game).size+1) ≤ W := by
    have b : (MarketTrial.grid a.game).size ≤ Binary.gridBitBound L := Binary.grid_size a valid
    unfold W inputWidth; omega
  have re : l.reals.value.length ≤ sizeLimit L := by
    rw [l.reals_value,List.length_finRange,← l.bidOrder]
    exact (l.bid_count hs).trans (Nat.le_add_right ..)
  have pt := point_bound l d dg dir dt valid normal hs route
  exact fun i j q => ⟨ac.buyer_work d af (fd.mono fw) grid _ re i j q,
    ac.siteTest_work af pt grid _ re i j q⟩

end Kintali.TrialWork.Selected
