module

public import Kintali.QuotaSweep.InventoryRun
public import Kintali.TrialWork.SelectedLists
public import Kintali.InputOutput.InitializationWork

/-! # Reading the selected real column and the consecutive private intervals -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected
open StochasticGames.CompilerRun StochasticGames.BinarySize LinearProgramming.ArithmeticRun

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def indexWidth (L : ℕ) := recordLimit L+L+Binary.gridBitBound L+6

def vectorBy {T : Type} {n : ℕ} (len : Run ℕ) (eq : len.value = n) (f : Fin n → Run T) : Run (Vector T n) :=
  let values := tabulate len.value (fun i => f (Fin.cast eq i))
  ⟨eq ▸ values.value,len.work.seq values.work⟩

theorem vectorBy_value {T : Type} {n : ℕ} (len : Run ℕ) (eq : len.value = n) (f : Fin n → Run T) :
    (vectorBy len eq f).value = Vector.ofFn (fun i => (f i).value) := by
  subst n; simp [vectorBy]

theorem vectorBy_work {T : Type} {n d c w : ℕ} (len : Run ℕ) (eq : len.value = n) (f : Fin n → Run T)
    (input : len.Bound d w) (dim : n.size ≤ w) (cells : ∀ i, (f i).Bound c w) :
    (vectorBy len eq f).Bound (d+(3*(n+1)+n*c)) w := by
  subst n
  exact ⟨Nat.add_le_add input.1 (tabulate_bound _ dim cells).1,max_le input.2 (tabulate_bound _ dim cells).2⟩

theorem cutLength (l : Lists a toSite s) (j : Fin a.targets) :
    (Sparse.partition (G := grid a.game) a.game toSite s j).groups+1 = l.cuts[j.val].length := by
  rw [l.cutOrder]
  let levels := (Sparse.siteCuts (G := grid a.game) a.game toSite s j).sort
  have nonempty : 0 < levels.length := List.length_pos_of_mem (show 0 ∈ levels by simp [levels,Sparse.siteCuts])
  change levels.length-1+1=levels.length
  omega

def cut (l : Lists a toSite s) (j : Fin a.targets)
    (ix : Fin ((Sparse.partition (G := grid a.game) a.game toSite s j).groups+1)) : Run ℕ :=
  let row := step j.val.size l.cuts[j.val]
  let value := get row.value (Fin.cast (cutLength l j) ix)
  ⟨value.value,row.work.seq value.work⟩

private theorem same_get {T : Type} {p q : List T} {n : ℕ} (eq : p = q) (i : Fin n)
    (hp : n = p.length) (hq : n = q.length) : p.get (Fin.cast hp i) = q.get (Fin.cast hq i) := by
  subst q; rfl

theorem cut_value (l : Lists a toSite s) (j : Fin a.targets)
    (ix : Fin ((Sparse.partition (G := grid a.game) a.game toSite s j).groups+1)) :
    (cut l j ix).value = (Sparse.partition (G := grid a.game) a.game toSite s j).cut ix := by
  change (get l.cuts[j.val] (Fin.cast (cutLength l j) ix)).value = _
  rw [get_value]
  exact same_get (l.cutOrder j) ix (cutLength l j)
    ((cutLength l j).trans (congrArg List.length (l.cutOrder j)))

theorem cut_work (l : Lists a toSite s) (hs : SelectionBound a s) (j : Fin a.targets)
    (ix : Fin ((Sparse.partition (G := grid a.game) a.game toSite s j).groups+1)) :
    let L := Binary.lengthInput a
    (cut l j ix).Bound (recordLimit L+2) (indexWidth L) := by
  let L := Binary.lengthInput a
  let W := indexWidth L
  have gc := Lists.group_count (a := a) (toSite := toSite) hs j
  have hi : ix.val ≤ recordLimit L := (Nat.le_of_lt_succ ix.isLt).trans gc
  have hj := (size_le_self j.val).trans (j.isLt.le.trans (Binary.dimensions a).1)
  have v := get_bound l.cuts[j.val] (Fin.cast (cutLength l j) ix)
  change 1+(get l.cuts[j.val] (Fin.cast (cutLength l j) ix)).work.slots ≤ _ ∧
    max j.val.size (get l.cuts[j.val] (Fin.cast (cutLength l j) ix)).work.width ≤ _
  simp only [Fin.val_cast] at v
  exact ⟨by have := v.1; omega,max_le (hj.trans (by unfold indexWidth; omega))
    (v.2.trans ((size_le_self _).trans (by unfold indexWidth; omega)))⟩

def groupSize (l : Lists a toSite s) (h : StoredLookup.SelectedGroups a toSite s) : Run ℕ := do
  let lo ← cut l h.1 h.2.castSucc
  let hi ← cut l h.1 h.2.succ
  natSub hi lo

@[simp] theorem groupSize_value (l : Lists a toSite s) (h : StoredLookup.SelectedGroups a toSite s) :
    (groupSize l h).value = (Sparse.selectedLayout (G := grid a.game) a.game toSite s).size h := by
  simp only [groupSize,Run.bind_value,cut_value,natSub,step_value]
  rfl

def rep (l : Lists a toSite s) (h : StoredLookup.SelectedGroups a toSite s) : Run (Fin (grid a.game)) :=
  let hi := cut l h.1 h.2.succ
  let idx := natSub hi.value 1
  let inside : idx.value < grid a.game := by
    change hi.value-1 < _
    rw [cut_value]
    have upper := (Sparse.partition (G := grid a.game) a.game toSite s h.1).hi_le_end h.2
    have lower := (Sparse.partition (G := grid a.game) a.game toSite s h.1).lo_lt_hi h.2
    change (Sparse.partition (G := grid a.game) a.game toSite s h.1).hi h.2-1 < _
    omega
  ⟨⟨idx.value,inside⟩,hi.work.seq idx.work⟩

@[simp] theorem rep_value (l : Lists a toSite s) (h : StoredLookup.SelectedGroups a toSite s) :
    (rep l h).value = ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).representative h).2 := by
  apply Fin.ext
  change (cut l h.1 h.2.succ).value-1 = _
  rw [cut_value]
  rfl

theorem cut_width (a : Input) (valid : a.Valid) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (j : Fin a.targets)
    (i : Fin ((Sparse.partition (G := grid a.game) a.game toSite s j).groups+1)) :
    ((Sparse.partition (G := grid a.game) a.game toSite s j).cut i).size ≤ indexWidth (Binary.lengthInput a) := by
  let D := Sparse.partition (G := grid a.game) a.game toSite s j
  have upper : D.cut i ≤ grid a.game := (D.increasing.monotone (Fin.le_last i)).trans_eq D.last
  exact (Nat.size_le_size upper).trans ((Binary.grid_size a valid).trans (by unfold indexWidth; omega))

theorem groupSize_work (l : Lists a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (h : StoredLookup.SelectedGroups a toSite s) :
    let L := Binary.lengthInput a
    (groupSize l h).Bound (2*(recordLimit L+2)+1) (indexWidth L) := by
  let L := Binary.lengthInput a
  have lo := cut_work l hs h.1 h.2.castSucc
  have hi := cut_work l hs h.1 h.2.succ
  have A := cut_width a valid toSite s h.1 h.2.castSucc
  have B := cut_width a valid toSite s h.1 h.2.succ
  have out := bound_bind lo (f := fun low => do let high ← cut l h.1 h.2.succ; natSub high low)
    (bound_bind hi (show (natSub (cut l h.1 h.2.succ).value (cut l h.1 h.2.castSucc).value).Bound 1 (indexWidth L) by
      rw [cut_value,cut_value]; exact ⟨le_rfl,max_le B A⟩))
  exact out.weaken (by omega) le_rfl

theorem rep_work (l : Lists a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (h : StoredLookup.SelectedGroups a toSite s) :
    let L := Binary.lengthInput a
    (rep l h).Bound (recordLimit L+3) (indexWidth L) := by
  have t := cut_work l hs h.1 h.2.succ
  have one : (1:ℕ).size ≤ indexWidth (Binary.lengthInput a) := by change 1 ≤ _; unfold indexWidth; omega
  refine ⟨Nat.succ_le_succ t.1,max_le t.2 ?_⟩
  change max (cut l h.1 h.2.succ).value.size 1 ≤ _
  rw [cut_value]
  exact max_le (cut_width a valid toSite s ..) one

end Kintali.QuotaSweep.SelectedBuilder
