module

public import Kintali.QuotaSweep.BuilderBaseRank
public import Kintali.QuotaSweep.BuilderColumns

/-! # Admitted ordinary bids, active private buyers and stored book endpoints -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def subset {T : Type} (xs : List T) (unique : xs.Nodup) (keep : T → Run Bool) : Run (Finset T) :=
  let cells := TrialWork.ListBuild.retain keep xs
  let good : cells.value.Nodup := by rw [TrialWork.ListBuild.retain_value]; exact unique.filter _
  ⟨⟨cells.value,good⟩,cells.work.seq (StochasticGames.CompilerRun.Work.one 0)⟩

theorem mem_subset {T : Type} (xs : List T) (unique : xs.Nodup) (keep : T → Run Bool) (t : T) :
    t ∈ (subset xs unique keep).value ↔ t ∈ xs ∧ (keep t).value = true := by
  change t ∈ (TrialWork.ListBuild.retain keep xs).value ↔ _
  rw [TrialWork.ListBuild.retain_value,List.mem_filter]

theorem subset_work {T : Type} (xs : List T) (unique : xs.Nodup) (keep : T → Run Bool) {c w : ℕ}
    (ok : ∀ t, (keep t).Bound c w) : (subset xs unique keep).Bound (2+xs.length*(c+1)) w := by
  have h := TrialWork.ListBuild.retain_work keep xs (fun x _ => ok x)
  exact ⟨(Nat.add_le_add_right h.1 1).trans (by omega),max_le h.2 (Nat.zero_le _)⟩

def active (d : TrialWork.Fields a.types a.targets) (j : Fin a.targets) : Run Bool :=
  d.gain j >>= TrialWork.lt 0

@[simp] theorem active_value (d : TrialWork.Fields a.types a.targets) (j : Fin a.targets) :
    (active d j).value = decide (0 < d.game.gain j) := by simp [active,TrialWork.Fields.game]; rfl

def allow (d : TrialWork.Fields a.types a.targets) : Bids a toSite s → Run Bool
  | .inl _ => step 0 true
  | .inr h => active d h.1

def privateBuyer (d : TrialWork.Fields a.types a.targets) : Buyers a toSite s → Run Bool
  | .inl _ => step 0 false
  | .inr h => active d h.1

def admitted (d : TrialWork.Fields a.types a.targets) (o : Orders a toSite s) (ok : o.Valid) :=
  subset o.bids ok.bids_unique (allow d)

def privateBuyers (d : TrialWork.Fields a.types a.targets) (o : Orders a toSite s) (ok : o.Valid) :=
  subset o.buyers ok.buyers_unique (privateBuyer d)

theorem admitted_value (d : TrialWork.Fields a.types a.targets) (hd : d.game = a.game)
    (o : Orders a toSite s) (ok : o.Valid) :
    (admitted d o ok).value = (Sparse.book a.game Fin.val Fin.val
      ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored)).retained := by
  ext e
  rw [admitted,mem_subset,and_iff_right (ok.bids_complete e),Sparse.Layout.stored_eq]
  rcases e with i|h
  · simp [allow,Sparse.real_retained]
  · rw [Sparse.group_retained]
    simp [allow,hd]
    rfl

theorem privateBuyers_value (d : TrialWork.Fields a.types a.targets) (hd : d.game = a.game)
    (o : Orders a toSite s) (ok : o.Valid) :
    (privateBuyers d o ok).value = (Sparse.selectedParameters (G := grid a.game) a.game toSite s
      (privateScale a.game)).privateBuyers := by
  ext b
  rw [privateBuyers,mem_subset,and_iff_right (ok.buyers_complete b)]
  rcases b with i|h
  · simp [privateBuyer,Sparse.selectedParameters,BudgetContact.parameters,BudgetContact.privateSet]
  · simp [privateBuyer,hd,Sparse.selectedParameters,BudgetContact.parameters,BudgetContact.privateSet]
    rfl

def endpointLayout (lists : Lists a toSite s) (c : RankRun.Columns a toSite s) (correct : c.Correct) :
    Sparse.Layout (Fin a.types) (Fin a.targets) (grid a.game) (StoredLookup.SelectedReals a toSite s)
      (StoredLookup.SelectedGroups a toSite s) :=
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  { real := ⟨fun i => c.reals[i.val], fun _ _ e => l.real.injective ((correct.1 _).symm.trans (e.trans (correct.1 _)))⟩
    representative := ⟨fun h => (h.1,c.gap h),fun _ _ e =>
      l.representative.injective ((correct.2 _).symm.trans (e.trans (correct.2 _)))⟩
    size := fun h => (groupSize lists h).value }

theorem endpointLayout_eq (lists : Lists a toSite s) (c : RankRun.Columns a toSite s) (correct : c.Correct) :
    endpointLayout lists c correct = (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored := by
  rw [Sparse.Layout.mk.injEq]
  exact ⟨Function.Embedding.ext correct.1,Function.Embedding.ext correct.2,funext (fun h => by
    simp only [Sparse.Layout.stored_eq]; exact groupSize_value lists h)⟩

/-- The rank field of this book is replaced by the addressed rank matrix
before any proposal is evaluated. Its stored endpoint closures read the
real column and group coordinates directly. -/
def createBook (lists : Lists a toSite s) (d : TrialWork.Fields a.types a.targets)
    (n : ℕ) (gridEq : n = grid a.game)
    (c : RankRun.Columns a toSite s) (hc : c.Correct) (o : Orders a toSite s) (ho : o.Valid) :
    Run (Book (Buyers a toSite s) (Fin a.targets) (Bids a toSite s)) :=
  let l := endpointLayout lists c hc
  let mask := admitted d o ho
  let unique : o.records.Nodup := by rw [ho.records]; simp [Sparse.book]
  let total : ∀ e, e ∈ o.records := fun e => ho.records ▸ (Sparse.book a.game Fin.val Fin.val _).complete e
  let keys := c.makeAt n gridEq d
  let keyEq : ∀ v e, (keys v e).value = Expanded.key d.game Fin.val Fin.val (l.embedVertex v) (l.embedRecord e) := by
    intro v e
    simp only [keys,RankRun.Columns.makeAt_eq,RankRun.Columns.make,Run.bind_value,RankRun.keyAt_value,
      c.vertex_value hc,c.record_value hc,l,endpointLayout_eq]
  let b : Book (Buyers a toSite s) (Fin a.targets) (Bids a toSite s) :=
    { market := listMarket d.game Fin.val Fin.val l o.records unique total (fun v e => (keys v e).value) keyEq
      buyer := l.buyer,site := l.site,ends_bid := fun _ => rfl,ends_outside := fun _ => rfl,
      ends_vacancy := fun _ => rfl,records := o.records,
      complete := fun e => ho.records ▸ (Sparse.book a.game Fin.val Fin.val _).complete e
      retained := mask.value }
  ⟨b,mask.work.seq (StochasticGames.CompilerRun.Work.one 0)⟩

theorem createBook_value (lists : Lists a toSite s) (d : TrialWork.Fields a.types a.targets) (hd : d.game = a.game)
    (n : ℕ) (gridEq : n = grid a.game)
    (c : RankRun.Columns a toSite s) (hc : c.Correct) (o : Orders a toSite s) (ho : o.Valid) :
    (createBook lists d n gridEq c hc o ho).value =
      Sparse.book a.game Fin.val Fin.val ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored) := by
  have mask := admitted_value d hd o ho
  simp only [createBook,listMarket_eq,endpointLayout_eq,hd,ho.records,mask]
  rfl

theorem active_work (d : TrialWork.Fields a.types a.targets) {c w W : ℕ} (data : TrialWork.FieldBound d c w)
    (width : TrialWork.scalarWidth w ≤ W) (j : Fin a.targets) :
    (active d j).Bound (c+4) W :=
  bound_bind ((data.gain j).1.weaken le_rfl ((show w ≤ TrialWork.scalarWidth w by unfold TrialWork.scalarWidth; omega).trans width))
    ((TrialWork.lt_work (Fits.zero.mono data.positive) (data.gain j).2).weaken le_rfl width)

theorem admitted_work (d : TrialWork.Fields a.types a.targets) (o : Orders a toSite s) (ho : o.Valid)
    {c w W : ℕ} (data : TrialWork.FieldBound d c w) (width : TrialWork.scalarWidth w ≤ W) :
    (admitted d o ho).Bound (2+o.bids.length*(c+4+1)) W :=
  subset_work _ _ _ (fun e => by rcases e with t|h
                                 · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
                                 · exact active_work d data width h.1)

theorem privateBuyers_work (d : TrialWork.Fields a.types a.targets) (o : Orders a toSite s) (ho : o.Valid)
    {c w W : ℕ} (data : TrialWork.FieldBound d c w) (width : TrialWork.scalarWidth w ≤ W) :
    (privateBuyers d o ho).Bound (2+o.buyers.length*(c+4+1)) W :=
  subset_work _ _ _ (fun b => by rcases b with t|h
                                 · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
                                 · exact active_work d data width h.1)

end Kintali.QuotaSweep.SelectedBuilder
