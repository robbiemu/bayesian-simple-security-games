module

public import Kintali.TrialWork.Intervals
public import Kintali.QuotaSweep.StoredLookupRun
public import Kintali.QuotaSweep.ContactCharge

/-! The retained bids and per-site cut lists supplied by book preparation
also index the projected contact and the blocking queries. The only private
labels visited are the intervals between adjacent retained cuts. -/

@[expose] public section
namespace Kintali.TrialWork.Selected

open StochasticGames.CompilerRun StochasticGames.BinarySize ExactRecovery MarketTrial QuoteSearch
open QuotaSweep ContactSize InputOutput QuotaSweep.StoredLookup

variable (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))

structure Lists where
  bids : List (Sparse.ListedBid a.types a.targets (grid a.game))
  cuts : Vector (List ℕ) a.targets
  bidOrder : bids = Sparse.realOrder a.game toSite s
  cutOrder : ∀ j : Fin a.targets, cuts[j.val] = (Sparse.siteCuts (G := grid a.game) a.game toSite s j).sort

variable {a toSite s}

def number {n : ℕ} (r : Run ℕ) (eq : r.value = n) : Run (List (Fin n)) :=
  let ids := finRange r.value
  ⟨eq ▸ ids.value,r.work.seq ids.work⟩

@[simp] theorem number_value {n : ℕ} (r : Run ℕ) (eq : r.value = n) : (number r eq).value = List.finRange n := by
  subst n; simp [number]

theorem number_work {n c w : ℕ} (r : Run ℕ) (eq : r.value = n) (h : r.Bound c w) (idx : n.size ≤ w) :
    (number r eq).Bound (c+(2*n+1)) w := by
  subst n
  have rg := finRange_bound r.value
  exact ⟨Nat.add_le_add h.1 rg.1,max_le h.2 (rg.2.trans idx)⟩

namespace Lists

variable (l : Lists a toSite s)

def reals : Run (List (SelectedReals a toSite s)) :=
  number (length l.bids) ((length_value l.bids).trans (congrArg List.length l.bidOrder))

@[simp] theorem reals_value : l.reals.value = List.finRange (Sparse.realOrder (G := grid a.game) a.game toSite s).length :=
  number_value ..

def count (j : Fin a.targets) : Run ℕ := do
  let xs ← step a.targets.size l.cuts[j.val]
  let n ← length xs
  natSub n 1

@[simp] theorem count_value (j : Fin a.targets) :
    (l.count j).value = (Sparse.partition (G := grid a.game) a.game toSite s j).groups := by
  simp only [count,Run.bind_value,step_value,length_value,natSub,l.cutOrder]
  rfl

def groupRow (j : Fin a.targets) : Run (List (SelectedGroups a toSite s)) := do
  let ids ← number (l.count j) (l.count_value j)
  mapM (fun h => step 0 (Sigma.mk j h)) ids

@[simp] theorem groupRow_value (j : Fin a.targets) :
    (l.groupRow j).value =
      (List.finRange (Sparse.partition (G := grid a.game) a.game toSite s j).groups).map (Sigma.mk j) := by
  simp [groupRow]

def groups : Run (List (SelectedGroups a toSite s)) :=
  finRange a.targets >>= flatMapM l.groupRow

theorem groups_value : l.groups.value = (List.finRange a.targets).sigma
    (fun j => List.finRange (Sparse.partition (G := grid a.game) a.game toSite s j).groups) := by
  simp [groups,List.sigma]

theorem groups_unique : l.groups.value.Nodup := by
  rw [l.groups_value]
  exact (List.nodup_finRange _).sigma (fun _ => List.nodup_finRange _)

theorem groups_complete (p : SelectedGroups a toSite s) : p ∈ l.groups.value := by
  rw [l.groups_value]
  rcases p with ⟨j,h⟩
  simp [List.sigma]

theorem group_count (hs : SelectionBound a s) (j : Fin a.targets) :
    (Sparse.partition (G := grid a.game) a.game toSite s j).groups ≤ recordLimit (Binary.lengthInput a) := by
  let D := Sparse.partition (G := grid a.game) a.game toSite s
  have inj : Function.Injective (fun h : Fin (D j).groups => (⟨j,h⟩ : SelectedGroups a toSite s)) :=
    fun _ _ eq => eq_of_heq (Sigma.mk.inj eq).2
  exact (Fintype.card_fin _ ▸ Fintype.card_le_of_injective _ inj).trans (selected_inventory a toSite s hs).2.1

theorem bid_count (hs : SelectionBound a s) : l.bids.length ≤ recordLimit (Binary.lengthInput a) := by
  rw [l.bidOrder]
  simpa only [Fintype.card_fin] using (selected_inventory a toSite s hs).1

theorem groups_length (hs : SelectionBound a s) : l.groups.value.length ≤ recordLimit (Binary.lengthInput a) := by
  rw [← List.toFinset_card_of_nodup l.groups_unique]
  exact (Finset.card_le_univ _).trans (selected_inventory a toSite s hs).2.1

def labelsWidth (L : ℕ) := recordLimit L+L+3
def labelsSlots (L : ℕ) := 12+(L+1)*(8*(recordLimit L+2))+4*recordLimit L+2*L

theorem labels_work (hs : SelectionBound a s) :
    let L := Binary.lengthInput a
    (l.reals.work.seq l.groups.work).slots ≤ labelsSlots L ∧
    (l.reals.work.seq l.groups.work).width ≤ labelsWidth L := by
  let L := Binary.lengthInput a
  let R := recordLimit L
  let W := labelsWidth L
  have d : a.targets ≤ L := (Binary.dimensions a).1
  have mw : a.targets.size ≤ W := (size_le_self _).trans (by unfold W labelsWidth; omega)
  have rwid : R+2 ≤ W := by unfold W labelsWidth R; omega
  have wl : 1 ≤ W := by omega
  have real : l.bids.length ≤ R := l.bid_count hs
  have nr : (Sparse.realOrder (G := grid a.game) a.game toSite s).length ≤ R := by rwa [← l.bidOrder]
  have sizes (n : ℕ) (h : n ≤ R+2) : n.size ≤ W := (size_le_self _).trans (h.trans rwid)
  have re : l.reals.Bound ((R+1)+(2*R+1)) W := (number_work _ _ ((length_bound _).weaken
    (Nat.add_le_add_right real 1) (sizes _ (by omega)))
    (sizes _ (by omega))).weaken (by omega) le_rfl
  have gr (j : Fin a.targets) : (l.groupRow j).Bound (6*R+7) W := by
    let n := (Sparse.partition (G := grid a.game) a.game toSite s j).groups
    have hc : n ≤ R := group_count hs j
    have eq : l.cuts[j.val].length - 1 = n := by simpa [count,natSub] using l.count_value j
    have lim : l.cuts[j.val].length ≤ R+1 := by omega
    have cw : (l.count j).Bound (1+((R+2)+1)) W := by
      apply bound_bind ((bound_step _ _).weaken le_rfl mw)
      rw [step_value]
      apply bound_bind ((length_bound _).weaken (by omega) (sizes _ (by omega)))
      exact ⟨le_rfl,max_le (sizes _ (by simp; omega)) wl⟩
    have ids := number_work _ (l.count_value j) cw (sizes _ (by omega))
    have tags := mapM_bound (fun h : Fin n => step 0 (Sigma.mk j h : SelectedGroups a toSite s))
      (List.finRange n) 1 W (fun _ _ => (bound_step _ _).weaken le_rfl (Nat.zero_le _))
    simp only [List.length_finRange] at tags
    unfold groupRow
    apply Run.Bound.weaken (k := (1+(R+2+1)+(2*n+1))+(n*(1+2)+1)) (w := W) ?_ (by omega) le_rfl
    apply bound_bind ids
    rw [number_value]
    exact tags
  have tags := flatMapM_bound l.groupRow (List.finRange a.targets) (6*R+7) R W
    (fun j _ => gr j) (fun j _ => by simpa using (group_count (a := a) (toSite := toSite) hs j))
  simp only [List.length_finRange] at tags
  have all : l.groups.Bound (2*a.targets+1+(a.targets*(6*R+7+R+2)+1)) W := by
    apply bound_bind ((finRange_bound _).weaken le_rfl mw)
    rw [finRange_value]
    exact tags
  have mn := Nat.mul_le_mul d (show 6*R+7+R+2 ≤ 8*(R+2) by omega)
  have up : L*(8*(R+2)) ≤ (L+1)*(8*(R+2)) := Nat.mul_le_mul_right _ (Nat.le_succ _)
  constructor
  · change l.reals.work.slots+l.groups.work.slots ≤ _
    have := re.1; have := all.1
    unfold labelsSlots
    dsimp only [R,L] at *
    omega
  · exact max_le re.2 all.2

end Lists
end Kintali.TrialWork.Selected
