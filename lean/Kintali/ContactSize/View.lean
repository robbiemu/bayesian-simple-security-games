module

public import Kintali.ContactSize.Parameters
public import Kintali.Solver
public import Kintali.TrialSize
import Kintali.QuotaSweep.SparseWork

/-! Polynomial sizes for the rational pressure, coverage and joint flows of
the sparse view used by the quote-search driver. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.ContactSize

open ExactRecovery MarketTrial InputOutput QuotaSweep QuoteSearch

def sampleLimit (L : ℕ) := 4*(L+L+L*L)

def recordLimit (L : ℕ) := 3*(L*L*(sampleLimit L+1))+4*L

def allocationWidth (L : ℕ) := stateWidth (recordLimit L) (parameterWidth L)

def viewWidth (L : ℕ) := 3+(recordLimit L+1)*(allocationWidth L+1)+scaleWidth L

/-- The bound holds for the retained list in every driver state, independent of its weights. -/
def SelectionBound (a : Input) (s : Selection (a.types*a.targets)) : Prop :=
  ∀ p : Fin (a.types*a.targets), s[p].length ≤ sampleLimit (Binary.lengthInput a)

theorem driver_selection (a : Input) (state : WeightTable (a.types*a.targets)) :
    SelectionBound a (select (4*witnessBound a.game) state) := by
  have dims := Binary.dimensions a
  have sites : a.game.positiveTargets.length ≤ a.targets := by
    simpa only [Game.positiveTargets, List.length_finRange] using
      (List.length_filter_le (fun j => decide (0<a.game.gain j)) (List.finRange a.targets))
  have bound : witnessBound a.game ≤ Binary.lengthInput a + Binary.lengthInput a +
      Binary.lengthInput a*Binary.lengthInput a :=
    Nat.add_le_add (Nat.add_le_add dims.2.1 (sites.trans dims.1))
      (Nat.mul_le_mul dims.2.1 (sites.trans dims.1))
  intro p
  simpa [select,sampleLimit] using (Runs.selected_count state[p] (4*witnessBound a.game)).trans
    ((Nat.sub_le ..).trans (Nat.mul_le_mul_left 4 bound))

theorem selected_inventory (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hSelect : SelectionBound a s) :
    let g := a.game
    let G := grid g
    let A := Fin (Sparse.realOrder (G := G) g toSite s).length
    let H := Sparse.IntervalGroup (Sparse.partition (G := G) g toSite s)
    let K := Sparse.book g Fin.val Fin.val (Sparse.selectedLayout (G := G) g toSite s)
    let r := recordLimit (Binary.lengthInput a)
    Fintype.card A ≤ r ∧ Fintype.card H ≤ r ∧
      Fintype.card (Sparse.R (Fin a.types) (Fin a.targets) A H) ≤ r ∧ K.records.length ≤ r := by
  let L := Binary.lengthInput a
  let G := grid a.game
  let A := Fin (Sparse.realOrder (G := G) a.game toSite s).length
  let H := Sparse.IntervalGroup (Sparse.partition (G := G) a.game toSite s)
  let U := L*L*(sampleLimit L+1)
  let N := Fintype.card (Sparse.R (Fin a.types) (Fin a.targets) A H)
  have dims := Binary.dimensions a
  have real := Sparse.realBids_count (G := G) a.game toSite s (Nat.succ_pos (sampleLimit L))
    (fun p => by simpa only [Nat.succ_sub_one] using hSelect p)
  have count : (Sparse.realBids (G := G) a.game toSite s).card ≤ U :=
    real.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul dims.2.1 dims.1))
  have ac : Fintype.card A = (Sparse.realBids (G := G) a.game toSite s).card := by
    simp only [A,Fintype.card_fin,Sparse.realOrder_length]
  have hc : Fintype.card H ≤ U+L :=
    (Sparse.groups_count (G := G) a.game toSite s).trans (Nat.add_le_add count dims.1)
  have ac' := ac.le.trans count
  have eq : N = Fintype.card A+Fintype.card H+(a.types+Fintype.card H)+a.targets := by
    simpa only [Fintype.card_fin] using
      (Sparse.record_count (I := Fin a.types) (J := Fin a.targets) (A := A) (H := H))
  have hdim : a.types ≤ L ∧ a.targets ≤ L := ⟨dims.2.1,dims.1⟩
  have fit : N ≤ 3*U+4*L := by omega
  have len : (Sparse.book a.game Fin.val Fin.val
      (Sparse.selectedLayout (G := G) a.game toSite s)).records.length = N := Sparse.records_length ..
  exact ⟨by change Fintype.card A ≤ 3*U+4*L; omega,
    by change Fintype.card H ≤ 3*U+4*L; omega,fit,len.le.trans fit⟩

theorem selected_state (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (hSelect : SelectionBound a s) :
    let z := Sparse.selectedContact (G := grid a.game) a.game toSite s (privateScale a.game)
    let b := allocationWidth (Binary.lengthInput a)
    Fits b z.pressure ∧ ∀ e, Fits b (z.allocation e) := by
  let g := a.game
  let G := grid g
  let σ := privateScale g
  let layout := Sparse.selectedLayout (G := G) g toSite s
  let K := Sparse.book g Fin.val Fin.val layout
  let P := Sparse.selectedParameters (G := G) g toSite s σ
  let z := Sparse.selectedContact (G := G) g toSite s σ
  have hσ : 0 < σ := sigma_pos g (contactTolerance_pos g)
  have hG : 0 < G := gridSize_pos g (contactTolerance g)
  have small (j) : g.gain j * σ < 1 :=
    (gain_sigma_le g (contactTolerance_pos g).le j).trans_lt (contactTolerance_lt_one g)
  obtain ⟨hs, hp, hu, _⟩ := Sparse.selectedContact_correct g toSite s
    ((Input.valid_iff a).mp valid).1 normal σ hσ hG small
  have zEq : z = K.firstContact P := Sparse.selectedContact_eq_firstContact ..
  have mass : P.mass = Sparse.mass g σ layout := by funext b; cases b <;> rfl
  have rate : P.rate = Expanded.siteRate g := by
    funext j; simp only [P,Sparse.selectedParameters,BudgetContact.parameters,BudgetContact.rate,
      Expanded.siteRate,one_div]
  have feasible : K.Feasible P (K.firstContact P) := by
    change K.market.StableOn K.retainedRecords (Book.quota P.rate P.mass _) _
    rw [← zEq,rate,mass]
    exact hs
  obtain ⟨_,_,count,len⟩ := selected_inventory a toSite s hSelect
  change Fits _ z.pressure ∧ ∀ e, Fits _ (z.allocation e)
  rw [zEq]
  exact contact_state K (parameters_fit a valid toSite s) len count feasible
    (zEq ▸ hp.le) (zEq ▸ hu.le)

structure ViewFits {k m G : ℕ} (w : ℕ) (v : ContactView k m G) : Prop where
  pressure : Fits w v.pressure
  coverage : ∀ j, Fits w (v.coverage j)
  joint : ∀ i j, Fits w (v.joint i j)

theorem sparse_view (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (s : Selection (a.types*a.targets)) (hSelect : SelectionBound a s) :
    ViewFits (viewWidth (Binary.lengthInput a)) (sparseView a.game valid.1 s) := by
  rw [sparseView_eq]
  let g := a.game
  let G := grid g
  let σ := privateScale g
  let L := Binary.lengthInput a
  let r := recordLimit L
  let b := allocationWidth L
  let toSite := redirect g valid.1
  let layout := Sparse.selectedLayout (G := G) g toSite s
  let z := Sparse.selectedContact (G := G) g toSite s σ
  obtain ⟨pres,alloc⟩ := selected_state a valid normal toSite s hSelect
  obtain ⟨ac,hc,_,_⟩ := selected_inventory a toSite s hSelect
  change Fintype.card (Fin (Sparse.realOrder (G := G) g toSite s).length) ≤ r at ac
  change Fintype.card (Sparse.IntervalGroup (Sparse.partition (G := G) g toSite s)) ≤ r at hc
  have zero : Fits b 0 := Fits.zero.mono pres.pos
  have widen : b ≤ viewWidth L := by
    change b ≤ 3+(r+1)*(b+1)+scaleWidth L
    rw [Nat.add_mul]; omega
  constructor
  · exact pres.mono widen
  · intro j
    change Fits _ (if 0 < g.gain j then Sparse.siteOutside layout z.allocation j/σ else 0)
    split
    · have total := Fits.sum Finset.univ (fun h =>
          if (layout.representative h).1 = j then z.allocation (outside (.inr h)) else 0)
          (w := b) (by intro h _; split <;> first | exact alloc _ | exact zero)
      simp only [Finset.card_univ] at total
      apply (total.div (scale_fits a valid)).mono
      change 1+_* (b+1)+scaleWidth L ≤ 3+(r+1)*(b+1)+scaleWidth L
      have h : Fintype.card (Sparse.IntervalGroup (Sparse.partition (G := G) g toSite s))*(b+1)
          ≤ (r+1)*(b+1) := Nat.mul_le_mul_right (b+1) (hc.trans (Nat.le_succ r))
      omega
    · exact zero.mono widen
  · intro i j
    change Fits _ (Sparse.attackJoint layout toSite z.allocation i j)
    unfold Sparse.attackJoint
    have total := Fits.sum Finset.univ (fun a =>
      if (layout.real a).1 = i ∧ (layout.real a).2.1 = j then z.allocation (bid (.inl a)) else 0)
      (w := b) (by intro a _; split <;> first | exact alloc _ | exact zero)
    have outsideFits : Fits b (if toSite i = j then z.allocation (outside (.inl i)) else 0) := by
      split <;> first | exact alloc _ | exact zero
    apply (total.add outsideFits).mono
    simp only [Finset.card_univ]
    change 1+_* (b+1)+b+1 ≤ 3+(r+1)*(b+1)+scaleWidth L
    have h := Nat.mul_le_mul_right (b+1) ac
    rw [Nat.add_mul]; omega

end Kintali.ContactSize
