module

public import Kintali.QuotaSweep.WorkFrame
import Mathlib.Tactic.Linarith

/-! # Counted execution of the finite restricted contact search -/

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E) [Fintype B] [Fintype S]

def measuredStage (unit : ℕ) (P : Parameters B S) (z : Stored B S E) : (Stored B S E × Bool) × ℕ :=
  let f := K.frame unit P z
  let finish := K.applyFrame f.1 z f.1.duration
  let outside := outsideRead P.privateBuyers finish.1.entries
  let firstCharge := f.2+finish.2+outside.2+2
  if outside.1 ≤ P.target then
    let start := outsideRead P.privateBuyers z.entries
    let slope := outsideRead P.privateBuyers f.1.slopes
    let δ := (P.target-start.1)/slope.1
    let stop := K.applyFrame f.1 z δ
    ((stop.1,true),firstCharge+start.2+slope.2+stop.2+3)
  else ((finish.1,decide (P.upper ≤ finish.1.pressure)),firstCharge+1)

private def mathematicalStage (P : Parameters B S) (z : State B S E) : State B S E × Bool :=
  let finish := K.segment P z (K.duration z.allocation P.rate z.pressure P.upper)
  if privateOutside P.privateBuyers finish.allocation ≤ P.target then
    (K.segment P z (K.budgetTime P z),true)
  else (finish,decide (P.upper ≤ finish.pressure))

private theorem stage_value (unit : ℕ) (P : Parameters B S) (z : Stored B S E) :
    ((K.measuredStage unit P z).1.1.view,(K.measuredStage unit P z).1.2) =
      K.mathematicalStage P z.view := by
  let f := (K.frame unit P z).1
  let finish := (K.applyFrame f z f.duration).1
  let endpoint := K.segment P z.view (K.duration z.view.allocation P.rate z.pressure P.upper)
  have he : finish.view = endpoint := (K.applyFrame_value unit P z f.duration).trans
    (congrArg (K.segment P z.view) (K.frame_time unit P z))
  have hout : (outsideRead P.privateBuyers finish.entries).1 = privateOutside P.privateBuyers endpoint.allocation :=
    (outsideRead_value P.privateBuyers finish).trans (congrArg _ (congrArg State.allocation he))
  have hbudget : (P.target-(outsideRead P.privateBuyers z.entries).1)/
      (outsideRead P.privateBuyers f.slopes).1 = K.budgetTime P z.view := by
    rw [outsideRead_value,show f = _ from rfl,K.outsideRead_slope]; rfl
  let cross := (K.applyFrame f z (K.budgetTime P z.view)).1
  have hcross : cross.view = K.segment P z.view (K.budgetTime P z.view) := K.applyFrame_value ..
  have hp : finish.pressure = endpoint.pressure := congrArg State.pressure he
  unfold measuredStage mathematicalStage
  dsimp only
  change ((if (outsideRead P.privateBuyers finish.entries).1 ≤ P.target then _ else _ : (Stored B S E × Bool) × ℕ).1.1.view,
    (if (outsideRead P.privateBuyers finish.entries).1 ≤ P.target then _ else _ : (Stored B S E × Bool) × ℕ).1.2) =
    (if privateOutside P.privateBuyers endpoint.allocation ≤ P.target then _ else _)
  rw [hout]
  split <;> rename_i h
  · change ((K.applyFrame f z ((P.target-(outsideRead P.privateBuyers z.entries).1)/
      (outsideRead P.privateBuyers f.slopes).1)).1.view,true) = _
    rw [hbudget]
    exact congrArg (fun s => (s,true)) hcross
  · change (finish.view,decide (P.upper ≤ finish.pressure)) = (endpoint,decide (P.upper ≤ endpoint.pressure))
    rw [he,hp]

def stageLimit (n r u : ℕ) :=
  frameLimit n r u + 2*(r*(r+r+3)+2) + 3*(n*(r+2))+5

theorem measuredStage_work (unit : ℕ) (P : Parameters B S) (z : Stored B S E)
    (hlen : z.entries.length ≤ K.records.length) (hu : K.records.length ≤ unit) :
    (K.measuredStage unit P z).2 ≤ stageLimit (Fintype.card (Vertex B S)) K.records.length unit := by
  let f := (K.frame unit P z).1
  let finish := (K.applyFrame f z f.duration).1
  let n := Fintype.card (Vertex B S)
  let r := K.records.length
  have hf := K.frame_work unit P z (hlen.trans hu)
  have hfl : f.slopes.length = r := K.frame_length ..
  have hinc (δ : ℚ) : (K.applyFrame f z δ).2 ≤ r*(r+r+3)+2 := by
    apply (K.applyFrame_work f z δ).trans
    rw [hfl]; gcongr
  have hpc : P.privateBuyers.card ≤ n :=
    (Finset.card_le_univ _).trans (by simp [n])
  have hout (l : List (Record B S E × ℚ)) (hl : l.length ≤ r) :
      (outsideRead P.privateBuyers l).2 ≤ n*(r+2) :=
    (outsideRead_work ..).trans (Nat.mul_le_mul hpc (Nat.add_le_add_right hl 2))
  have he := hout finish.entries (K.applyFrame_length f z f.duration).le
  have hs := hout z.entries hlen
  have hd := hout f.slopes hfl.le
  let δ := (P.target-(outsideRead P.privateBuyers z.entries).1)/(outsideRead P.privateBuyers f.slopes).1
  have hi := hinc f.duration
  have hj := hinc δ
  change (if (outsideRead P.privateBuyers finish.entries).1 ≤ P.target then _ else _ : (Stored B S E × Bool) × ℕ).2 ≤ stageLimit n r unit
  by_cases h : (outsideRead P.privateBuyers finish.entries).1 ≤ P.target
  · rw [ite_eq_left h]
    change (K.frame unit P z).2+(K.applyFrame f z f.duration).2+(outsideRead P.privateBuyers finish.entries).2+2+
      (outsideRead P.privateBuyers z.entries).2+(outsideRead P.privateBuyers f.slopes).2+
      (K.applyFrame f z δ).2+3 ≤ _
    change (K.frame unit P z).2 ≤ frameLimit n r unit at hf
    unfold stageLimit
    omega
  · rw [ite_eq_right h]
    change (K.frame unit P z).2+(K.applyFrame f z f.duration).2+(outsideRead P.privateBuyers finish.entries).2+2+1 ≤ _
    change (K.frame unit P z).2 ≤ frameLimit n r unit at hf
    unfold stageLimit
    omega

theorem measuredStage_length (unit : ℕ) (P : Parameters B S) (z : Stored B S E) :
    (K.measuredStage unit P z).1.1.entries.length = K.records.length := by
  dsimp [measuredStage]
  split <;> apply K.applyFrame_length

/-- The counter is an accumulator so the transition to the next materialized
state is a tail call. The contact search keeps one record table across stages. -/
def countedRun (unit : ℕ) (P : Parameters B S) : ℕ → Stored B S E → ℕ → Stored B S E × ℕ
  | 0,z,charge => (z,charge)
  | fuel+1,z,charge =>
    let h := K.measuredStage unit P z
    let total := charge+h.2+1
    if h.1.2 then (h.1.1,total)
    else countedRun unit P fuel h.1.1 total

private theorem math_succ (P : Parameters B S) (n : ℕ) (z : State B S E) :
    K.run P (n+1) z = if (K.mathematicalStage P z).2 then (K.mathematicalStage P z).1
      else K.run P n (K.mathematicalStage P z).1 := by
  rw [run]
  unfold mathematicalStage
  dsimp only
  split <;> simp_all

theorem countedRun_value (unit : ℕ) (P : Parameters B S) (n : ℕ) (z : Stored B S E) (c : ℕ) :
    (K.countedRun unit P n z c).1.view = K.run P n z.view := by
  induction n generalizing z c with
  | zero => rfl
  | succ n ih =>
    let h := K.measuredStage unit P z
    have hval : (h.1.1.view,h.1.2) = K.mathematicalStage P z.view := K.stage_value unit P z
    have hstate := congrArg Prod.fst hval
    have hstop := congrArg Prod.snd hval
    rw [K.math_succ]
    change (if h.1.2 then _ else K.countedRun unit P n h.1.1 (c+h.2+1)).1.view = _
    by_cases hb : h.1.2 = true
    · have hright : (K.mathematicalStage P z.view).2 = true := hstop.symm.trans hb
      simpa only [hb,hright,↓reduceIte] using hstate
    · have hright : (K.mathematicalStage P z.view).2 ≠ true := fun h => hb (hstop.trans h)
      simp only [ite_eq_right hb,ite_eq_right hright]
      exact (ih _ _).trans (congrArg (K.run P n) hstate)

theorem countedRun_work (unit : ℕ) (P : Parameters B S) (n : ℕ) (z : Stored B S E) (c : ℕ)
    (hz : z.entries.length ≤ K.records.length) (hu : K.records.length ≤ unit) :
    (K.countedRun unit P n z c).2 ≤ c+n*(stageLimit (Fintype.card (Vertex B S)) K.records.length unit+1) := by
  induction n generalizing z c with
  | zero => simp [countedRun]
  | succ n ih =>
    let h := K.measuredStage unit P z
    let L := stageLimit (Fintype.card (Vertex B S)) K.records.length unit+1
    have hstage : h.2+1 ≤ L := Nat.succ_le_succ (K.measuredStage_work unit P z hz hu)
    change (if h.1.2 then _ else K.countedRun unit P n h.1.1 (c+h.2+1)).2 ≤ c+(n+1)*L
    by_cases hb : h.1.2 = true
    · rw [ite_eq_left hb,Nat.add_mul,Nat.one_mul]
      change c+h.2+1 ≤ _
      omega
    · rw [ite_eq_right hb,Nat.add_mul,Nat.one_mul]
      apply (ih h.1.1 (c+h.2+1) (K.measuredStage_length unit P z).le).trans
      change c+h.2+1+n*L ≤ _
      omega

def storedInitial (mass : B → ℚ) : Stored B S E := ⟨0,(Work.tabulate (fun e => (initial mass e,0)) K.records).1⟩

omit [Fintype B] [Fintype S] in
theorem storedInitial_value (mass : B → ℚ) : (K.storedInitial mass).view = ⟨0,initial mass⟩ := by
  unfold Stored.view
  congr 1
  funext e
  exact Work.read_tabulate (fun r => (initial mass r,0)) K.records 0 (K.complete e)

/-- A caller can use any upper charge for its book primitives. The contact
result is independent of this parameter and agrees with the paper-order run. -/
def contactWork (P : Parameters B S) [Fintype E] (oracleCharge : ℕ) : Stored B S E × ℕ :=
  let r := K.records.length
  K.countedRun (r+oracleCharge+1) P (Fintype.card (Record B S E)+1)
    (K.storedInitial P.mass) (r*(oracleCharge+2))

theorem contactWork_value (P : Parameters B S) [Fintype E] (u : ℕ) :
    (K.contactWork P u).1.view = K.firstContact P := by
  simp [contactWork,K.countedRun_value,K.storedInitial_value,firstContact]

theorem contactWork_bound (P : Parameters B S) [Fintype E] (u : ℕ) :
    let r := K.records.length
    (K.contactWork P u).2 ≤ r*(u+2) + (Fintype.card (Record B S E)+1)*
      (stageLimit (Fintype.card (Vertex B S)) r (r+u+1)+1) :=
  K.countedRun_work _ _ _ _ _ (by simp [storedInitial]) (by omega)

theorem countedRun_length (unit : ℕ) (P : Parameters B S) (n : ℕ) (z : Stored B S E) (c : ℕ)
    (hz : z.entries.length = K.records.length) :
    (K.countedRun unit P n z c).1.entries.length = K.records.length := by
  induction n generalizing z c with
  | zero => exact hz
  | succ n ih =>
    let h := K.measuredStage unit P z
    have hs : h.1.1.entries.length = K.records.length := K.measuredStage_length ..
    change (if h.1.2 then _ else K.countedRun unit P n h.1.1 (c+h.2+1)).1.entries.length = _
    by_cases hb : h.1.2 = true
    · rw [ite_eq_left hb]; exact hs
    · rw [ite_eq_right hb]; exact ih _ _ hs

theorem contactWork_length (P : Parameters B S) [Fintype E] (u : ℕ) :
    (K.contactWork P u).1.entries.length = K.records.length :=
  K.countedRun_length _ _ _ _ _ (by simp [storedInitial])

end Kintali.QuotaSweep.Book
