module

public import Kintali.QuotaSweep.ScanWork
import Mathlib.Tactic.Linarith

/-! # Work of worst-record and eligible-proposal selection -/

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E] (K : Book B S E)

def acceptLimit (records unit : ℕ) := records*(4*unit+4)
def comparisonCharge (unit : ℕ) := 2*unit+1
def choiceLimit (records unit : ℕ) :=
  records*(3*unit+4+acceptLimit records unit) + records*(comparisonCharge unit+1)+2

/-- `unit` bounds a rank query, an endpoint/retention test, or a lookup
of the current holding. The acceptance scan stops on its first witness. -/
def measuredAccept (unit : ℕ) (x : Record B S E → ℚ × ℕ) (v : Vertex B S) (e : Record B S E) :
    Bool × ℕ :=
  let result := Work.find (fun f =>
    let q := x f
    (decide (v ∈ K.market.ends f ∧ K.market.rank v e < K.market.rank v f ∧ 0 < q.1),
      3*unit+q.2+3)) K.records
  (result.1.isSome, result.2)

theorem measuredAccept_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (v : Vertex B S)
    (e : Record B S E) :
    (K.measuredAccept unit x v e).1 = K.accepts (fun r => (x r).1) v e := by
  simp [measuredAccept, Work.find_value, accepts, List.isSome_find?]

theorem measuredAccept_work (unit : ℕ) (x : Record B S E → ℚ × ℕ) (hx : ∀ r, (x r).2 ≤ unit)
    (v : Vertex B S) (e : Record B S E) :
    (K.measuredAccept unit x v e).2 ≤ acceptLimit K.records.length unit := by
  apply Work.find_work _ (4*unit+3)
  intro f
  dsimp
  grind

def measuredWorst (unit : ℕ) (x : Record B S E → ℚ × ℕ) (b : B) : Record B S E × ℕ :=
  let keep := Work.select (fun e =>
    let q := x e
    (decide (Sum.inl b ∈ K.market.ends e ∧ 0 < q.1),unit+q.2+1)) K.records
  let best := Work.extremum (fun f e => K.market.rank (.inl b) e < K.market.rank (.inl b) f)
    (comparisonCharge unit) keep.1 none
  (best.1.getD (outside b),keep.2+best.2+1)

theorem measuredWorst_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (b : B) :
    (K.measuredWorst unit x b).1 = K.worst (fun r => (x r).1) b := by
  simp [measuredWorst, Work.select_value, Work.extremum_value, worst, holdings, List.argmax]

theorem measuredWorst_work (unit : ℕ) (x : Record B S E → ℚ × ℕ) (hx : ∀ r, (x r).2 ≤ unit)
    (b : B) : (K.measuredWorst unit x b).2 ≤ choiceLimit K.records.length unit := by
  let p := fun e => (decide (Sum.inl b ∈ K.market.ends e ∧ 0 < (x e).1),unit+(x e).2+1)
  have hp (e) : (p e).2 ≤ 2*unit+1 := by dsimp [p]; grind
  have hc := Work.select_work p _ hp K.records
  have hl : (Work.select p K.records).1.length ≤ K.records.length := by
    rw [Work.select_value]; exact List.length_filter_le ..
  let rel := fun f e => K.market.rank (.inl b) e < K.market.rank (.inl b) f
  have he := (Work.extremum_work rel (comparisonCharge unit) (Work.select p K.records).1 none).trans
    (Nat.mul_le_mul_right _ hl)
  change (Work.select p K.records).2 + (Work.extremum rel (comparisonCharge unit) (Work.select p K.records).1 none).2 + 1 ≤ _
  have hs : K.records.length*(2*unit+1+1) ≤
      K.records.length*(3*unit+4+acceptLimit K.records.length unit) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold choiceLimit
  omega

def measuredOffer (unit : ℕ) (x : Record B S E → ℚ × ℕ) (s : S) : Record B S E → Bool × ℕ
  | .inl e =>
    if e ∈ K.retained ∧ K.site e = s then
      let h := K.measuredAccept unit x (.inl (K.buyer e)) (bid e)
      (h.1, 3*unit+3+h.2)
    else (false,2*unit+2)
  | .inr _ => (false,1)

def measuredProposal (unit : ℕ) (x : Record B S E → ℚ × ℕ) (s : S) : Record B S E × ℕ :=
  let keep := Work.select (K.measuredOffer unit x s) K.records
  let best := Work.extremum (fun f e => K.market.rank (.inr s) f < K.market.rank (.inr s) e)
    (comparisonCharge unit) keep.1 none
  (best.1.getD (vacancy s), keep.2+best.2+1)

theorem measuredProposal_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (s : S) :
    (K.measuredProposal unit x s).1 = K.proposal (fun r => (x r).1) s := by
  simp only [measuredProposal, Work.select_value, Work.extremum_value, proposal, offers, List.argmin]
  congr 3
  funext r
  cases r with
  | inl e =>
    by_cases he : e ∈ K.retained ∧ K.site e = s <;>
      simp [measuredOffer, he, measuredAccept_value]
  | inr v => rfl

theorem measuredProposal_work (unit : ℕ) (x : Record B S E → ℚ × ℕ) (hx : ∀ r, (x r).2 ≤ unit)
    (s : S) : (K.measuredProposal unit x s).2 ≤ choiceLimit K.records.length unit := by
  let p := K.measuredOffer unit x s
  have hp (e) : (p e).2 ≤ 3*unit+3+acceptLimit K.records.length unit := by
    rcases e with e | v
    · dsimp [p, measuredOffer]; split
      · exact Nat.add_le_add_left (K.measuredAccept_work unit x hx _ _) _
      · omega
    · dsimp [p, measuredOffer]; omega
  have hc := Work.select_work p _ hp K.records
  have hl : (Work.select p K.records).1.length ≤ K.records.length := by
    rw [Work.select_value]; exact List.length_filter_le ..
  let rel := fun f e => K.market.rank (.inr s) f < K.market.rank (.inr s) e
  have he := (Work.extremum_work rel (comparisonCharge unit) (Work.select p K.records).1 none).trans
    (Nat.mul_le_mul_right _ hl)
  change (Work.select p K.records).2 + (Work.extremum rel (comparisonCharge unit) (Work.select p K.records).1 none).2 + 1 ≤ _
  unfold choiceLimit
  have hc' : (Work.select p K.records).2 ≤
      K.records.length*(3*unit+4+acceptLimit K.records.length unit) := by
    exact hc.trans (Nat.mul_le_mul_left _ (by omega))
  omega

end Kintali.QuotaSweep.Book
