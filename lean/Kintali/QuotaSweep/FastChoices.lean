module

public import Kintali.QuotaSweep.ChoiceWork
public import Kintali.QuotaSweep.GraphCycle
import Mathlib.Tactic.Linarith

/-! # Cache each buyer's worst held rank before testing site offers -/

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E)

theorem accepts_worst (x : Record B S E → ℚ) (b : B) (e : Record B S E) :
    K.market.Accepts x (.inl b) e ↔ 0 < x (K.worst x b) ∧
      K.market.rank (.inl b) e < K.market.rank (.inl b) (K.worst x b) := by
  constructor
  · rintro ⟨f,hi,better,positive⟩
    have h := K.mem_holdings.mpr ⟨hi,positive⟩
    exact ⟨(K.mem_holdings.mp (K.worst_mem h)).2,better.trans_le (K.worst_rank h)⟩
  · rintro ⟨pos,better⟩
    exact ⟨_,K.worst_incident x b,better,pos⟩

abbrev Release (B S E : Type*) := Record B S E × Option ℕ

def releaseInfo (unit : ℕ) (x : Record B S E → ℚ × ℕ) (b : B) : Release B S E × ℕ :=
  let w := K.measuredWorst unit x b
  let h := x w.1
  ((w.1,if 0 < h.1 then some (K.market.rank (.inl b) w.1) else none),w.2+h.2+unit+2)

def releaseTable (unit : ℕ) (x : Record B S E → ℚ × ℕ) :=
  Work.tabulate (K.releaseInfo unit x) K.buyerOrder

def readRelease (table : List (B × Release B S E)) (b : B) :=
  Work.search b (outside b,none) table

theorem readRelease_table (unit : ℕ) (x : Record B S E → ℚ × ℕ) (b : B) :
    (readRelease (K.releaseTable unit x).1 b).1 = (K.releaseInfo unit x b).1 := by
  unfold readRelease releaseTable
  rw [Work.search_value,Work.tabulate_value,List.lookup_graph _ (K.mem_buyerOrder b)]
  rfl

def fastOffer (unit : ℕ) (table : List (B × Release B S E)) (s : S) :
    Record B S E → Bool × ℕ
  | .inl e =>
    if e ∈ K.retained ∧ K.site e = s then
      let b := K.buyer e
      let w := readRelease table b
      (w.1.2.any (fun n => decide (K.market.rank (.inl b) (bid e) < n)),w.2+4*unit+3)
    else (false,2*unit+2)
  | .inr _ => (false,1)

private theorem fastOffer_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (s : S) (e : E) :
    (K.fastOffer unit (K.releaseTable unit x).1 s (bid e)).1 =
      (decide (e ∈ K.retained ∧ K.site e = s) && K.accepts (fun r => (x r).1) (.inl (K.buyer e)) (bid e)) := by
  apply Bool.eq_iff_iff.mpr
  by_cases he : e ∈ K.retained ∧ K.site e = s
  · by_cases hp : 0 < (x (K.worst (fun r => (x r).1) (K.buyer e))).1 <;>
      simp [fastOffer,he,K.readRelease_table,releaseInfo,K.measuredWorst_value,K.accepts_worst,hp]
  · simp [fastOffer,he]


def fastProposal (unit : ℕ) (table : List (B × Release B S E)) (s : S) : Record B S E × ℕ :=
  let keep := Work.select (K.fastOffer unit table s) K.records
  let best := Work.extremum (fun f e => K.market.rank (.inr s) f < K.market.rank (.inr s) e)
    (comparisonCharge unit) keep.1 none
  (best.1.getD (vacancy s), keep.2+best.2+1)

theorem fastProposal_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (s : S) :
    (K.fastProposal unit (K.releaseTable unit x).1 s).1 = K.proposal (fun r => (x r).1) s := by
  simp only [fastProposal,Work.select_value,Work.extremum_value,proposal,offers,List.argmin]
  congr 3
  funext r
  rcases r with e | v
  · exact K.fastOffer_value ..
  · rfl

def proposalLimit (r u : ℕ) := r*(r+4*u+4)+r*(comparisonCharge u+1)+1

theorem fastProposal_work (unit : ℕ) (table : List (B × Release B S E))
    (hlen : table.length ≤ K.records.length) (s : S) :
    (K.fastProposal unit table s).2 ≤ proposalLimit K.records.length unit := by
  let p := K.fastOffer unit table s
  let r := K.records.length
  have hp (e) : (p e).2 ≤ r+4*unit+3 := by
    rcases e with e | v
    · have hr := (Work.search_work (K.buyer e) (outside (K.buyer e),none) table).trans hlen
      dsimp [p,fastOffer,readRelease]; split <;> omega
    · dsimp [p,fastOffer]; omega
  have hc := Work.select_work p _ hp K.records
  have hl : (Work.select p K.records).1.length ≤ r := by
    rw [Work.select_value]; exact List.length_filter_le ..
  let rel := fun f e => K.market.rank (.inr s) f < K.market.rank (.inr s) e
  have he := (Work.extremum_work rel (comparisonCharge unit) (Work.select p K.records).1 none).trans
    (Nat.mul_le_mul_right _ hl)
  exact Nat.add_le_add_right (Nat.add_le_add hc he) 1

def buyerTableLimit (r u : ℕ) := r*(choiceLimit r u+u+u+3)

theorem releaseTable_work (unit : ℕ) (x : Record B S E → ℚ × ℕ) (hx : ∀ r, (x r).2 ≤ unit)
    (hbuyers : K.buyerOrder.length ≤ K.records.length) :
    (K.releaseTable unit x).2 ≤ buyerTableLimit K.records.length unit := by
  apply (Work.tabulate_work _ (choiceLimit K.records.length unit+unit+unit+2) _ K.buyerOrder).trans
    (Nat.mul_le_mul_right _ hbuyers)
  intro b
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (K.measuredWorst_work unit x hx b) (hx _)) _) 2

end Kintali.QuotaSweep.Book
