module

public import Kintali.ContactComparison
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith

/-!
# Choices in the finite restricted market (Kintali, §2, Lemma 3)

An ordinary bid is indexed by `E`. The other two record types are outside
balances and vacancies. The input list gives a reproducible order for scans.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.QuotaSweep

abbrev Vertex (B S : Type*) := B ⊕ S
abbrev Record (B S E : Type*) := E ⊕ (B ⊕ S)

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]

abbrev bid (e : E) : Record B S E := .inl e
abbrev outside (b : B) : Record B S E := .inr (.inl b)
abbrev vacancy (s : S) : Record B S E := .inr (.inr s)

/-- The ordinal market together with its buyer and site indices. Its record
list can contain precisely the grouped private bids retained in the book. -/
structure Book (B S E : Type*) [DecidableEq B] [DecidableEq S] [DecidableEq E] where
  market : Market (Vertex B S) (Record B S E)
  buyer : E → B
  site : E → S
  ends_bid : ∀ e, market.ends (bid e) = {.inl (buyer e), .inr (site e)}
  ends_outside : ∀ b, market.ends (outside b) = {.inl b}
  ends_vacancy : ∀ s, market.ends (vacancy s) = {.inr s}
  records : List (Record B S E)
  complete : ∀ e, e ∈ records
  retained : Finset E

namespace Book

variable (K : Book B S E)

/-- The ordinary bids admitted by this restriction. -/
def retainedRecords : Finset (Record B S E) :=
  K.retained.map ⟨bid, Sum.inl_injective⟩

@[simp] theorem mem_retainedRecords {e : E} :
    bid e ∈ K.retainedRecords ↔ e ∈ K.retained := by
  simp [retainedRecords]

@[simp] theorem buyer_mem_bid (b : B) (e : E) :
    Sum.inl b ∈ K.market.ends (bid e) ↔ b = K.buyer e := by simp [K.ends_bid]

@[simp] theorem site_mem_bid (s : S) (e : E) :
    Sum.inr s ∈ K.market.ends (bid e) ↔ s = K.site e := by simp [K.ends_bid]

@[simp] theorem bid_degree (e : E) : (K.market.ends (bid e)).card = 2 := by
  simp [K.ends_bid]

/-- Executable strict acceptance test, including an outside balance. -/
def accepts (x : Record B S E → ℚ) (v : Vertex B S) (e : Record B S E) : Bool :=
  K.records.any fun f => decide (v ∈ K.market.ends f ∧ K.market.rank v e < K.market.rank v f ∧
    0 < x f)

@[simp] theorem accepts_iff {x : Record B S E → ℚ} {v : Vertex B S} {e : Record B S E} :
    K.accepts x v e = true ↔ K.market.Accepts x v e := by
  simp [accepts, Market.Accepts, K.complete]

def holdings (x : Record B S E → ℚ) (b : B) : List (Record B S E) :=
  K.records.filter fun e => decide (.inl b ∈ K.market.ends e ∧ 0 < x e)

@[simp] theorem mem_holdings {x : Record B S E → ℚ} {b : B} {e : Record B S E} :
    e ∈ K.holdings x b ↔ Sum.inl b ∈ K.market.ends e ∧ 0 < x e := by
  simp [holdings, K.complete]

/-- A buyer releases its worst positive record. The fallback covers a buyer
of mass zero, which the short paper removes before running the sweep. -/
def worst (x : Record B S E → ℚ) (b : B) : Record B S E :=
  ((K.holdings x b).argmax (K.market.rank (.inl b))).getD (outside b)

def offers (x : Record B S E → ℚ) (s : S) : List (Record B S E) :=
  K.records.filter fun r => match r with
    | .inl e => decide (e ∈ K.retained ∧ K.site e = s) && K.accepts x (.inl (K.buyer e)) (bid e)
    | .inr _ => false

@[simp] theorem bid_mem_offers {x : Record B S E → ℚ} {s : S} {e : E} :
    bid e ∈ K.offers x s ↔ e ∈ K.retained ∧ K.site e = s ∧
      K.market.Accepts x (.inl (K.buyer e)) (bid e) := by
  simp [offers, K.complete, and_assoc]

@[simp] theorem slack_not_mem_offers (x : Record B S E → ℚ) (s : S) (v : Vertex B S) :
    Sum.inr v ∉ K.offers x s := by simp [offers]

/-- A site increases its best buyer-accepted ordinary bid, or its vacancy. -/
def proposal (x : Record B S E → ℚ) (s : S) : Record B S E :=
  ((K.offers x s).argmin (K.market.rank (.inr s))).getD (vacancy s)

theorem worst_mem {x : Record B S E → ℚ} {b : B} {e : Record B S E}
    (he : e ∈ K.holdings x b) : K.worst x b ∈ K.holdings x b := by
  unfold worst
  cases h : (K.holdings x b).argmax (K.market.rank (.inl b)) with
  | none => simp [List.argmax_eq_none.mp h] at he
  | some f => exact List.argmax_mem (m := f) (Option.mem_def.mpr h)

theorem worst_rank {x : Record B S E → ℚ} {b : B} {e : Record B S E}
    (he : e ∈ K.holdings x b) :
    K.market.rank (.inl b) e ≤ K.market.rank (.inl b) (K.worst x b) := by
  unfold worst
  cases h : (K.holdings x b).argmax (K.market.rank (.inl b)) with
  | none => simp [List.argmax_eq_none.mp h] at he
  | some f => exact List.le_of_mem_argmax he (Option.mem_def.mpr h)

theorem worst_incident (x : Record B S E → ℚ) (b : B) :
    Sum.inl b ∈ K.market.ends (K.worst x b) := by
  unfold worst
  cases h : (K.holdings x b).argmax (K.market.rank (.inl b)) with
  | none => simp [K.ends_outside]
  | some f => exact (K.mem_holdings.mp (List.argmax_mem (Option.mem_def.mpr h))).1

theorem rejects_worst (x : Record B S E → ℚ) (b : B) :
    ¬K.market.Accepts x (.inl b) (K.worst x b) := by
  rintro ⟨e, hinc, hlt, hpos⟩
  exact (K.worst_rank (K.mem_holdings.mpr ⟨hinc, hpos⟩)).not_gt hlt

theorem proposal_cases (x : Record B S E → ℚ) (s : S) :
    K.proposal x s ∈ K.offers x s ∨ K.proposal x s = vacancy s := by
  unfold proposal
  cases h : (K.offers x s).argmin (K.market.rank (.inr s)) with
  | none => exact Or.inr rfl
  | some f => exact Or.inl (List.argmin_mem (Option.mem_def.mpr h))

theorem proposal_rank {x : Record B S E → ℚ} {s : S} {e : Record B S E}
    (he : e ∈ K.offers x s) :
    K.market.rank (.inr s) (K.proposal x s) ≤ K.market.rank (.inr s) e := by
  unfold proposal
  cases h : (K.offers x s).argmin (K.market.rank (.inr s)) with
  | none => simp [List.argmin_eq_none.mp h] at he
  | some f => exact List.le_of_mem_argmin he (Option.mem_def.mpr h)

theorem proposal_bid {x : Record B S E → ℚ} {s : S} {e : E}
    (h : K.proposal x s = bid e) :
    e ∈ K.retained ∧ K.site e = s ∧ K.market.Accepts x (.inl (K.buyer e)) (bid e) := by
  rcases K.proposal_cases x s with hoff | hvac
  · apply K.bid_mem_offers.mp
    simpa [h] using hoff
  · simp [h] at hvac

theorem proposal_incident (x : Record B S E → ℚ) (s : S) :
    Sum.inr s ∈ K.market.ends (K.proposal x s) := by
  rcases K.proposal_cases x s with hoff | hvac
  · cases h : K.proposal x s with
    | inl e =>
      have he := K.proposal_bid h
      exact (K.site_mem_bid s e).mpr he.2.1.symm
    | inr v => exact False.elim (K.slack_not_mem_offers x s v (h ▸ hoff))
  · simp [hvac, K.ends_vacancy]

end Book
end Kintali.QuotaSweep
