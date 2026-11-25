module

public import Kintali.QuotaSweep.Events
import Mathlib.Tactic.Linarith

/-!
# The initial allocation, private outside balances and the upper endpoint

At pressure zero all masses are outside. With increasing pressure every
outside balance is nonincreasing by the rejection-weight comparison.
At a site whose quota exceeds its possible purchases, positive vacancy
forces every private buyer there to purchase its sole retained bid.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

def initial (mass : B → ℚ) : Record B S E → ℚ
  | .inl _ => 0
  | .inr (.inl b) => mass b
  | .inr (.inr _) => 0

theorem initial_stable (rate : S → ℚ) {mass : B → ℚ} (hm : ∀ b, 0 ≤ mass b) :
    K.market.StableOn K.retainedRecords (quota rate mass 0) (initial mass) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (e | b | s) <;> simp [initial, hm]
  · rintro (b | s) <;>
      simp [Fintype.sum_sum_type, initial, K.ends_outside, quota]
  · rintro (e | b | s) he hpos
    · simp [initial] at hpos
    · change (K.market.ends (outside b)).card = 2 at he
      simp [K.ends_outside] at he
    · simp [initial] at hpos
  · intro r hr hb
    obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hr
    have hsite : Sum.inr (K.site e) ∈ K.market.ends (bid e) := by simp
    obtain ⟨f, hf, _, hp⟩ := hb.2 (.inr (K.site e)) hsite
    rcases f with f | b | s
    · simp [initial] at hp
    · change Sum.inr (K.site e) ∈ K.market.ends (outside b) at hf
      simp [K.ends_outside] at hf
    · simp [initial] at hp

/-- The budget variable is the sum of private outside balances. The paper's
target for it is `σ*r`, since total purchased private mass is `σ*(m₊-r)`. -/
def privateOutside (privateBuyers : Finset B) (x : Record B S E → ℚ) : ℚ :=
  ∑ b ∈ privateBuyers, x (outside b)

omit [Fintype E] in
theorem privateOutside_move (p : Finset B) (x : Record B S E → ℚ)
    (q : Vertex B S → ℚ) (δ : ℚ) :
    privateOutside p (K.move x q δ) = privateOutside p x +
      δ * privateOutside p (K.direction x q) := by
  simp [privateOutside, move, Finset.sum_add_distrib, Finset.mul_sum]

theorem outside_antitone {x y : Record B S E → ℚ} {rate : S → ℚ} {mass : B → ℚ}
    {t u : ℚ} (hr : ∀ s, 0 ≤ rate s) (htu : t ≤ u)
    (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x)
    (hy : K.market.StableOn K.retainedRecords (quota rate mass u) y) (b : B) :
    y (outside b) ≤ x (outside b) := by
  rw [quota_eq_pressureQuota] at hx hy
  let isSite : Vertex B S → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hside (e : Record B S E) (he : (K.market.ends e).card = 2) :
      (∑ v ∈ K.market.ends e, Market.side isSite v) = 0 := by
    rcases e with e | b | s
    · change (∑ v ∈ K.market.ends (bid e), Market.side isSite v) = 0
      simp [K.ends_bid, Market.side, isSite]
    · change (K.market.ends (outside b)).card = 2 at he
      simp [K.ends_outside] at he
    · change (K.market.ends (vacancy s)).card = 2 at he
      simp [K.ends_vacancy] at he
  have hinj (v : Vertex B S) : 0 ≤ injection rate v := by cases v <;> simp [injection, hr]
  have hout (b : B) (e : Record B S E) (he : e ∈ ({outside b} : Finset _)) :
      ∃ v, isSite v = false ∧ K.market.ends e = {v} := by
    obtain rfl := Finset.mem_singleton.mp he
    exact ⟨.inl b, rfl, K.ends_outside b⟩
  simpa [Market.coverage] using
    (Market.coverage_antitone hside hinj htu (by decide : (0 : ℚ) < 1) hout hy hx b)

theorem privateOutside_antitone {p : Finset B} {x y : Record B S E → ℚ}
    {rate : S → ℚ} {mass : B → ℚ} {t u : ℚ}
    (hr : ∀ s, 0 ≤ rate s) (htu : t ≤ u)
    (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x)
    (hy : K.market.StableOn K.retainedRecords (quota rate mass u) y) :
    privateOutside p y ≤ privateOutside p x :=
  Finset.sum_le_sum fun b _ => K.outside_antitone hr htu hx hy b

/-- Purchases of all ordinary bids at a site. -/
def sitePurchases (s : S) (x : Record B S E → ℚ) : ℚ :=
  ∑ e : E, if K.site e = s then x (bid e) else 0

theorem vacancy_balance {x : Record B S E → ℚ} {rate : S → ℚ} {mass : B → ℚ} {t : ℚ}
    (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x) (s : S) :
    K.sitePurchases s x + x (vacancy s) = rate s * t := by
  have h := hx.balance (.inr s)
  simpa [Fintype.sum_sum_type, sitePurchases, K.ends_bid, K.ends_outside, K.ends_vacancy,
    quota, eq_comm] using h

/-- Vacancy forces the outside balance of each buyer with a retained bid at
this site to vanish if that buyer would strictly prefer the bid to outside. -/
theorem private_filled_of_vacancy {x : Record B S E → ℚ} {q : Vertex B S → ℚ}
    (hx : K.market.StableOn K.retainedRecords q x) {e : E} (he : e ∈ K.retained)
    (hv : 0 < x (vacancy (K.site e))) : x (outside (K.buyer e)) = 0 := by
  apply le_antisymm _ (hx.nonneg _)
  by_contra! hp
  apply hx.stable (bid e) (K.mem_retainedRecords.mpr he)
  refine ⟨K.bid_degree e, ?_⟩
  intro v h
  simp only [K.ends_bid, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · refine ⟨outside (K.buyer e), by simp [K.ends_outside], ?_, hp⟩
    exact K.market.slack_last _ (by simp [K.ends_outside]) _ (by simp [K.ends_outside]) _
      (by simp) (by simp)
  · refine ⟨vacancy (K.site e), by simp [K.ends_vacancy], ?_, hv⟩
    exact K.market.slack_last _ (by simp [K.ends_vacancy]) _ (by simp [K.ends_vacancy]) _
      (by simp) (by simp)

theorem buyer_balance {x : Record B S E → ℚ} {rate : S → ℚ} {mass : B → ℚ} {t : ℚ}
    (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x) (b : B) :
    (∑ e : E, if K.buyer e = b then x (bid e) else 0) + x (outside b) = mass b := by
  have h := hx.balance (.inl b)
  simpa [Fintype.sum_sum_type, K.ends_bid, K.ends_outside, K.ends_vacancy, quota, eq_comm] using h

/-- Counting each bid in its buyer row bounds a site's purchases by the
combined masses of its incident buyers, including all private buyers there. -/
theorem sitePurchases_le_mass {x : Record B S E → ℚ} {rate : S → ℚ} {mass : B → ℚ} {t : ℚ}
    (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x) (s : S)
    (buyers : Finset B) (hin : ∀ e, K.site e = s → K.buyer e ∈ buyers) :
    K.sitePurchases s x ≤ ∑ b ∈ buyers, mass b := by
  have hsum : K.sitePurchases s x = ∑ b ∈ buyers, ∑ e : E,
      if K.buyer e = b then (if K.site e = s then x (bid e) else 0) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : K.site e = s
    · simp [he, hin e he]
    · simp [he]
  rw [hsum]
  apply Finset.sum_le_sum
  intro b _
  have hbound : (∑ e : E, if K.buyer e = b then
      (if K.site e = s then x (bid e) else 0) else 0) ≤
      ∑ e : E, if K.buyer e = b then x (bid e) else 0 := by
    apply Finset.sum_le_sum
    intro e _
    by_cases hb : K.buyer e = b <;> by_cases hs : K.site e = s <;> simp [hb, hs, hx.nonneg]
  exact hbound.trans ((le_add_of_nonneg_right (hx.nonneg (outside b))).trans_eq
    (K.buyer_balance hx b))

/-- A local purchase bound suffices at the upper pressure. In the paper
the real buyers total one and the private buyers at one site total σ. -/
theorem privateOutside_zero_of_excess {p : Finset B} {x : Record B S E → ℚ}
    {rate : S → ℚ} {mass : B → ℚ} {upper : ℚ}
    (hx : K.market.StableOn K.retainedRecords (quota rate mass upper) x)
    (hbid : ∀ b ∈ p, ∃ e ∈ K.retained, K.buyer e = b)
    (hexcess : ∀ s, K.sitePurchases s x < rate s * upper) : privateOutside p x = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨e, he, rfl⟩ := hbid b hb
  have hbal := K.vacancy_balance hx (K.site e)
  exact K.private_filled_of_vacancy hx he (by linarith [hexcess (K.site e)])

end Kintali.QuotaSweep.Book
