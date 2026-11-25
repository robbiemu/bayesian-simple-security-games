module

public import Kintali.QuotaSweep.Preservation
public import Kintali.QuotaSweep.Routing
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Applying the cycle or pressure rate in the ordinal market

The signed record change is the difference between the rate on its site
proposal and the rate on its buyer's worst holding. No record can receive
both. Vertex conservation gives the new pressure quotas by summation.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E)

/-- The other endpoint of the record named by this vertex, with `none`
for an outside option or a vacancy. -/
def next (x : Record B S E → ℚ) : Vertex B S → Option (Vertex B S)
  | .inl b => match K.worst x b with
    | .inl e => some (.inr (K.site e))
    | .inr _ => none
  | .inr s => match K.proposal x s with
    | .inl e => some (.inl (K.buyer e))
    | .inr _ => none

theorem incoming_at_buyer (x : Record B S E → ℚ) (s : S) (b : B) :
    K.next x (.inr s) = some (.inl b) ↔ Sum.inl b ∈ K.market.ends (K.proposal x s) := by
  cases h : K.proposal x s with
  | inl e => simp [next, h, eq_comm]
  | inr v =>
    obtain hoff | hv := K.proposal_cases x s
    · exact False.elim (K.slack_not_mem_offers x s v (h ▸ hoff))
    · rw [hv] at h
      simp [next, hv, ← h, K.ends_vacancy]

theorem incoming_at_site (x : Record B S E → ℚ) (b : B) (s : S) :
    K.next x (.inl b) = some (.inr s) ↔ Sum.inr s ∈ K.market.ends (K.worst x b) := by
  cases h : K.worst x b with
  | inl e => simp [next, h, eq_comm]
  | inr v =>
    rcases v with c | t
    · simp [next, h, K.ends_outside]
    · have hi := K.worst_incident x b
      rw [h] at hi
      change Sum.inl b ∈ K.market.ends (vacancy t) at hi
      simp [K.ends_vacancy] at hi

@[simp] theorem no_buyer_to_buyer (x : Record B S E → ℚ) (b c : B) :
    K.next x (.inl b) ≠ some (.inl c) := by
  cases h : K.worst x b <;> simp [next, h]

@[simp] theorem no_site_to_site (x : Record B S E → ℚ) (s t : S) :
    K.next x (.inr s) ≠ some (.inr t) := by
  cases h : K.proposal x s <;> simp [next, h]

variable [Fintype B] [Fintype S] [Fintype E]

def received (x : Record B S E → ℚ) (q : Vertex B S → ℚ) (e : Record B S E) : ℚ :=
  ∑ s : S, if K.proposal x s = e then q (.inr s) else 0

def released (x : Record B S E → ℚ) (q : Vertex B S → ℚ) (e : Record B S E) : ℚ :=
  ∑ b : B, if K.worst x b = e then q (.inl b) else 0

def direction (x : Record B S E → ℚ) (q : Vertex B S → ℚ) (e : Record B S E) : ℚ :=
  K.received x q e - K.released x q e

def move (x : Record B S E → ℚ) (q : Vertex B S → ℚ) (δ : ℚ) (e : Record B S E) : ℚ :=
  x e + δ * K.direction x q e

omit [Fintype B] [Fintype E] in
theorem received_nonneg {x : Record B S E → ℚ} {q : Vertex B S → ℚ}
    (hq : ∀ v, 0 ≤ q v) (e : Record B S E) : 0 ≤ K.received x q e :=
  Finset.sum_nonneg fun _ _ => by split <;> simp_all

omit [Fintype S] [Fintype E] in
theorem released_nonneg {x : Record B S E → ℚ} {q : Vertex B S → ℚ}
    (hq : ∀ v, 0 ≤ q v) (e : Record B S E) : 0 ≤ K.released x q e :=
  Finset.sum_nonneg fun _ _ => by split <;> simp_all

omit [Fintype B] [Fintype E] in
theorem received_eq_zero_of_worst (x : Record B S E → ℚ) (q : Vertex B S → ℚ) (b : B) :
    K.received x q (K.worst x b) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  have hne : K.proposal x s ≠ K.worst x b := by
    intro heq
    have ha := K.buyer_accepts_proposal (heq.symm ▸ K.worst_incident x b)
    rw [heq] at ha
    exact K.rejects_worst x b ha
  simp [hne]

omit [Fintype S] [Fintype E] in
theorem released_worst (x : Record B S E → ℚ) (q : Vertex B S → ℚ) (b : B) :
    K.released x q (K.worst x b) = q (.inl b) := by
  unfold released
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hne
    have hrec : K.worst x c ≠ K.worst x b := fun h =>
      hne (K.incident_buyers_eq (h ▸ K.worst_incident x c) (K.worst_incident x b))
    simp [hrec]
  · simp

omit [Fintype E] in
@[simp] theorem move_worst (x : Record B S E → ℚ) (q : Vertex B S → ℚ) (δ : ℚ) (b : B) :
    K.move x q δ (K.worst x b) = x (K.worst x b) - δ * q (.inl b) := by
  simp [move, direction, K.received_eq_zero_of_worst, K.released_worst, sub_eq_add_neg]

omit [Fintype E] in
theorem move_nonneg {x : Record B S E → ℚ} {q : Vertex B S → ℚ} {δ : ℚ}
    (hx : ∀ e, 0 ≤ x e) (hq : ∀ v, 0 ≤ q v) (hδ : 0 ≤ δ)
    (hmax : ∀ b, δ * q (.inl b) ≤ x (K.worst x b)) (e : Record B S E) :
    0 ≤ K.move x q δ e := by
  by_cases he : ∃ b, K.worst x b = e
  · obtain ⟨b, rfl⟩ := he
    rw [K.move_worst]
    exact sub_nonneg.mpr (hmax b)
  · have hz : K.released x q e = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      simp [show K.worst x b ≠ e from fun h => he ⟨b, h⟩]
    simp only [move, direction, hz, sub_zero]
    exact add_nonneg (hx e) (mul_nonneg hδ (K.received_nonneg hq e))

omit [Fintype E] in
theorem move_purchases {x : Record B S E → ℚ} {q : Vertex B S → ℚ} {δ : ℚ}
    (hq : ∀ v, 0 ≤ q v) (hδ : 0 ≤ δ) : K.Purchases x (K.move x q δ) := by
  intro e hp
  by_cases he : ∃ s, K.proposal x s = e
  · exact Or.inr he
  · have hz : K.received x q e = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      simp [show K.proposal x s ≠ e from fun h => he ⟨s, h⟩]
    simp only [move, direction, hz, zero_sub, mul_neg, ← sub_eq_add_neg] at hp
    exact Or.inl (hp.trans_le (sub_le_self _ (mul_nonneg hδ (K.released_nonneg hq e))))

/-- Sum the quantities carried by a finite set of labelled arcs at an endpoint. -/
theorem sum_assign {A R : Type*} [Fintype A] [Fintype R] [DecidableEq R]
    (label : A → R) (q : A → ℚ) (P : R → Prop) [DecidablePred P] :
    (∑ e : R, if P e then ∑ a : A, (if label a = e then q a else 0) else 0) =
    ∑ a : A, if P (label a) then q a else 0 := by
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (label a)]
  · simp
  · intro e _ hne
    simp [Ne.symm hne]
  · simp

def injection (rate : S → ℚ) : Vertex B S → ℚ := Sum.elim (fun _ => 0) rate

def quota (rate : S → ℚ) (mass : B → ℚ) (t : ℚ) : Vertex B S → ℚ :=
  Sum.elim mass (fun s => rate s * t)

omit [DecidableEq B] [DecidableEq S] [Fintype B] [Fintype S] in
theorem quota_eq_pressureQuota (rate : S → ℚ) (mass : B → ℚ) (t : ℚ) :
    quota rate mass t = Market.pressureQuota (Sum.elim (fun _ => false) (fun _ => true))
      (injection rate) (Sum.elim mass (fun _ => 0)) t := by
  funext v
  cases v <;> rfl

theorem sum_direction {x : Record B S E → ℚ} {q : Vertex B S → ℚ} {rate : S → ℚ} {speed : ℚ}
    (hflow : ∀ v, q v = speed * injection rate v + Routing.incoming (K.next x) q v)
    (v : Vertex B S) :
    (∑ e, if v ∈ K.market.ends e then K.direction x q e else 0) = speed * injection rate v := by
  have splitSub (p : Prop) [Decidable p] (a b : ℚ) :
      (if p then a - b else 0) = (if p then a else 0) - (if p then b else 0) := by
    by_cases h : p <;> simp [h]
  simp only [direction, splitSub, Finset.sum_sub_distrib, received, released, sum_assign]
  rcases v with b | s
  · have hown (c : B) : Sum.inl b ∈ K.market.ends (K.worst x c) ↔ c = b :=
      ⟨fun h => K.incident_buyers_eq (K.worst_incident x c) h,
       by rintro rfl; exact K.worst_incident x c⟩
    simp_rw [← K.incoming_at_buyer, hown]
    have h := hflow (.inl b)
    simp [injection, Routing.incoming, Fintype.sum_sum_type] at h
    simp [injection, h]
  · have hown (t : S) : Sum.inr s ∈ K.market.ends (K.proposal x t) ↔ t = s :=
      ⟨fun h => K.incident_sites_eq (K.proposal_incident x t) h,
       by rintro rfl; exact K.proposal_incident x t⟩
    simp_rw [hown, ← K.incoming_at_site]
    have h := hflow (.inr s)
    simp [injection, Routing.incoming, Fintype.sum_sum_type] at h
    simp [injection, h]

/-- All balances, feasibility, support and stability hold at each point of
the affine step up to and including its first exhaustion. -/
theorem stable_move {x : Record B S E → ℚ} {q : Vertex B S → ℚ} {rate : S → ℚ}
    {mass : B → ℚ} {t δ speed : ℚ}
    (hx : K.market.StableOn K.retainedRecords (quota rate mass t) x)
    (hq : ∀ v, 0 ≤ q v) (hδ : 0 ≤ δ)
    (hmax : ∀ b, δ * q (.inl b) ≤ x (K.worst x b))
    (hflow : ∀ v, q v = speed * injection rate v + Routing.incoming (K.next x) q v) :
    K.market.StableOn K.retainedRecords (quota rate mass (t + δ * speed)) (K.move x q δ) := by
  apply K.stable_of_purchases hx (K.move_nonneg hx.nonneg hq hδ hmax) _ (K.move_purchases hq hδ)
  intro v
  have splitMove (e : Record B S E) : (if v ∈ K.market.ends e then K.move x q δ e else 0) =
      (if v ∈ K.market.ends e then x e else 0) + δ *
        (if v ∈ K.market.ends e then K.direction x q e else 0) := by
    by_cases h : v ∈ K.market.ends e <;> simp [h, move]
  simp only [splitMove, Finset.sum_add_distrib, ← Finset.mul_sum, hx.balance, K.sum_direction hflow]
  cases v <;> simp [injection, quota]
  ring

end Kintali.QuotaSweep.Book
