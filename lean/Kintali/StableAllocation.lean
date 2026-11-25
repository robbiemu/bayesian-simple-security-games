module

public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Fixed-quota invariance for ordinal transportation

This is the rejection-weight argument in Lemma 5 of Shiva Kintali,
*A polynomial time algorithm for computing exact equilibria in Bayesian simple security
games* (short version, November 24, 2026).
-/

open scoped BigOperators

@[expose] public section

namespace Kintali

/-- Ordinary records have two endpoints. Outside and vacancy records have one
endpoint and rank last there. Smaller ranks are preferred. -/
structure Market (Vertex Record : Type*) [DecidableEq Vertex] where
  ends : Record → Finset Vertex
  rank : Vertex → Record → ℕ
  degree : ∀ e, (ends e).card = 1 ∨ (ends e).card = 2
  rank_injective : ∀ v e f, v ∈ ends e → v ∈ ends f → rank v e = rank v f → e = f
  slack_last : ∀ e, (ends e).card = 1 → ∀ v ∈ ends e, ∀ f, v ∈ ends f →
    f ≠ e → rank v f < rank v e

namespace Market

variable {Vertex Record : Type*} [DecidableEq Vertex]
variable (M : Market Vertex Record)

/-- An incident endpoint accepts a bid when it holds some strictly worse record. -/
def Accepts (allocation : Record → ℚ) (v : Vertex) (e : Record) : Prop :=
  ∃ f, v ∈ M.ends f ∧ M.rank v e < M.rank v f ∧ 0 < allocation f

/-- Both endpoints of an ordinary record accept it. This also tests omitted bids. -/
def Blocks (allocation : Record → ℚ) (e : Record) : Prop :=
  (M.ends e).card = 2 ∧ ∀ v ∈ M.ends e, M.Accepts allocation v e

variable [Fintype Record]

/-- Stability on the retained ordinary bids. Slack records are always available. -/
structure StableOn (retained : Finset Record) (quota : Vertex → ℚ)
    (allocation : Record → ℚ) : Prop where
  nonneg : ∀ e, 0 ≤ allocation e
  balance : ∀ v, (∑ e, if v ∈ M.ends e then allocation e else 0) = quota v
  support : ∀ e, (M.ends e).card = 2 → 0 < allocation e → e ∈ retained
  stable : ∀ e ∈ retained, ¬M.Blocks allocation e

variable {M} {retained : Finset Record} {quota quotaX quotaY : Vertex → ℚ}
variable {x y : Record → ℚ}

omit [Fintype Record] in
private theorem rejects_slack (M : Market Vertex Record) {e : Record}
    (he : (M.ends e).card = 1) {v : Vertex} (hv : v ∈ M.ends e) :
    ¬M.Accepts x v e := by
  rintro ⟨f, hfv, hbetter, _⟩
  exact (not_lt_of_ge (M.slack_last e he v hv f hfv (by rintro rfl; exact lt_irrefl _ hbetter)).le)
    hbetter

private def Counted (M : Market Vertex Record) (x y : Record → ℚ) (v : Vertex)
    (e : Record) : Prop :=
  v ∈ M.ends e ∧
    ((y e < x e ∧ ¬M.Accepts y v e) ∨ (x e < y e ∧ ¬M.Accepts x v e))

private noncomputable def rejectionWeight (M : Market Vertex Record)
    (x y : Record → ℚ) (v : Vertex) (e : Record) : ℚ := by
  classical
  exact if M.Counted x y v e then |x e - y e| else 0

omit [Fintype Record] in
private theorem no_opposite_rejections (hx : ∀ e, 0 ≤ x e)
    (hy : ∀ e, 0 ≤ y e) {v : Vertex} {e f : Record}
    (he : v ∈ M.ends e) (hf : v ∈ M.ends f)
    (hxe : y e < x e) (hyf : x f < y f)
    (hre : ¬M.Accepts y v e) (hrf : ¬M.Accepts x v f) : False := by
  have hfe : M.rank v f ≤ M.rank v e :=
    le_of_not_gt (fun h => hre ⟨f, hf, h, (hx f).trans_lt hyf⟩)
  have hef : M.rank v e ≤ M.rank v f :=
    le_of_not_gt (fun h => hrf ⟨e, he, h, (hy e).trans_lt hxe⟩)
  have hef' := M.rank_injective v e f he hf (le_antisymm hef hfe)
  subst f
  exact lt_asymm hxe hyf

/-- Counted rejections have one sign. The imbalance between the two signs
is exactly the change in quota. -/
private theorem vertex_rejection_bound
    (hx : M.StableOn retained quotaX x) (hy : M.StableOn retained quotaY y) (v : Vertex) :
    2 * (∑ e, M.rejectionWeight x y v e) ≤
      (∑ e, if v ∈ M.ends e then |x e - y e| else 0) + |quotaX v - quotaY v| := by
  classical
  let pos (e : Record) := if v ∈ M.ends e then max (x e - y e) 0 else 0
  let neg (e : Record) := if v ∈ M.ends e then max (y e - x e) 0 else 0
  have hdiff (e : Record) : pos e - neg e =
      (if v ∈ M.ends e then x e else 0) - (if v ∈ M.ends e then y e else 0) := by
    by_cases hv : v ∈ M.ends e
    · by_cases h : y e ≤ x e
      · simp [pos, neg, hv, max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
      · have h' := le_of_not_ge h
        simp [pos, neg, hv, max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h')]
    · simp [pos, neg, hv]
  have habs (e : Record) :
      pos e + neg e = if v ∈ M.ends e then |x e - y e| else 0 := by
    by_cases hv : v ∈ M.ends e
    · by_cases h : y e ≤ x e
      · simp [pos, neg, hv, max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
          abs_of_nonneg (sub_nonneg.mpr h)]
      · have h' := le_of_not_ge h
        simp [pos, neg, hv, max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h'),
          abs_of_nonpos (sub_nonpos.mpr h')]
    · simp [pos, neg, hv]
  have hbalance : (∑ e, pos e) - (∑ e, neg e) = quotaX v - quotaY v := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [hdiff]
    rw [Finset.sum_sub_distrib, hx.balance, hy.balance]
  have habssum : (∑ e, if v ∈ M.ends e then |x e - y e| else 0) =
      (∑ e, pos e) + (∑ e, neg e) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [habs]
  by_cases hpositive : ∃ e, v ∈ M.ends e ∧ y e < x e ∧ ¬M.Accepts y v e
  · obtain ⟨f, hf, hxf, hrf⟩ := hpositive
    have hsum : (∑ e, M.rejectionWeight x y v e) ≤ ∑ e, pos e := by
      apply Finset.sum_le_sum
      intro e _
      by_cases he : M.Counted x y v e
      · rcases he.2 with ⟨h, _⟩ | ⟨h, hr⟩
        · simp [rejectionWeight, he, pos, he.1, abs_of_nonneg (sub_nonneg.mpr h.le),
            max_eq_left (sub_nonneg.mpr h.le)]
        · exact (no_opposite_rejections hx.nonneg hy.nonneg hf he.1 hxf h hrf hr).elim
      · simpa [rejectionWeight, he, pos] using
          (show 0 ≤ if v ∈ M.ends e then max (x e - y e) 0 else 0 from
            by split <;> simp)
    linarith [le_abs_self (quotaX v - quotaY v)]
  · have hsum : (∑ e, M.rejectionWeight x y v e) ≤ ∑ e, neg e := by
      apply Finset.sum_le_sum
      intro e _
      by_cases he : M.Counted x y v e
      · rcases he.2 with ⟨h, hr⟩ | ⟨h, _⟩
        · exact (hpositive ⟨e, he.1, h, hr⟩).elim
        · simp [rejectionWeight, he, neg, he.1, abs_of_nonpos (sub_nonpos.mpr h.le),
            max_eq_left (sub_nonneg.mpr h.le)]
      · simpa [rejectionWeight, he, neg] using
          (show 0 ≤ if v ∈ M.ends e then max (y e - x e) 0 else 0 from
            by split <;> simp)
    linarith [neg_le_abs (quotaX v - quotaY v)]

variable [Fintype Vertex]

private theorem record_rejection_bound
    (hx : M.StableOn retained quotaX x) (hy : M.StableOn retained quotaY y) (e : Record) :
    |x e - y e| ≤ ∑ v, M.rejectionWeight x y v e := by
  classical
  have hnonneg : ∀ v, 0 ≤ M.rejectionWeight x y v e := by
    intro v
    unfold rejectionWeight
    split <;> simp
  rcases lt_trichotomy (y e) (x e) with h | h | h
  · suffices hrej : ∃ v, v ∈ M.ends e ∧ ¬M.Accepts y v e by
      obtain ⟨v, hv, hr⟩ := hrej
      have hc : M.Counted x y v e := ⟨hv, Or.inl ⟨h, hr⟩⟩
      simpa [rejectionWeight, hc] using
        (Finset.single_le_sum (f := fun v => M.rejectionWeight x y v e)
          (fun v _ => hnonneg v) (Finset.mem_univ v))
    rcases M.degree e with hcard | hcard
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (M.ends e).card)
      exact ⟨v, hv, M.rejects_slack hcard hv⟩
    · by_contra hn
      push Not at hn
      exact hy.stable e (hx.support e hcard ((hy.nonneg e).trans_lt h)) ⟨hcard, hn⟩
  · simp [h, Finset.sum_nonneg (fun v _ => hnonneg v)]
  · suffices hrej : ∃ v, v ∈ M.ends e ∧ ¬M.Accepts x v e by
      obtain ⟨v, hv, hr⟩ := hrej
      have hc : M.Counted x y v e := ⟨hv, Or.inr ⟨h, hr⟩⟩
      simpa [rejectionWeight, hc] using
        (Finset.single_le_sum (f := fun v => M.rejectionWeight x y v e)
          (fun v _ => hnonneg v) (Finset.mem_univ v))
    rcases M.degree e with hcard | hcard
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (M.ends e).card)
      exact ⟨v, hv, M.rejects_slack hcard hv⟩
    · by_contra hn
      push Not at hn
      exact hx.stable e (hy.support e hcard ((hx.nonneg e).trans_lt h)) ⟨hcard, hn⟩

/-- The total variation in outside and vacancy records is bounded by the
total variation of the quotas, even when the quotas differ. -/
theorem slack_variation_le
    (hx : M.StableOn retained quotaX x) (hy : M.StableOn retained quotaY y) :
    (∑ e, if (M.ends e).card = 1 then |x e - y e| else 0) ≤
      ∑ v, |quotaX v - quotaY v| := by
  classical
  have hlower : (∑ f, |x f - y f|) ≤ ∑ f, ∑ v, M.rejectionWeight x y v f :=
    Finset.sum_le_sum (fun f _ => record_rejection_bound hx hy f)
  have hcount (f : Record) :
      (∑ v, if v ∈ M.ends f then |x f - y f| else 0) =
        ((M.ends f).card : ℚ) * |x f - y f| := by
    rw [← Finset.sum_filter]
    simp
  have hupper : 2 * (∑ f, ∑ v, M.rejectionWeight x y v f) ≤
      (∑ f, ((M.ends f).card : ℚ) * |x f - y f|) + ∑ v, |quotaX v - quotaY v| := by
    calc
      _ = 2 * (∑ v, ∑ f, M.rejectionWeight x y v f) := by rw [Finset.sum_comm]
      _ ≤ ∑ v, ((∑ f, if v ∈ M.ends f then |x f - y f| else 0) +
          |quotaX v - quotaY v|) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun v _ => vertex_rejection_bound hx hy v)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        refine congrArg (· + _) ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun f _ => hcount f)
  have hsplit (f : Record) : (if (M.ends f).card = 1 then |x f - y f| else 0) =
      2 * |x f - y f| - ((M.ends f).card : ℚ) * |x f - y f| := by
    rcases M.degree f with h | h
    · simp [h]
      linarith
    · simp [h]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

/-- Lemma 5. Outside and vacancy balances agree at a fixed quota. -/
theorem slack_invariant
    (hx : M.StableOn retained quota x) (hy : M.StableOn retained quota y)
    {e : Record} (he : (M.ends e).card = 1) : x e = y e := by
  have hzero := slack_variation_le hx hy
  simp at hzero
  have hn (f : Record) : 0 ≤ (if (M.ends f).card = 1 then |x f - y f| else 0) := by
    split <;> simp
  have hle := Finset.single_le_sum (f := fun f => if (M.ends f).card = 1 then |x f - y f| else 0)
    (fun f _ => hn f) (Finset.mem_univ e)
  have hle' := hle.trans hzero
  simp [he] at hle'
  exact sub_eq_zero.mp hle'

private theorem signed_balance (hx : M.StableOn retained quota x) (side : Vertex → ℚ) :
    (∑ v, side v * quota v) = ∑ e, (∑ v ∈ M.ends e, side v) * x e := by
  calc
    _ = ∑ v, ∑ e, if v ∈ M.ends e then side v * x e else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← hx.balance v, Finset.mul_sum]
      simp only [mul_ite, mul_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_mul, ← Finset.sum_filter]
      simp

/-- Orient each ordinary bid between opposite signs. When quotas change
in the direction of the signs, every slack moves in its endpoint's direction.
The market application uses sign −1 for buyers and +1 for sites. -/
theorem signed_slack_change
    (hx : M.StableOn retained quotaX x) (hy : M.StableOn retained quotaY y)
    (side : Vertex → ℚ) (hside : ∀ v, side v = 1 ∨ side v = -1)
    (hcancel : ∀ f, (M.ends f).card = 2 → (∑ v ∈ M.ends f, side v) = 0)
    (hquota : ∀ v, |quotaX v - quotaY v| = side v * (quotaX v - quotaY v))
    {e : Record} {v : Vertex} (he : M.ends e = {v}) :
    |x e - y e| = side v * (x e - y e) := by
  classical
  let signed (f : Record) := (∑ u ∈ M.ends f, side u) * (x f - y f)
  let gap (f : Record) := (if (M.ends f).card = 1 then |x f - y f| else 0) - signed f
  have haccount : (∑ u, |quotaX u - quotaY u|) = ∑ f, signed f := by
    simp_rw [hquota, mul_sub]
    rw [Finset.sum_sub_distrib, signed_balance hx, signed_balance hy, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro f _
    exact (mul_sub _ _ _).symm
  have hnonneg (f : Record) : 0 ≤ gap f := by
    rcases M.degree f with h | h
    · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h
      rcases hside u with hs | hs
      · simpa [gap, signed, h, hu, hs, sub_nonneg] using le_abs_self (x f - y f)
      · simpa [gap, signed, h, hu, hs, sub_nonneg] using neg_le_abs (x f - y f)
    · simp [gap, signed, h, hcancel f h]
  have htotal : (∑ f, gap f) ≤ 0 := by
    dsimp only [gap]
    rw [Finset.sum_sub_distrib, ← haccount]
    exact sub_nonpos.mpr (slack_variation_le hx hy)
  have hgap : gap e = 0 := le_antisymm
    ((Finset.single_le_sum (fun f _ => hnonneg f) (Finset.mem_univ e)).trans htotal) (hnonneg e)
  apply sub_eq_zero.mp
  simpa [gap, signed, he] using hgap

end Market
end Kintali
