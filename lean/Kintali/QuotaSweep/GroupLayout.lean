module

public import Kintali.QuotaSweep.GroupFill

/-!
# A consecutive-block refinement of an ordinal book

The coarse book and the fine book share the same sparse real-bid labels.
One coarse private buyer is split into equal masses at consecutive ranks.
Only structural incidence and preference comparisons are supplied by the
particular grid construction.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Grouping

abbrev PrivateBook (I S R F : Type*) [DecidableEq I] [DecidableEq S] [DecidableEq R]
    [DecidableEq F] := Book (I ⊕ F) S (R ⊕ F)
abbrev PrivateRecord (I S R F : Type*) := Record (I ⊕ F) S (R ⊕ F)

namespace Partition

variable {I S R F H : Type*} (P : Partition F H)

def buyer : I ⊕ F → I ⊕ H := Sum.map id P.group
def edge : R ⊕ F → R ⊕ H := Sum.map id P.group
def record : PrivateRecord I S R F → PrivateRecord I S R H :=
  Sum.map P.edge (Sum.map P.buyer id)

def coarseMass (realMass : I → ℚ) (unit : H → ℚ) : I ⊕ H → ℚ :=
  Sum.elim realMass (fun h => (P.size h : ℚ) * unit h)

def fineMass (realMass : I → ℚ) (unit : H → ℚ) : I ⊕ F → ℚ :=
  Sum.elim realMass (fun f => unit (P.group f))

/-- Keep real records and vacancies fixed and fill each private group from
highest rank down; assign each fine buyer the remaining outside balance. -/
def expand (unit : H → ℚ) (x : PrivateRecord I S R H → ℚ) : PrivateRecord I S R F → ℚ
  | .inl (.inl e) => x (bid (.inl e))
  | .inl (.inr f) => fill (unit (P.group f)) (x (bid (.inr (P.group f)))) (P.index f)
  | .inr (.inl (.inl i)) => x (outside (.inl i))
  | .inr (.inl (.inr f)) => unit (P.group f) -
      fill (unit (P.group f)) (x (bid (.inr (P.group f)))) (P.index f)
  | .inr (.inr s) => x (vacancy s)

end Partition

variable {I S R F H : Type*} [DecidableEq I] [DecidableEq S] [DecidableEq R]
variable [DecidableEq F] [DecidableEq H]
variable {P : Partition F H} {C : PrivateBook I S R H} {L : PrivateBook I S R F}

/-- Structural data for splitting private groups while preserving the retained
real bids and every strict comparison between distinct coarse records. -/
structure Refinement (P : Partition F H) (C : PrivateBook I S R H) (L : PrivateBook I S R F) where
  realOwner : R → I
  coarse_real : ∀ e, C.buyer (.inl e) = .inl (realOwner e)
  fine_real : ∀ e, L.buyer (.inl e) = .inl (realOwner e)
  coarse_private : ∀ h, C.buyer (.inr h) = .inr h
  fine_private : ∀ f, L.buyer (.inr f) = .inr f
  sites : ∀ e, L.site e = C.site (P.edge e)
  retained : ∀ e, e ∈ L.retained ↔ P.edge e ∈ C.retained
  buyer_rank : ∀ b e f, Sum.inl b ∈ L.market.ends e → Sum.inl b ∈ L.market.ends f →
    L.market.rank (.inl b) e < L.market.rank (.inl b) f →
    C.market.rank (.inl (P.buyer b)) (P.record e) < C.market.rank (.inl (P.buyer b)) (P.record f)
  site_rank : ∀ s e f, Sum.inr s ∈ L.market.ends e → Sum.inr s ∈ L.market.ends f →
    P.record e ≠ P.record f → L.market.rank (.inr s) e < L.market.rank (.inr s) f →
    C.market.rank (.inr s) (P.record e) < C.market.rank (.inr s) (P.record f)
  internal_rank : ∀ f g, P.group f = P.group g →
    L.market.rank (.inr (L.site (.inr f))) (bid (.inr f)) <
      L.market.rank (.inr (L.site (.inr f))) (bid (.inr g)) → P.index f < P.index g

namespace Refinement

variable (A : Refinement P C L)
include A

theorem owners (e : R ⊕ F) : P.buyer (L.buyer e) = C.buyer (P.edge e) := by
  cases e <;> simp [Partition.buyer, Partition.edge, A.coarse_real, A.fine_real,
    A.coarse_private, A.fine_private]

theorem maps_buyer {b : I ⊕ F} {e : PrivateRecord I S R F} (h : Sum.inl b ∈ L.market.ends e) :
    Sum.inl (P.buyer b) ∈ C.market.ends (P.record e) := by
  rcases e with e | b' | s
  · change Sum.inl (P.buyer b) ∈ C.market.ends (bid (P.edge e))
    exact (C.buyer_mem_bid _ _).mpr
      ((congrArg P.buyer ((L.buyer_mem_bid _ _).mp h)).trans (A.owners e))
  · change Sum.inl b ∈ L.market.ends (outside b') at h
    change Sum.inl (P.buyer b) ∈ C.market.ends (outside (P.buyer b'))
    simp [L.ends_outside] at h
    simp [h, C.ends_outside]
  · change Sum.inl b ∈ L.market.ends (vacancy s) at h
    simp [L.ends_vacancy] at h

theorem maps_site {s : S} {e : PrivateRecord I S R F} (h : Sum.inr s ∈ L.market.ends e) :
    Sum.inr s ∈ C.market.ends (P.record e) := by
  rcases e with e | b | t
  · change Sum.inr s ∈ C.market.ends (bid (P.edge e))
    exact (C.site_mem_bid _ _).mpr (((L.site_mem_bid _ _).mp h).trans (A.sites e))
  · change Sum.inr s ∈ L.market.ends (outside b) at h
    simp [L.ends_outside] at h
  · change Sum.inr s ∈ L.market.ends (vacancy t) at h
    change Sum.inr s ∈ C.market.ends (vacancy t)
    simpa [L.ends_vacancy, C.ends_vacancy] using h

/-- A fine private buyer can accept its unique ordinary bid only by
surrendering positive outside mass. -/
theorem private_accepts {y : PrivateRecord I S R F → ℚ} {f : F}
    (ha : L.market.Accepts y (.inl (.inr f)) (bid (.inr f))) :
    0 < y (outside (.inr f)) := by
  obtain ⟨r, hi, hr, hp⟩ := ha
  rcases r with (e | g) | b | s
  · have h := (L.buyer_mem_bid _ _).mp hi
    simp [A.fine_real] at h
  · have h := (L.buyer_mem_bid _ _).mp hi
    simp [A.fine_private] at h
    subst g
    exact False.elim ((lt_irrefl _) hr)
  · change Sum.inl (Sum.inr f) ∈ L.market.ends (outside b) at hi
    simp [L.ends_outside] at hi
    exact hi.symm ▸ hp
  · change Sum.inl (Sum.inr f) ∈ L.market.ends (vacancy s) at hi
    simp [L.ends_vacancy] at hi

variable [Fintype I] [Fintype S] [Fintype R] [Fintype H]

theorem private_row {x : PrivateRecord I S R H → ℚ} {rate : S → ℚ} {mass : I → ℚ}
    {unit : H → ℚ} {t : ℚ}
    (hx : C.market.StableOn C.retainedRecords (Book.quota rate (P.coarseMass mass unit) t) x)
    (h : H) :
    x (bid (.inr h)) + x (outside (.inr h)) = (P.size h : ℚ)*unit h := by
  simpa [Fintype.sum_sum_type, A.coarse_real, A.coarse_private, Partition.coarseMass] using
    C.buyer_balance hx (.inr h)

theorem outside_fiber {x : PrivateRecord I S R H → ℚ} {rate : S → ℚ} {mass : I → ℚ}
    {unit : H → ℚ} {t : ℚ}
    (hx : C.market.StableOn C.retainedRecords (Book.quota rate (P.coarseMass mass unit) t) x)
    (h : H) :
    (∑ k : Fin (P.size h), P.expand unit x
      (outside (.inr (P.enumerate.symm ⟨h, k⟩)))) = x (outside (.inr h)) := by
  have hrow := A.private_row hx h
  have hcap : x (bid (.inr h)) ≤ (P.size h : ℚ)*unit h := by linarith [hx.nonneg (outside (.inr h))]
  simp only [Partition.expand, Partition.group_symm, Partition.index_symm]
  rw [outside_sum (hx.nonneg _) hcap]
  linarith

theorem positive_coarse {x : PrivateRecord I S R H → ℚ} {rate : S → ℚ} {mass : I → ℚ}
    {unit : H → ℚ} {t : ℚ} (hw : ∀ h, 0 ≤ unit h)
    (hx : C.market.StableOn C.retainedRecords (Book.quota rate (P.coarseMass mass unit) t) x)
    {e : PrivateRecord I S R F} (hp : 0 < P.expand unit x e) : 0 < x (P.record e) := by
  rcases e with (e | f) | (i | f) | s
  · exact hp
  · change 0 < x (bid (.inr (P.group f)))
    by_contra! hz
    have he := le_antisymm hz (hx.nonneg _)
    change 0 < fill _ _ _ at hp
    simp [fill, he, min_eq_right (mul_nonneg (Nat.cast_nonneg _) (hw _))] at hp
  · exact hp
  · let h := P.group f
    change 0 < x (outside (.inr h))
    have hrow := A.private_row hx h
    by_contra! hz
    have hzero := le_antisymm hz (hx.nonneg _)
    have hcap : x (bid (.inr h)) = (P.size h : ℚ)*unit h := by linarith
    have hk : P.index f + 1 ≤ P.size h := (P.enumerate f).2.isLt
    have h₁ := mul_le_mul_of_nonneg_right (show ((P.index f+1 : ℕ) : ℚ) ≤ (P.size h : ℚ)
      by exact_mod_cast hk) (hw h)
    have h₂ := mul_le_mul_of_nonneg_right (show (P.index f : ℚ) ≤ (P.size h : ℚ)
      by exact_mod_cast (Nat.le_of_succ_le hk)) (hw h)
    change 0 < unit h - fill (unit h) (x (bid (.inr h))) (P.index f) at hp
    rw [fill, hcap, min_eq_left h₁, min_eq_left h₂] at hp
    push_cast at hp
    linarith
  · exact hp

end Refinement
end Kintali.QuotaSweep.Grouping
