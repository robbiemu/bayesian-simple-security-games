module

public import Kintali.ExactRecovery.Cutoff
public import Kintali.QuotaSweep.Expansion
import Mathlib.Data.Fintype.BigOperators

/-! # Computing real attack flows and bid tests from the sparse holdings

The executable functions enumerate the explicitly listed real labels A.
The expanded allocation appears only in their correctness statements.
-/

open scoped BigOperators
open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Sparse

variable {I J A H : Type*} {G : ℕ}

/-- The real and slack records needed to evaluate the trial. -/
structure RepresentsReal (L : Layout I J G A H) (x : R I J A H → ℚ) (Y : Expanded.R I J G → ℚ) : Prop where
  listed : ∀ a, Y (bid (.inl (L.real a))) = x (bid (.inl a))
  omitted : ∀ d, (∀ a, L.real a ≠ d) → Y (bid (.inl d)) = 0
  outside : ∀ i, Y (QuotaSweep.outside (.inl i)) = x (QuotaSweep.outside (.inl i))
  vacancy : ∀ j, Y (QuotaSweep.vacancy j) = x (QuotaSweep.vacancy j)

variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [Fintype I] [Fintype J] [Fintype A]

theorem represents_expansion (L : Layout I J G A H) (P : Grouping.Partition (J × Fin G) H)
    (unit : H → ℚ) (x : R I J A H → ℚ) :
    RepresentsReal L x (Restriction.extend L.elementary.embedRecord (P.expand unit x)) := by
  let E := L.elementary.embedRecord
  constructor
  · intro a
    exact Restriction.extend_image E (P.expand unit x) (bid (.inl a))
  · intro d absent
    apply Restriction.extend_zero
    rintro ((a | f) | v) eq
    · exact absent a (Sum.inl.inj (Sum.inl.inj eq))
    · exact Sum.inr_ne_inl (show (Sum.inr f : Expanded.Bid I J G) = Sum.inl d from Sum.inl.inj eq)
    · exact Sum.inr_ne_inl eq
  · intro i
    exact Restriction.extend_image E (P.expand unit x) (outside (.inl i))
  · intro j
    exact Restriction.extend_image E (P.expand unit x) (vacancy j)

theorem represents_expandedAllocation (g : Game I J) (σ : ℚ) (L : Layout I J G A H)
    (P : Grouping.Partition (J × Fin G) H) (x : R I J A H → ℚ) :
    RepresentsReal L x (expandedAllocation g σ L P x) :=
  represents_expansion L P (groupUnit g σ L) x

variable {L : Layout I J G A H} {x : R I J A H → ℚ} {Y : Expanded.R I J G → ℚ}

omit [DecidableEq I] [DecidableEq J] [DecidableEq A] [Fintype I] [Fintype J] [Fintype A] in
theorem positive_real_image (rep : RepresentsReal L x Y) {d : I × (J × Quote G)}
    (pos : 0 < Y (bid (.inl d))) : ∃ a, L.real a = d ∧ 0 < x (bid (.inl a)) := by
  by_cases yes : ∃ a, L.real a = d
  · obtain ⟨a,rfl⟩ := yes
    exact ⟨a,rfl,(rep.listed a) ▸ pos⟩
  · exact (pos.ne' (rep.omitted d (fun a eq => yes ⟨a,eq⟩))).elim

omit [Fintype I] [Fintype J] in
private theorem real_fiber (rep : RepresentsReal L x Y) (d : I × (J × Quote G)) :
    Y (bid (.inl d)) = ∑ a, if L.real a = d then x (bid (.inl a)) else 0 := by
  by_cases yes : ∃ a, L.real a = d
  · obtain ⟨a,rfl⟩ := yes
    simp [L.real.injective.eq_iff, rep.listed]
  · have absent (a : A) : L.real a ≠ d := fun eq => yes ⟨a,eq⟩
    simp [absent, rep.omitted d absent]

/-- The redirected flow on a target uses one sparse real-bid sum. -/
def attackJoint (L : Layout I J G A H) (redirect : I → J) (x : R I J A H → ℚ) (i : I) (j : J) : ℚ :=
  (∑ a, if (L.real a).1 = i ∧ (L.real a).2.1 = j then x (bid (.inl a)) else 0) +
    if redirect i = j then x (outside (.inl i)) else 0

omit [Fintype I] [Fintype J] in
theorem attackJoint_eq (rep : RepresentsReal L x Y) (redirect : I → J) :
    attackJoint L redirect x = (Expanded.holdings Y).joint redirect := by
  funext i j
  simp only [attackJoint, Holdings.joint, Expanded.holdings, Expanded.realBid, rep.outside,
    add_left_inj, real_fiber rep]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Quote G)))]
  apply Finset.sum_congr rfl
  intro a _
  rcases ha : L.real a with ⟨b,k,w⟩
  by_cases hi : b = i <;> by_cases hj : k = j <;> simp [hi, hj]

variable [Encodable I] [Encodable J]

/-- A real buyer checks outside and its positive real purchases; private
groups and other buyers' records never enter the comparison. -/
def buyerAcceptsQuote (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H)
    (x : R I J A H → ℚ) (i : I) (j : J) (z : Quote G) : Bool :=
  decide (0 < x (outside (.inl i)) ∨ ∃ a : A, (L.real a).1 = i ∧ 0 < x (bid (.inl a)) ∧
    Expanded.key g bi si (.inl (.inl i)) (bid (Expanded.realBid i j z)) <
      Expanded.key g bi si (.inl (.inl i)) (bid (.inl (L.real a))))

omit [DecidableEq A] in
theorem buyerAcceptsQuote_iff (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    (rep : RepresentsReal L x Y) (i : I) (j : J) (z : Quote G) :
    buyerAcceptsQuote g bi si L x i j z = true ↔
      (Expanded.market g bi si).Accepts Y (.inl (.inl i)) (bid (Expanded.realBid i j z)) := by
  simp only [buyerAcceptsQuote, decide_eq_true_eq]
  constructor
  · rintro (out | ⟨a,owner,pos,preference⟩)
    · exact ⟨outside (.inl i), by simp [Expanded.market, Expanded.ends],
        Expanded.ordinary_before_slack ..,(rep.outside i).symm ▸ out⟩
    · refine ⟨bid (.inl (L.real a)), ?_, Expanded.rank_strict g bi si _ preference, (rep.listed a).symm ▸ pos⟩
      simp [Expanded.market, Expanded.ends, Expanded.buyer, owner]
  · rintro ⟨r,inc,better,pos⟩
    rcases r with (d | f) | ((b | f) | k)
    · obtain ⟨a,rfl,purchased⟩ := positive_real_image rep pos
      refine Or.inr ⟨a,?_,purchased,(Expanded.rank_lt_iff_key ..).mp better⟩
      simpa [Expanded.market, Expanded.ends, Expanded.buyer, eq_comm] using inc
    · simp [Expanded.market, Expanded.ends, Expanded.buyer] at inc
    · have eq : i = b := by simpa [Expanded.market, Expanded.ends] using inc
      subst b
      exact Or.inl ((rep.outside i) ▸ pos)
    · simp [Expanded.market, Expanded.ends] at inc
    · simp [Expanded.market, Expanded.ends] at inc

/-- The site checks its coverage cutoff and, only at equality, vacancy or
a same-quote positive real purchase with lower buyer priority. -/
def siteAcceptsQuote (coverage : J → ℚ) (bi : I → ℕ) (L : Layout I J G A H)
    (x : R I J A H → ℚ) (i : I) (j : J) (z : Quote G) : Bool :=
  decide (coverage j < price z ∨ coverage j = price z ∧
    (0 < x (vacancy j) ∨ ∃ a : A, (L.real a).2 = (j,z) ∧ bi i < bi (L.real a).1 ∧ 0 < x (bid (.inl a))))

omit [DecidableEq A] in
theorem siteAcceptsQuote_iff {g : Game I J} {redirect : I → J} {σ t : ℚ}
    (bi : I → ℕ) (si : J → ℕ) (unique : Function.Injective bi) (rep : RepresentsReal L x Y)
    (contact : (Expanded.holdings Y).Contact g redirect σ t) (coverage : J → ℚ)
    (correct : coverage = (Expanded.holdings Y).physical g σ) (i : I) (j : J)
    (site : 0 < g.gain j) (z : Quote G) :
    siteAcceptsQuote coverage bi L x i j z = true ↔
      (Expanded.market g bi si).Accepts Y (.inr j) (bid (Expanded.realBid i j z)) := by
  rw [Expanded.site_accepts_iff_cutoff contact unique i j site z]
  simp only [siteAcceptsQuote, decide_eq_true_eq, correct, Expanded.holdings, rep.vacancy]
  refine or_congr Iff.rfl (and_congr Iff.rfl (or_congr Iff.rfl ?_))
  constructor
  · rintro ⟨a,equal,index,pos⟩
    refine ⟨(L.real a).1,index,?_⟩
    have d : L.real a = ((L.real a).1,j,z) := Prod.ext rfl equal
    have purchase := (rep.listed a).symm ▸ pos
    rwa [d] at purchase
  · rintro ⟨b,index,pos⟩
    obtain ⟨a,ha,hp⟩ := positive_real_image rep pos
    exact ⟨a,congrArg Prod.snd ha,by simpa only [ha] using index,hp⟩

end Kintali.ExactRecovery.Sparse
