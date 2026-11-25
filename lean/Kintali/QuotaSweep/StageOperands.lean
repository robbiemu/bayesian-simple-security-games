module

public import Kintali.QuotaSweep.OperandBounds

/-! # Operand bounds for one finite graph, its affine stage, and its budget test -/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.OperandBounds

open Kintali.ContactSize

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] (K : Book B S E)

/-- The partial sums range over arbitrary subsets, so the bounds hold in
any iteration order of the finite graph and outside-buyers tables. -/
structure StageOperands (P : Parameters B S) (z : State B S E) (w : ℕ) : Prop where
  inputs : ParametersFit w P
  pressure : Fits w z.pressure
  holding : ∀ e, Fits w (z.allocation e)
  routeSum : ∀ v (s : Finset (Vertex B S)),
    Fits w (∑ a ∈ s, ((Routing.visits (K.next z.allocation) v (Fintype.card (Option (Vertex B S)))
      (some a)).1 : ℚ) * Book.injection P.rate a)
  through : ∀ v, Fits w (K.through z.allocation P.rate v)
  received : ∀ e (s : Finset S), Fits w (∑ j ∈ s, if K.proposal z.allocation j = e then
    K.through z.allocation P.rate (.inr j) else 0)
  released : ∀ e (s : Finset B), Fits w (∑ b ∈ s, if K.worst z.allocation b = e then
    K.through z.allocation P.rate (.inl b) else 0)
  derivative : ∀ e, Fits w (K.direction z.allocation (K.through z.allocation P.rate) e)
  exhaustion : ∀ d ∈ K.exhaustions z.allocation P.rate, Fits w d
  upperGap : Fits w (P.upper-z.pressure)
  duration : Fits w (K.duration z.allocation P.rate z.pressure P.upper)
  startingOutside : ∀ p, Fits w (Book.privateOutside p z.allocation)
  outsideDerivative : ∀ p, Fits w (Book.privateOutside p (K.direction z.allocation
    (K.through z.allocation P.rate)))
  budgetGap : Fits w (P.target-Book.privateOutside P.privateBuyers z.allocation)
  budgetTime : Fits w (K.budgetTime P z)
  advance : ∀ δ, δ = K.duration z.allocation P.rate z.pressure P.upper ∨ δ = K.budgetTime P z →
    Fits w (δ*K.speed z.allocation) ∧ Fits w (K.segment P z δ).pressure ∧
    (∀ e, Fits w (δ*K.direction z.allocation (K.through z.allocation P.rate) e)) ∧
    (∀ e, Fits w ((K.segment P z δ).allocation e)) ∧
    ∀ p, Fits w (Book.privateOutside p (K.segment P z δ).allocation)

private theorem subWidth {q r : ℚ} {u v : ℕ} (hq : Fits u q) (hr : Fits v r) :
    Fits (u+v+1) (q-r) := by simpa [sub_eq_add_neg] using hq.add (KeyWidth.fits_neg hr)

private theorem subset_flow {A : Type*} [Fintype A] (s : Finset A) (n u : ℕ)
    (hn : Fintype.card A ≤ n) (f : A → ℚ) (h : ∀ a, Fits u (f a)) :
    Fits (sumWidth n u) (∑ a ∈ s, f a) := (Fits.sum _ _ (fun a _ => h a)).mono
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ ((Finset.card_le_univ s).trans hn)) 1)

theorem stage_operands {P : Parameters B S} {u w : ℕ} (inputs : ParametersFit u P)
    (z : State B S E) (pressure : Fits u z.pressure) (hold : ∀ e, Fits u (z.allocation e))
    (hw : stageWidth (Fintype.card (Vertex B S)) u ≤ w) : StageOperands K P z w := by
  let n := Fintype.card (Vertex B S)
  change stageWidth n u ≤ w at hw
  have hb : Fintype.card B ≤ n := by simp [n]
  have hs : Fintype.card S ≤ n := by simp [n]
  have upper : advanceWidth n u ≤ w := by unfold stageWidth at hw; omega
  have after : sumWidth n (advanceWidth n u) ≤ w := by unfold stageWidth at hw; omega
  have evt : eventWidth n u ≤ w := by unfold advanceWidth at upper; omega
  have budget : budgetWidth n u ≤ w := by unfold advanceWidth at upper; omega
  have diff : changeWidth n u ≤ w := by unfold advanceWidth at upper; omega
  have rate : rateWidth n u ≤ w := by unfold eventWidth at evt; omega
  have sumBound : sumWidth n (rateWidth n u) ≤ w := by unfold changeWidth at diff; omega
  have orig : u ≤ w := by unfold advanceWidth at upper; omega
  have zero : Fits (rateWidth n u) 0 := Fits.zero.mono (by simp [rateWidth,sumWidth])
  have through (v) := through_fits K inputs z.allocation v
  have derivative (e) := change_fits K inputs z.allocation e
  refine ⟨⟨fun b => (inputs.rate b).mono orig,fun s => (inputs.mass s).mono orig,
    inputs.target.mono orig,inputs.upper.mono orig⟩, pressure.mono orig,fun e => (hold e).mono orig,
    ?_,fun v => (through v).mono rate,?_,?_,fun e => (derivative e).mono diff,
    ?_,?_,(duration_fits K inputs z pressure hold).mono evt,?_,?_,?_,(budget_fits K inputs z hold).mono budget,?_⟩
  · intro v s
    exact (route_partial (K.next z.allocation) (Book.injection P.rate)
      (fun a => by cases a with
                   | inl _ => exact Fits.zero.mono inputs.upper.pos
                   | inr j => exact inputs.rate j) v s).mono rate
  · intro e s
    apply Fits.mono _ sumBound
    apply subset_flow _ _ _ hs
    intro j
    split
    · exact through _
    · exact zero
  · intro e s
    apply Fits.mono _ sumBound
    apply subset_flow _ _ _ hb
    intro b
    split
    · exact through _
    · exact zero
  · intro d hd
    exact (candidate_fits K inputs z hold hd).mono (show u+rateWidth n u ≤ w by unfold eventWidth at evt; omega)
  · exact (subWidth inputs.upper pressure).mono (show u+u+1 ≤ w by unfold eventWidth at evt; omega)
  · intro p
    exact (outside_fits (S := S) hold p).mono (show sumWidth n u ≤ w by unfold budgetWidth at budget; omega)
  · intro p
    exact (outside_fits (S := S) derivative p).mono (show sumWidth n (changeWidth n u) ≤ w by unfold budgetWidth at budget; omega)
  · exact (subWidth inputs.target (outside_fits (S := S) hold P.privateBuyers)).mono
      (show u+sumWidth n u+1 ≤ w by unfold budgetWidth at budget; omega)
  · intro δ hδ
    obtain ⟨hp,hx,_⟩ := segment_fits K inputs z pressure hold δ hδ
    have delta : Fits (eventWidth n u + budgetWidth n u) δ := by
      rcases hδ with rfl | rfl
      · exact (duration_fits K inputs z pressure hold).mono (Nat.le_add_right ..)
      · exact (budget_fits K inputs z hold).mono (Nat.le_add_left ..)
    have speed : Fits 1 (K.speed z.allocation) := by
      unfold Book.speed; split; exact Fits.zero; exact Fits.one
    exact ⟨(delta.mul speed).mono (by unfold advanceWidth at upper; omega),hp.mono upper,
      fun e => (delta.mul (derivative e)).mono (by change eventWidth n u+budgetWidth n u+changeWidth n u ≤ w
                                                   unfold advanceWidth at upper; omega),
      fun e => (hx e).mono upper,fun p => (outside_fits (S := S) hx p).mono after⟩

end Kintali.QuotaSweep.OperandBounds
