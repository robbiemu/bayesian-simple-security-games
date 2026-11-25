module

public import Kintali.ContactSize.View
import all Kintali.ContactSize.Sweep
import all Kintali.QuotaSweep.BitBounds
import all Kintali.QuotaSweep.SparseContact
import all Kintali.BudgetContact
import all StochasticGames.Precision
import Mathlib.Tactic.Linarith

/-! Every state obtained by stopping the actual sweep after a given number
of stages has polynomial-width entries. This includes the initial state,
every internal event and the final contact. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.ContactSize

open QuotaSweep StochasticGames.Precision

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

/-- Stopping on fuel exhaustion preserves feasibility and both pressure bounds. -/
theorem prefix_feasible (P : Parameters B S) (rates : ∀ s, 0 ≤ P.rate s)
    (n : ℕ) (z : State B S E) (stable : K.Feasible P z)
    (upper : z.pressure < P.upper) (budget : P.target < Book.privateOutside P.privateBuyers z.allocation) :
    let y := K.run P n z
    K.Feasible P y ∧ z.pressure ≤ y.pressure ∧ y.pressure ≤ P.upper := by
  induction n generalizing z with
  | zero => exact ⟨stable,le_rfl,upper.le⟩
  | succ n ih =>
    let δ := K.duration z.allocation P.rate z.pressure P.upper
    let f := K.segment P z δ
    have pos : 0 < δ := K.duration_pos (fun b => K.worst_positive_of_flow (x := z.allocation) rates
      (b := b)) upper
    have feas : K.Feasible P f := K.feasible_segment stable rates pos.le le_rfl
    have speed : 0 ≤ K.speed z.allocation := by unfold Book.speed; split <;> decide
    have advance : z.pressure ≤ f.pressure := le_add_of_nonneg_right (mul_nonneg pos.le speed)
    have cap : f.pressure ≤ P.upper := K.pressure_le_upper upper.le
    simp only [Book.run]
    split
    · rename_i hit
      obtain ⟨time,less,_,_⟩ := K.crossing_time pos budget hit
      exact ⟨K.feasible_segment stable rates time.le less,
        le_add_of_nonneg_right (mul_nonneg time.le speed),
        (add_le_add_right (mul_le_mul_of_nonneg_right less speed) z.pressure).trans cap⟩
    · rename_i miss
      split
      · exact ⟨feas,advance,cap⟩
      · rename_i below
        obtain ⟨hf,ha,hc⟩ := ih f feas (lt_of_not_ge below) (lt_of_not_ge miss)
        exact ⟨hf,advance.trans ha,hc⟩

theorem prefix_state {w r : ℕ} {P : Parameters B S} (fit : ParametersFit w P)
    (records : K.records.length ≤ r) (inventory : Fintype.card (Record B S E) ≤ r)
    (rates : ∀ s, 0 ≤ P.rate s) (masses : ∀ b, 0 ≤ P.mass b) (upper : 0 < P.upper)
    (target : P.target < ∑ b ∈ P.privateBuyers, P.mass b) {n : ℕ} (fuel : n ≤ r+1) :
    let z : State B S E := K.run P n ⟨0,Book.initial P.mass⟩
    Fits (stateWidth r w) z.pressure ∧ ∀ e, Fits (stateWidth r w) (z.allocation e) := by
  let z₀ : State B S E := ⟨0,Book.initial P.mass⟩
  let z := K.run P n z₀
  obtain ⟨stable,nonneg,cap⟩ := prefix_feasible K P rates n z₀
    (K.initial_stable P.rate masses) upper target
  obtain ⟨d,pos,bound,hs⟩ := K.run_scale (denominator_pos _) (K.input_rate_bounded P)
    n z₀ (denominator_pos _) (K.initial_scale P)
  have bits : d.size ≤ denominatorWidth r w :=
    (Book.size_of_power_bound bound).trans (Nat.add_le_add (scales K fit records).1
      (Nat.mul_le_mul (factor_size K fit records inventory) fuel))
  exact state_of_scale K fit stable nonneg cap pos bits (Arithmetic.denominator_dvd pos hs.pressure)
    (fun e => Arithmetic.denominator_dvd pos (hs.allocation e))

open ExactRecovery MarketTrial InputOutput QuoteSearch

/-- The actual selected market starts strictly below its pressure cap and
strictly above its private outside target on every interior input. -/
theorem selected_start (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :
    let g := a.game
    let P := Sparse.selectedParameters (G := grid g) g toSite s (privateScale g)
    (∀ j, 0 ≤ P.rate j) ∧ (∀ b, 0 ≤ P.mass b) ∧ 0 < P.upper ∧
      P.target < ∑ b ∈ P.privateBuyers, P.mass b := by
  let g := a.game
  let G := grid g
  let σ := privateScale g
  let layout := Sparse.selectedLayout (G := G) g toSite s
  let siteOf := fun h => (layout.representative h).1
  let mass := fun h => Sparse.mass g σ layout (.inr h)
  let P := Sparse.selectedParameters (G := G) g toSite s σ
  have hσ : 0 < σ := sigma_pos g (contactTolerance_pos g)
  have hG : 0 < G := gridSize_pos g (contactTolerance g)
  refine ⟨BudgetContact.rate_nonneg g,?_,?_,?_⟩
  · rintro (i|h)
    · exact ((Input.valid_iff a).mp valid).1.prior_nonneg i
    · change 0 ≤ if 0 < g.gain (layout.representative h).1 then (layout.size h : ℚ) * (σ/G) else 0
      split
      · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg hσ.le (Nat.cast_nonneg _))
      · exact le_rfl
  · change 0 < 1 + maxGain g
    have hn : 0 ≤ maxGain g := Finset.le_max' _ 0 (Finset.mem_insert_self _ _)
    linarith
  · change σ*(g.resources : ℚ) < ∑ b ∈ BudgetContact.privateSet g siteOf, BudgetContact.mass g mass b
    rw [BudgetContact.private_mass g σ siteOf mass
      (Sparse.intervalMass_sum g (Sparse.realEmbedding g toSite s) (Sparse.partition g toSite s) hG)]
    apply mul_lt_mul_of_pos_left _ hσ
    exact_mod_cast (BudgetContact.interior_budget g normal).2

/-- The same public polynomial bounds every stored numerical state along an
actual selected trial, for every truncation through its full fuel. -/
theorem selected_prefix (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) (hSelect : SelectionBound a s)
    {n : ℕ} (fuel : n ≤ recordLimit (Binary.lengthInput a)+1) :
    let g := a.game
    let G := grid g
    let layout := Sparse.selectedLayout (G := G) g toSite s
    let K := Sparse.book g Fin.val Fin.val layout
    let P := Sparse.selectedParameters (G := G) g toSite s (privateScale g)
    let z := K.run P n ⟨0,Book.initial P.mass⟩
    let b := allocationWidth (Binary.lengthInput a)
    Fits b z.pressure ∧ ∀ e, Fits b (z.allocation e) := by
  obtain ⟨_,_,card,len⟩ := selected_inventory a toSite s hSelect
  obtain ⟨rates,masses,upper,target⟩ := selected_start a valid normal toSite s
  exact prefix_state _ (parameters_fit a valid toSite s) len card rates masses upper target fuel

end Kintali.ContactSize
