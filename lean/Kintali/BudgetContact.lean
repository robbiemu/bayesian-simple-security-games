module

public import Kintali.QuotaSweep.Contact
public import Kintali.ExactRecovery.Grid
public import Kintali.Theorem1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Kintali.QuotaSweep.Rates

/-!
# The quota sweep at the game budget

The same pressure and budget parameters apply to elementary gaps and
to grouped private buyers. At an active site's upper endpoint the
quota exceeds the total mass of every buyer who can buy there.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.BudgetContact

open QuotaSweep ExactRecovery

variable {k m : ℕ}

def activeSites (g : Game (Fin k) (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun j => 0 < g.gain j

theorem activeSites_card (g : Game (Fin k) (Fin m)) :
    (activeSites g).card = g.positiveTargets.length := by
  have hf : g.positiveTargets.toFinset = activeSites g := by
    ext j
    simp [activeSites, Game.positiveTargets]
  rw [← hf]
  exact List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)

theorem interior_budget (g : Game (Fin k) (Fin m)) (normal : ¬g.DirectCase) :
    0 < g.resources ∧ g.resources < (activeSites g).card := by
  rw [activeSites_card]
  unfold Game.DirectCase at normal
  omega

def rate (g : Game (Fin k) (Fin m)) (j : Fin m) : ℚ :=
  if 0 < g.gain j then (g.gain j)⁻¹ else 0

theorem rate_nonneg (g : Game (Fin k) (Fin m)) (j : Fin m) :
    0 ≤ rate g j := by
  unfold rate
  split
  · positivity
  · exact le_rfl

variable {H : Type*} [Fintype H] [DecidableEq H]

def privateSet (g : Game (Fin k) (Fin m)) (siteOf : H → Fin m) : Finset (Fin k ⊕ H) :=
  Finset.univ.filter fun b => (match b with
    | .inl _ => false
    | .inr h => decide (0 < g.gain (siteOf h))) = true

def mass (g : Game (Fin k) (Fin m)) (privateMass : H → ℚ) : Fin k ⊕ H → ℚ :=
  Sum.elim g.prior privateMass

def sitePool (siteOf : H → Fin m) (j : Fin m) : Finset (Fin k ⊕ H) :=
  Finset.univ.filter fun b => (match b with
    | .inl _ => true
    | .inr h => decide (siteOf h = j)) = true

def target (g : Game (Fin k) (Fin m)) (σ : ℚ) : ℚ :=
  σ * (g.resources : ℚ)

def parameters (g : Game (Fin k) (Fin m)) (σ : ℚ) (siteOf : H → Fin m) (privateMass : H → ℚ) :
    Parameters (Fin k ⊕ H) (Fin m) :=
  ⟨rate g, mass g privateMass, privateSet g siteOf, 1 + maxGain g, target g σ⟩

omit [DecidableEq H] in
private theorem pool_mass (g : Game (Fin k) (Fin m)) (σ : ℚ) (siteOf : H → Fin m)
    (privateMass : H → ℚ) (hPrior : (∑ i, g.prior i) = 1)
    (hPrivate : ∀ j, (∑ h, if siteOf h = j then privateMass h else 0) =
      if 0 < g.gain j then σ else 0)
    (j : Fin m) (hj : 0 < g.gain j) :
    (∑ b ∈ sitePool siteOf j, mass g privateMass b) = 1 + σ := by
  rw [sitePool, Finset.sum_filter, Fintype.sum_sum_type]
  simp [mass, hPrior, hPrivate j, hj]

omit [DecidableEq H] in
theorem privateSum_bySite (g : Game (Fin k) (Fin m)) (siteOf : H → Fin m)
    (values : Fin k ⊕ H → ℚ) :
    (∑ b ∈ privateSet g siteOf, values b) =
      ∑ j ∈ activeSites g, ∑ h, if siteOf h = j then values (.inr h) else 0 := by
  rw [privateSet, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [Bool.false_eq_true, ite_false, Finset.sum_const_zero, zero_add, decide_eq_true_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_ite_eq]
  simp [activeSites]

def coverage (g : Game (Fin k) (Fin m)) (σ : ℚ) (siteOf : H → Fin m)
    (values : Fin k ⊕ H → ℚ) (j : Fin m) : ℚ :=
  if 0 < g.gain j then (∑ h, if siteOf h = j then values (.inr h) else 0) / σ else 0

omit [DecidableEq H] in
theorem coverage_sum (g : Game (Fin k) (Fin m)) (σ : ℚ) (siteOf : H → Fin m)
    (values : Fin k ⊕ H → ℚ) :
    (∑ j, coverage g σ siteOf values j) = (∑ b ∈ privateSet g siteOf, values b) / σ := by
  rw [privateSum_bySite, div_eq_mul_inv, Finset.sum_mul, activeSites, Finset.sum_filter]
  simp only [coverage, div_eq_mul_inv]

omit [DecidableEq H] in
private theorem private_mass (g : Game (Fin k) (Fin m)) (σ : ℚ) (siteOf : H → Fin m)
    (privateMass : H → ℚ)
    (hPrivate : ∀ j, (∑ h, if siteOf h = j then privateMass h else 0) =
      if 0 < g.gain j then σ else 0) :
    (∑ b ∈ privateSet g siteOf, mass g privateMass b) = σ * (activeSites g).card := by
  rw [privateSum_bySite]
  simp only [mass, Sum.elim_inr, hPrivate]
  rw [show (∑ j ∈ activeSites g, if 0 < g.gain j then σ else 0) =
    ∑ _j ∈ activeSites g, σ from Finset.sum_congr rfl (fun j hj => by
      simp [(Finset.mem_filter.mp hj).2])]
  simp [mul_comm]

theorem upper_quota (g : Game (Fin k) (Fin m)) (σ : ℚ) (j : Fin m)
    (hj : 0 < g.gain j) (hPrivate : g.gain j * σ < 1) :
    1 + σ < rate g j * (1 + maxGain g) := by
  have hg : g.gain j ≤ maxGain g :=
    Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  rw [rate, ite_eq_left hj, ← div_eq_inv_mul]
  apply (lt_div_iff₀ hj).mpr
  linarith [mul_comm σ (g.gain j)]

variable {E : Type*} [DecidableEq E] [Fintype E]

/-- Reach exactly the private outside total that corresponds to the
given coverage budget. The assumptions apply to either private
representation. -/
theorem at_budget (g : Game (Fin k) (Fin m)) (valid : g.Valid) (normal : ¬g.DirectCase)
    (σ : ℚ) (hσ : 0 < σ) (small : ∀ j, g.gain j * σ < 1)
    (K : Book (Fin k ⊕ H) (Fin m) E) (siteOf : H → Fin m) (privateMass : H → ℚ)
    (hMass : ∀ h, 0 ≤ privateMass h)
    (hPrivate : ∀ j, (∑ h, if siteOf h = j then privateMass h else 0) =
      if 0 < g.gain j then σ else 0)
    (hSite : ∀ e h, K.buyer e = .inr h → K.site e = siteOf h)
    (hRetained : ∀ h, 0 < g.gain (siteOf h) → ∃ e ∈ K.retained, K.buyer e = .inr h) :
    let P := parameters g σ siteOf privateMass
    let z := K.firstContact P
    K.Feasible P z ∧ 0 < z.pressure ∧ z.pressure < P.upper ∧
      Book.privateOutside P.privateBuyers z.allocation = P.target := by
  let P := parameters g σ siteOf privateMass
  obtain ⟨hPositive, hInterior⟩ := interior_budget g normal
  have hPositive' : (0 : ℚ) < g.resources := by exact_mod_cast hPositive
  have hInterior' : (g.resources : ℚ) < (activeSites g).card := by exact_mod_cast hInterior
  have hu : 0 < P.upper := by
    have hMax : 0 ≤ maxGain g := Finset.le_max' _ 0 (Finset.mem_insert_self _ _)
    dsimp [P, parameters]
    linarith
  have htarget : 0 < P.target := mul_pos hσ hPositive'
  have hstart : P.target < ∑ b ∈ P.privateBuyers, P.mass b := by
    change target g σ < ∑ b ∈ privateSet g siteOf, mass g privateMass b
    rw [private_mass g σ siteOf privateMass hPrivate, target]
    exact mul_lt_mul_of_pos_left hInterior' hσ
  have hm : ∀ b, 0 ≤ P.mass b := by
    rintro (i | h)
    · exact valid.prior_nonneg i
    · exact hMass h
  obtain ⟨hStable, hPos, hBelow, hBudget, _⟩ :=
    K.budget_contact (P := P) (rate_nonneg g) hm hu htarget hstart (sitePool siteOf)
      (by
        intro e
        cases hb : K.buyer e with
        | inl i => simp [sitePool]
        | inr h => simp [sitePool, hSite e h hb])
      (by
        rintro (i | h) hb
        · simp [P, parameters, privateSet] at hb
        · have active : 0 < g.gain (siteOf h) := by simpa [P, parameters, privateSet] using hb
          obtain ⟨e, he, hBuyer⟩ := hRetained h active
          refine ⟨e, he, hBuyer, ?_⟩
          change (∑ c ∈ sitePool siteOf (K.site e), mass g privateMass c) <
            rate g (K.site e) * (1 + maxGain g)
          rw [hSite e h hBuyer, pool_mass g σ siteOf privateMass valid.prior_sum hPrivate _ active]
          exact upper_quota g σ (siteOf h) active (small _))
  exact ⟨hStable, hPos, hBelow, hBudget⟩

end Kintali.BudgetContact
