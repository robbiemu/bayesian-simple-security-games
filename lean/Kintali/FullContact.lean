module

public import Kintali.MarketTrial
public import Kintali.BudgetContact
public import Kintali.ExactRecovery.Trial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity

/-!
# Full-market contact for the fixed witness

This full grid is used to prove existence of the witness. The executable
trial has its own sparse contact and does not build this grid.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.MarketTrial

open ExactRecovery ExactRecovery.Expanded QuotaSweep

variable {k m : ℕ} (g : Game (Fin k) (Fin m))

abbrev ExpandedRecord {k m : ℕ} (g : Game (Fin k) (Fin m)) :=
  R (Fin k) (Fin m) (grid g)

structure FullContact (hm : 0 < m) where
  pressure : ℚ
  allocation : ExpandedRecord g → ℚ
  stable : Stable g Fin.val Fin.val (redirect g hm) allQuotes (privateScale g) pressure allocation
  budget : (∑ j, (holdings allocation).physical g (privateScale g) j) = g.resources

private theorem mass_at_sites (j : Fin m) :
    (∑ h : Fin m × Fin (grid g), if h.1 = j then
      (if 0 < g.gain h.1 then privateScale g / grid g else 0) else 0) =
      if 0 < g.gain j then privateScale g else 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : 0 < g.gain j
  · simpa only [ite_eq_left h] using
      (gap_mass (G := grid g) (gridSize_pos g (contactTolerance g)) (privateScale g))
  · simp [h]

/-- A stable full contact exists at the supplied budget. -/
theorem fullContact_exists (valid : g.Valid) (normal : ¬g.DirectCase) :
    Nonempty (FullContact g valid.targets) := by
  let H := Fin m × Fin (grid g)
  let privateMass (h : H) := if 0 < g.gain h.1 then privateScale g / grid g else 0
  let P := BudgetContact.parameters g (privateScale g) (Prod.fst : H → Fin m) privateMass
  let K := book g Fin.val Fin.val (redirect g valid.targets) (allQuotes (G := grid g))
  let z := K.firstContact P
  have hG : 0 < grid g := gridSize_pos g (contactTolerance g)
  have hσ : 0 < privateScale g := sigma_pos g (contactTolerance_pos g)
  have hSmall (j : Fin m) : g.gain j * privateScale g < 1 :=
    (gain_sigma_le g (contactTolerance_pos g).le j).trans_lt (contactTolerance_lt_one g)
  have hSite (e : Bid (Fin k) (Fin m) (grid g)) (h : H)
      (he : K.buyer e = .inr h) : K.site e = h.1 := by
    rcases e with real | gap
    · cases he
    · have hs : gap = h := Sum.inr.inj he
      exact congrArg Prod.fst hs
  have hRetained (h : H) (active : 0 < g.gain h.1) : ∃ e ∈ K.retained, K.buyer e = .inr h :=
    ⟨privateBid h.1 h.2, (retained_private _ _ _ _ _ _ _).mpr active, rfl⟩
  have hNonneg (h : H) : 0 ≤ privateMass h := by
    dsimp [privateMass]
    split <;> positivity
  obtain ⟨hStable, _, _, hBudget⟩ :=
    BudgetContact.at_budget g valid normal (privateScale g) hσ hSmall K Prod.fst privateMass
      hNonneg (mass_at_sites g) hSite hRetained
  have hQuota : quota g (privateScale g) z.pressure = Book.quota P.rate P.mass z.pressure := by
    rw [quota_eq_sweep]
    congr 1
    · funext j
      simp [P, BudgetContact.parameters, BudgetContact.rate, siteRate, one_div]
    · funext a
      cases a <;> rfl
  have hExpanded : Stable g Fin.val Fin.val (redirect g valid.targets) allQuotes
      (privateScale g) z.pressure z.allocation := by
    change K.market.StableOn K.retainedRecords (quota g (privateScale g) z.pressure) z.allocation
    rwa [hQuota]
  have hCover (j : Fin m) :
      (holdings z.allocation).physical g (privateScale g) j =
        BudgetContact.coverage g (privateScale g) (Prod.fst : H → Fin m)
          (fun h => z.allocation (outside h)) j := by
    rw [← coverage_eq_physical hExpanded hσ hG]
    by_cases h : 0 < g.gain j
    · have hInj : Function.Injective (fun a : Fin (grid g) =>
          (outside (.inr (j, a)) : ExpandedRecord g)) := by
        intro a b hab
        simpa using hab
      simp only [Market.coverage, privateOutsideSet, ite_eq_left h, Finset.sum_image hInj.injOn,
        BudgetContact.coverage]
      congr 1
      rw [Fintype.sum_prod_type, Finset.sum_eq_single j]
      · simp
      · intro a _ hne
        simp [hne]
      · intro hne
        exact (hne (Finset.mem_univ _)).elim
    · simp [Market.coverage, privateOutsideSet, BudgetContact.coverage, h]
  refine ⟨⟨z.pressure, z.allocation, hExpanded, ?_⟩⟩
  simp_rw [hCover]
  rw [BudgetContact.coverage_sum]
  change Book.privateOutside P.privateBuyers z.allocation / (privateScale g) = g.resources
  rw [hBudget]
  change (privateScale g * (g.resources : ℚ)) / (privateScale g) = g.resources
  exact mul_div_cancel_left₀ _ hσ.ne'

end Kintali.MarketTrial
