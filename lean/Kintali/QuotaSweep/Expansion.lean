module

public import Kintali.ExactRecovery.SparseExtension
public import Kintali.ExactRecovery.Geometry
public import Kintali.QuotaSweep.Grouping

/-! # Grouped and expanded private balances at each site -/

open scoped BigOperators

@[expose] public section
namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep

variable {I J A H : Type*} {G : ℕ}

def groupUnit (g : Game I J) (σ : ℚ) (L : Layout I J G A H) (h : H) : ℚ :=
  if 0 < g.gain (L.representative h).1 then σ / G else 0

def siteOutside [Fintype H] [DecidableEq J] (L : Layout I J G A H) (x : R I J A H → ℚ)
    (j : J) : ℚ :=
  ∑ h, if (L.representative h).1 = j then x (outside (.inr h)) else 0

def siteCoverage [Fintype H] [DecidableEq J] (g : Game I J) (σ : ℚ) (L : Layout I J G A H)
    (x : R I J A H → ℚ) (j : J) : ℚ :=
  if 0 < g.gain j then siteOutside L x j / σ else 0

variable {L : Layout I J G A H} {P : Grouping.Partition (J × Fin G) H}

theorem coarseMass_eq (g : Game I J) (σ : ℚ) (geo : Geometry L P) :
    P.coarseMass g.prior (groupUnit g σ L) = mass g σ L := by
  funext b
  rcases b with i | h
  · rfl
  · by_cases ha : 0 < g.gain (L.representative h).1 <;>
      simp [Grouping.Partition.coarseMass, groupUnit, mass, ha, geo.size_eq]

theorem fineMass_eq (g : Game I J) (σ : ℚ) (geo : Geometry L P) :
    P.fineMass g.prior (groupUnit g σ L) = Expanded.buyerMass (G := G) g σ := by
  funext b
  rcases b with i | ⟨j,k⟩
  · rfl
  · simp [Grouping.Partition.fineMass, groupUnit, geo.same_site, Expanded.buyerMass]

variable [Fintype I] [Fintype J] [Fintype A]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A]

/-- Expand the grouped private buyers and extend unlisted real records by zero. -/
def expandedAllocation (g : Game I J) (σ : ℚ) (L : Layout I J G A H)
    (P : Grouping.Partition (J × Fin G) H) (x : R I J A H → ℚ) : Expanded.R I J G → ℚ :=
  Restriction.extend L.elementary.embedRecord (P.expand (groupUnit g σ L) x)

@[simp] theorem expanded_outside (g : Game I J) (σ : ℚ) (L : Layout I J G A H)
    (P : Grouping.Partition (J × Fin G) H) (x : R I J A H → ℚ) (f : J × Fin G) :
    expandedAllocation g σ L P x (outside (.inr f)) =
      P.expand (groupUnit g σ L) x (outside (.inr f)) :=
  Restriction.extend_image L.elementary.embedRecord _ (outside (.inr f))

variable [Fintype H] [DecidableEq H] [Encodable I] [Encodable J] [Encodable A] [Encodable H]
variable {g : Game I J} {bi : I → ℕ} {si : J → ℕ} {σ t : ℚ} {x : R I J A H → ℚ}

theorem siteOutside_eq (geo : Geometry L P)
    (refines : Grouping.Refinement P (book g bi si L) (book g bi si L.elementary))
    (hs : (book g bi si L).market.StableOn (book g bi si L).retainedRecords
      (Book.quota (Expanded.siteRate g) (mass g σ L) t) x) (j : J) :
    (∑ k : Fin G, expandedAllocation g σ L P x (outside (.inr (j,k)))) = siteOutside L x j := by
  rw [← coarseMass_eq g σ geo] at hs
  let y := P.expand (groupUnit g σ L) x
  have rows (h : H) := refines.outside_fiber hs h
  have hsite (h : H) (k : Fin (P.size h)) :
      (P.enumerate.symm ⟨h,k⟩).1 = (L.representative h).1 := by
    simpa only [P.group_symm] using (geo.same_site (P.enumerate.symm ⟨h,k⟩)).symm
  calc
    _ = ∑ f : J × Fin G, if f.1 = j then y (outside (.inr f)) else 0 := by
      rw [Fintype.sum_prod_type]
      simp [y]
    _ = _ := by
      rw [P.sum_fibers]
      simp only [hsite, Finset.sum_ite_irrel, Finset.sum_const_zero]
      exact Finset.sum_congr rfl fun h _ => by by_cases e : (L.representative h).1 = j <;> simp [e, y, rows]

end Kintali.ExactRecovery.Sparse
