module

public import Kintali.QuotaSweep.SparseRefinement
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Size of a restricted trial

Each pair contributes at most its selected optional quotes and one cap.
A site needs at most one private group beyond its number of real bids.
-/

open scoped BigOperators
@[expose] public section

namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep Kintali.QuoteSearch

variable {k m G : ℕ} (g : Game (Fin k) (Fin m)) (redirect : Fin k → Fin m)
variable (s : Selection (k * m))

theorem realBids_count {J : ℕ} (hJ : 0 < J)
    (hSelect : ∀ p : Fin (k * m), s[p].length ≤ J - 1) :
    (realBids (G := G) g redirect s).card ≤ k * m * J := by
  calc
    _ ≤ ∑ p : Fin k × Fin m,
          ((realAt (G := G) g redirect s p).image (fun z => (p.1,p.2,z))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin k × Fin m, J := by
      apply Finset.sum_le_sum
      intro p _
      have hs := hSelect (finProdFinEquiv p)
      have h := realAt_card_le (G := G) g redirect s p
      exact Finset.card_image_le.trans (h.trans (by omega))
    _ = _ := by simp [Fintype.card_prod]

theorem groups_count_at (j : Fin m) :
    (partition (G := G) g redirect s j).groups ≤
      ((realBids (G := G) g redirect s).filter (fun b => b.2.1 = j)).card + 1 := by
  change (siteCuts (G := G) g redirect s j).sort.length - 1 ≤ _
  rw [Finset.length_sort]
  have h1 := Finset.card_insert_le 0 (insert G
    (((realBids (G := G) g redirect s).filter (fun b => b.2.1 = j)).image (fun b => b.2.2.val)))
  have h2 := Finset.card_insert_le G
    (((realBids (G := G) g redirect s).filter (fun b => b.2.1 = j)).image (fun b => b.2.2.val))
  have h3 := Finset.card_image_le (f := fun b : ListedBid k m G => b.2.2.val)
    (s := (realBids (G := G) g redirect s).filter (fun b => b.2.1 = j))
  unfold siteCuts
  omega

theorem groups_count :
    Fintype.card (IntervalGroup (partition (G := G) g redirect s)) ≤
      (realBids (G := G) g redirect s).card + m := by
  classical
  have hf : (∑ j : Fin m, ((realBids (G := G) g redirect s).filter (fun b => b.2.1 = j)).card) =
      (realBids (G := G) g redirect s).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ j : Fin m, (((realBids (G := G) g redirect s).filter (fun b => b.2.1 = j)).card + 1) :=
      Finset.sum_le_sum (fun j _ => groups_count_at g redirect s j)
    _ = _ := by simp [Finset.sum_add_distrib, hf]

end Kintali.ExactRecovery.Sparse
