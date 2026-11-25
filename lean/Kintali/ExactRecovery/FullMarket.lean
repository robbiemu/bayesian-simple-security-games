module

public import Kintali.ExactRecovery.Trial
public import Kintali.ExactRecovery.Pruning

/-! # Lemma 4 on the paper's grid

Specialize the contact argument to the computed game height H, residual
1/(4H), grid and private mass prescribed in Sections 1 and 2, and to the
complete eligible real book. Only stability and budget contact are needed
from the independent quota sweep.
-/

open scoped BigOperators
open Kintali.QuotaSweep

@[expose] public section
namespace Kintali.ExactRecovery.Expanded

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [LinearOrder J] [Nonempty J]
variable [Encodable I] [Encodable J]

theorem full_pattern_exact (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (t : ℚ)
    (X : R I J (gridSize g (eta g)) → ℚ)
    (stable : Stable g bi si (outsideTarget g) allQuotes (sigma g (eta g)) t X)
    (contact : (∑ j, (holdings X).physical g (sigma g (eta g)) j) = g.resources)
    (pressure : 0 ≤ t) (priorSum : ∑ i, g.prior i = 1) (budget : 0 < g.resources)
    (slope : ∀ i j, 0 ≤ g.slope i j) (gain : ∀ j, 0 ≤ g.gain j) :
    let x := (holdings X).physical g (sigma g (eta g))
    let p := contactPattern g x (referenceTarget g x) (eta g) (eta_bounds g).1.le
    ∃ y q θ, Relaxed g p y q θ 0 := by
  let η := eta g
  let x := (holdings X).physical g (sigma g η)
  have eb := eta_bounds g
  have h := stableContact stable (gridSize_pos g η) (sigma_pos g eb.1) pressure
    (outsideTarget_min g) contact
  apply Holdings.full_contact_exact h (referenceTarget g x) (referenceTarget_min g x)
      _ ⟨eb.1.le,eb.2.2⟩ eb.2.1 slope gain (slope_step_le g eb.1) (gain_sigma_le g eb.1.le) priorSum budget
  intro i j z eligible costBlock
  let K := book g bi si (outsideTarget g) (allQuotes (G := gridSize g η))
  have member := (retained_real g bi si (outsideTarget g) allQuotes i j z).mpr ⟨eligible,Or.inr rfl⟩
  exact stable.stable _ (K.mem_retainedRecords.mpr member) (costBlock_is_block bi si _ _ _ costBlock)

end Kintali.ExactRecovery.Expanded
