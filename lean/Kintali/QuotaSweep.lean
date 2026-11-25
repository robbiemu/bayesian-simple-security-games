module

public import Kintali.QuotaSweep.RealContinuity
public import Kintali.QuotaSweep.BitBounds
public import Kintali.QuotaSweep.SparseContact
public import Kintali.QuotaSweep.PreparationWork
public import Kintali.QuotaSweep.InventoryRun

/-!
# Kintali §2, Lemma 3: the finite restricted quota sweep

A buyer releases its worst positive record. Each site proposes its best
retained bid whose buyer accepts, using its vacancy when no such bid exists.
`Book.worst` and `Book.proposal` define these two choices.

The choices form the proposal graph. A directed cycle uses unit flow and
keeps pressure fixed. In an acyclic graph the site injections propagate
along the unique outgoing paths. `Book.through_conservation` gives the
balance equation in either case. `Book.stable_segment` proves feasibility
and the absence of a blocking pair throughout each rational update.

The first exhausted holding ends a graph stage. The budget or upper
pressure can stop a stage sooner. Every internal endpoint removes a possible
worst record. `Book.firstContact` therefore uses at most one more step than
the number of records. The theorem below joins Kintali's first budget
contact to the stable, continuous private purchases along the real sweep.

The selected search trial uses `ExactRecovery.Sparse.selectedContact`.
It computes its contact on the grouped book, expands the private holdings
within each site's consecutive gaps in descending order, and assigns zero
to unused real grid records. `selectedContact_correct` proves stability
of this expansion and equality of every physical coverage.

`Book.contact_denominator_bits` bounds the common denominator of the
computed output. `Book.contactWork_polynomial` counts the finite scans,
graph walks and rational operations. `OperandBounds.selected_stage` and
`OperandBounds.selected_bit_charge` give input-dependent stage widths
and the corresponding schoolbook arithmetic charge. `ContactCharge.selected`
exposes the measured contact for composition with addressed trial code.
`StoredLookup.contact_read_work` bounds the individual allocation reads. `RankRun.Inventory.contact`
charges key construction and all ordinal rows against a supplied inventory.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

/-- The finite restricted part of Lemma 3, including the first contact and
the real-valued private-purchase curves at all intervening pressures. -/
theorem restricted_sweep {P : Parameters B S} (hr : ∀ s, 0 ≤ P.rate s)
    (hm : ∀ b, 0 ≤ P.mass b) (hu : 0 < P.upper) (htarget : 0 < P.target)
    (hstart : P.target < ∑ b ∈ P.privateBuyers, P.mass b)
    (pool : S → Finset B) (hpool : ∀ e, K.buyer e ∈ pool (K.site e))
    (hbid : ∀ b ∈ P.privateBuyers, ∃ e ∈ K.retained, K.buyer e = b ∧
      (∑ c ∈ pool (K.site e), P.mass c) < P.rate (K.site e)*P.upper) :
    let z := K.firstContact P
    K.Feasible P z ∧ 0 < z.pressure ∧ z.pressure < P.upper ∧
    privateOutside P.privateBuyers z.allocation = P.target ∧
    (∀ y, K.Feasible P y → y.pressure < z.pressure →
      P.target < privateOutside P.privateBuyers y.allocation) ∧
    (∀ t ∈ Set.Icc 0 (P.upper : ℝ), K.StableReal P.rate P.mass t (K.realSweep P t)) ∧
    ∀ p : Finset B,
      let purchases := fun t => ((∑ b ∈ p, P.mass b : ℚ) : ℝ) - realOutside p (K.realSweep P t)
      MonotoneOn purchases (Set.Icc 0 (P.upper : ℝ)) ∧ ContinuousOn purchases (Set.Icc 0 (P.upper : ℝ)) := by
  obtain ⟨stable,pos,bounded,atTarget,first⟩ := K.budget_contact hr hm hu htarget hstart pool hpool hbid
  exact ⟨stable,pos,bounded,atTarget,first,fun _ h => K.realSweep_stable hr hm hu h,
    fun p => K.privatePurchases_regular hr hm hu p⟩

end Kintali.QuotaSweep.Book
