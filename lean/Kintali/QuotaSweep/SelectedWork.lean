module

public import Kintali.QuotaSweep.StageOperands
public import Kintali.ContactSize.Prefix
import Mathlib.Tactic.Linarith

/-! # Restricted-sweep work and arithmetic widths on a public finite input -/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.OperandBounds

open Kintali.ContactSize Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch
open StochasticGames.BinarySize

def inputWidth (L : ℕ) := parameterWidth L + allocationWidth L
def inputStageWidth (L : ℕ) := stageWidth (recordLimit L) (inputWidth L)
def inputSlots (L : ℕ) := 300*(recordLimit L+2)^5
def inputStageBitCharge (L : ℕ) := inputSlots L * (64*(2*inputStageWidth L+2)^3)

theorem selected_slots (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) :
    (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).2 ≤ inputSlots (Binary.lengthInput a) := by
  obtain ⟨_,_,_,hr⟩ := selected_inventory a toSite s hs
  apply (Sparse.selectedRun_work (G := grid a.game) a.game toSite s (privateScale a.game)).trans
  unfold inputSlots
  gcongr

private theorem stage_bound_mono {n m u : ℕ} (h : n ≤ m) :
    stageWidth n u ≤ stageWidth m u := by
  unfold stageWidth advanceWidth eventWidth budgetWidth changeWidth rateWidth sumWidth; gcongr

/-- All rational graph sums, event candidates, stored updates and budget
comparisons in every selected stage fit a single input-dependent width. -/
theorem selected_operands (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) (hs : SelectionBound a s)
    {fuel : ℕ} (hn : fuel ≤ recordLimit (Binary.lengthInput a)+1) :
    let G := grid a.game
    let K := Sparse.book a.game Fin.val Fin.val (Sparse.selectedLayout (G := G) a.game toSite s)
    let P := Sparse.selectedParameters (G := G) a.game toSite s (privateScale a.game)
    let z := K.run P fuel ⟨0,Book.initial P.mass⟩
    StageOperands K P z (inputStageWidth (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  let G := grid a.game
  let l := Sparse.selectedLayout (G := G) a.game toSite s
  let K := Sparse.book a.game Fin.val Fin.val l
  let P := Sparse.selectedParameters (G := G) a.game toSite s (privateScale a.game)
  let z := K.run P fuel ⟨0,Book.initial P.mass⟩
  let n := Fintype.card (Vertex (Fin a.types ⊕ Sparse.IntervalGroup (Sparse.partition (G := G) a.game toSite s)) (Fin a.targets))
  obtain ⟨_,_,_,hr⟩ := selected_inventory a toSite s hs
  have hn' : n ≤ recordLimit L := K.vertex_count_le.trans hr
  have h := parameters_fit a valid toSite s
  have u₁ : parameterWidth L ≤ inputWidth L := Nat.le_add_right ..
  have u₂ : allocationWidth L ≤ inputWidth L := Nat.le_add_left ..
  have hin : ParametersFit (inputWidth L) P :=
    ⟨fun j => (h.rate j).mono u₁,fun b => (h.mass b).mono u₁,h.target.mono u₁,h.upper.mono u₁⟩
  obtain ⟨hp,hx⟩ := selected_prefix a valid normal toSite s hs hn
  exact stage_operands K hin z (hp.mono u₂) (fun e => (hx e).mono u₂) (stage_bound_mono hn')

/-- Both candidate updates at every prefix of a selected public run satisfy one
input polynomial, including their pressures, all holdings, and every site's
or market-wide sum of outside holdings used by the stop test. -/
theorem selected_stage (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) (hs : SelectionBound a s)
    {fuel : ℕ} (hn : fuel ≤ recordLimit (Binary.lengthInput a)+1) :
    let L := Binary.lengthInput a
    let G := grid a.game
    let layout := Sparse.selectedLayout (G := G) a.game toSite s
    let K := Sparse.book a.game Fin.val Fin.val layout
    let P := Sparse.selectedParameters (G := G) a.game toSite s (privateScale a.game)
    let z := K.run P fuel ⟨0,Book.initial P.mass⟩
    ∀ δ : ℚ, δ = K.duration z.allocation P.rate z.pressure P.upper ∨ δ = K.budgetTime P z →
      Fits (inputStageWidth L) (K.segment P z δ).pressure ∧
      (∀ e, Fits (inputStageWidth L) ((K.segment P z δ).allocation e)) ∧
      ∀ p, Fits (inputStageWidth L) (Book.privateOutside p (K.segment P z δ).allocation) := by
  have h := selected_operands a valid normal toSite s hs hn
  exact fun δ hs => ⟨(h.advance δ hs).2.1,(h.advance δ hs).2.2.2.1,(h.advance δ hs).2.2.2.2⟩

/-- A raw numerator sum, its unreduced denominator, and both products of
a quotient fit in the binary-arithmetic slot before Euclidean reduction. -/
theorem raw_arithmetic {a b : ℚ} {u v : ℕ} (ha : Fits u a) (hb : Fits v b) :
    (a.num*(b.den : ℤ)+(a.den : ℤ)*b.num).natAbs.size ≤ u+v+1 ∧
    (a.den*b.den).size ≤ u+v ∧
    (a.num*(b.den : ℤ)).natAbs.size ≤ u+v ∧ ((a.den : ℤ)*b.num).natAbs.size ≤ u+v ∧
    (a.num*b.num).natAbs.size ≤ u+v := by
  obtain ⟨_,_,left,right⟩ := KeyWidth.rational_comparison ha hb
  rw [Int.mul_comm b.num] at right
  refine ⟨?_,(size_mul_le ..).trans (Nat.add_le_add ha.2 hb.2),left,right,?_⟩
  · apply Nat.size_le.mpr
    rw [pow_succ]
    have h1 := Nat.size_le.mp left
    have h2 := Nat.size_le.mp right
    have hsum := Int.natAbs_add_le (a.num*(b.den : ℤ)) ((a.den : ℤ)*b.num)
    omega
  · rw [Int.natAbs_mul]
    exact (size_mul_le ..).trans (Nat.add_le_add ha.1 hb.1)

/-- Total arithmetic-slot charge in the project's binary model, for a
slot trace whose entries fit the proved stage width. -/
theorem selected_bit_charge (a : Input) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) :
    let L := Binary.lengthInput a
    (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).2 *
      (64*(2*inputStageWidth L+2)^3) ≤ inputStageBitCharge L :=
  Nat.mul_le_mul_right _ (selected_slots a toSite s hs)

end Kintali.QuotaSweep.OperandBounds
