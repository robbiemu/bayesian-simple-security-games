module

public import Kintali.QuotaSweep.KeyWidth
public import Kintali.ContactSize.Sweep
public import StochasticGames.CompilationCost
import Mathlib.Tactic.Linarith

/-!
# Exact arithmetic inside a materialized quota stage

Assume the input parameters and the current stored state fit in `u` bits.
The following estimates cover every partial sum of the graph flow,
per-record changes, candidate times, the budget stop, both trial updates,
and the private comparison after the trial update. Common-denominator
bounds for the stored states can therefore be applied independently at
each stage.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep.OperandBounds

open Kintali.ContactSize
open StochasticGames.BinarySize

def sumWidth (n w : ℕ) := 1+n*(w+1)
def rateWidth (n u : ℕ) := sumWidth n (n+u+2)
def changeWidth (n u : ℕ) := 2*sumWidth n (rateWidth n u)+1
def eventWidth (n u : ℕ) := 2*u+1+rateWidth n u
def budgetWidth (n u : ℕ) := u+sumWidth n u+1+sumWidth n (changeWidth n u)
def advanceWidth (n u : ℕ) := u+(eventWidth n u+budgetWidth n u)+(changeWidth n u+1)+1
def stageWidth (n u : ℕ) := 1+advanceWidth n u+sumWidth n (advanceWidth n u)

private theorem sub_fits {a b : ℚ} {u v : ℕ} (ha : Fits u a) (hb : Fits v b) :
    Fits (u+v+1) (a-b) := by simpa [sub_eq_add_neg] using ha.add (KeyWidth.fits_neg hb)

private theorem partial_sum {A : Type*} (s : Finset A) {n u : ℕ} (hs : s.card ≤ n) (f : A → ℚ)
    (h : ∀ a ∈ s, Fits u (f a)) : Fits (sumWidth n u) (∑ a ∈ s, f a) :=
  (Fits.sum s f h).mono (Nat.add_le_add_left (Nat.mul_le_mul_right _ hs) 1)

private theorem visits_count {V : Type*} [DecidableEq V] (next : V → Option V) (dest : V)
    (n : ℕ) (u : Option V) : (Routing.visits next dest n u).1 ≤ n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => cases u with
    | none => simp [Routing.visits]
    | some a =>
      by_cases ha : a = dest
      · subst a; simpa [Routing.visits,Nat.add_comm] using Nat.succ_le_succ (ih (next dest))
      · simpa [Routing.visits,ha] using (ih (next a)).trans (Nat.le_succ _)

theorem route_partial {V : Type*} [DecidableEq V] [Fintype V] (next : V → Option V)
    (inject : V → ℚ) {u : ℕ} (hi : ∀ a, Fits u (inject a)) (v : V) (s : Finset V) :
    Fits (rateWidth (Fintype.card V) u)
      (∑ a ∈ s, ((Routing.visits next v (Fintype.card (Option V)) (some a)).1 : ℚ) * inject a) := by
  apply partial_sum s (Finset.card_le_univ _)
  intro a _
  have hc := (size_le_self _).trans (visits_count next v (Fintype.card (Option V)) (some a))
  exact ((Fits.natCast _).mul (hi a)).mono (by rw [Fintype.card_option] at *; omega)

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] (K : Book B S E)

theorem through_fits {P : Parameters B S} {u : ℕ} (inputs : ParametersFit u P)
    (x : Record B S E → ℚ) (v : Vertex B S) : Fits (rateWidth (Fintype.card (Vertex B S)) u)
      (K.through x P.rate v) := by
  unfold Book.through
  split
  · obtain he | he := K.aroundCycle_zero_or_one x v
    · rw [he]; exact Fits.zero.mono (by simp [rateWidth,sumWidth])
    · rw [he]; exact Fits.one.mono (by simp [rateWidth,sumWidth])
  · rw [← Routing.measuredPath_value, Routing.measuredPath, Prod.fst_sum]
    apply route_partial
    rintro (b | s)
    · exact Fits.zero.mono inputs.upper.pos
    · exact inputs.rate s

theorem change_fits {P : Parameters B S} {u : ℕ} (inputs : ParametersFit u P)
    (x : Record B S E → ℚ) (e : Record B S E) : Fits (changeWidth (Fintype.card (Vertex B S)) u)
      (K.direction x (K.through x P.rate) e) := by
  let n := Fintype.card (Vertex B S)
  let w := rateWidth n u
  have zero : Fits w 0 := Fits.zero.mono (by simp [w,rateWidth,sumWidth])
  have hcS : Fintype.card S ≤ n := by simp [n]
  have hcB : Fintype.card B ≤ n := by simp [n]
  have ha : Fits (sumWidth n w) (K.received x (K.through x P.rate) e) := by
    apply partial_sum Finset.univ (by simpa using hcS)
    intro s _; split
    · exact through_fits K inputs x _
    · exact zero
  have hb : Fits (sumWidth n w) (K.released x (K.through x P.rate) e) := by
    apply partial_sum Finset.univ (by simpa using hcB)
    intro b _; split
    · exact through_fits K inputs x _
    · exact zero
  exact (sub_fits ha hb).mono (by change _ ≤ 2*sumWidth n w+1; omega)

omit [DecidableEq B] [DecidableEq S] [DecidableEq E] in
theorem outside_fits {u : ℕ} {x : Record B S E → ℚ} (hold : ∀ e, Fits u (x e)) (p : Finset B) :
    Fits (sumWidth (Fintype.card (Vertex B S)) u) (Book.privateOutside p x) :=
  partial_sum p ((Finset.card_le_univ _).trans (by simp)) _ (fun b _ => hold (outside b))

theorem candidate_fits {P : Parameters B S} {u : ℕ} (inputs : ParametersFit u P)
    (z : State B S E) (hold : ∀ e, Fits u (z.allocation e)) {d : ℚ}
    (h : d ∈ K.exhaustions z.allocation P.rate) :
    Fits (u+rateWidth (Fintype.card (Vertex B S)) u) d := by
  obtain ⟨b,_,rfl⟩ := K.mem_exhaustions.mp h
  exact (hold _).div (through_fits K inputs _ _)

theorem duration_fits {P : Parameters B S} {u : ℕ} (inputs : ParametersFit u P)
    (z : State B S E) (pressure : Fits u z.pressure) (hold : ∀ e, Fits u (z.allocation e)) :
    Fits (eventWidth (Fintype.card (Vertex B S)) u) (K.duration z.allocation P.rate z.pressure P.upper) := by
  let d := K.duration z.allocation P.rate z.pressure P.upper
  have h : d ∈ K.times z.allocation P.rate z.pressure P.upper := K.duration_mem ..
  have hdrop (hb : d ∈ K.exhaustions z.allocation P.rate) :=
    (candidate_fits K inputs z hold hb).mono (show u+_ ≤ eventWidth (Fintype.card (Vertex B S)) u by
      dsimp [eventWidth]; omega)
  by_cases hc : K.hasCycle z.allocation = true
  · exact hdrop (by simpa [Book.times,hc] using h)
  · rw [Book.times,ite_eq_right hc,Finset.mem_insert] at h
    rcases h with hd | hd
    · change Fits _ d
      rw [hd]
      exact (sub_fits inputs.upper pressure).mono (by dsimp [eventWidth]; omega)
    · exact hdrop hd

theorem budget_fits {P : Parameters B S} {u : ℕ} (inputs : ParametersFit u P)
    (z : State B S E) (hold : ∀ e, Fits u (z.allocation e)) :
    Fits (budgetWidth (Fintype.card (Vertex B S)) u) (K.budgetTime P z) := by
  have ho := outside_fits (S := S) hold P.privateBuyers
  have hs := outside_fits (S := S) (change_fits K inputs z.allocation) P.privateBuyers
  exact (sub_fits inputs.target ho).div hs

theorem segment_fits {P : Parameters B S} {u : ℕ} (inputs : ParametersFit u P)
    (z : State B S E) (pressure : Fits u z.pressure) (hold : ∀ e, Fits u (z.allocation e))
    (δ : ℚ) (hδ : δ = K.duration z.allocation P.rate z.pressure P.upper ∨ δ = K.budgetTime P z) :
    let n := Fintype.card (Vertex B S)
    Fits (advanceWidth n u) (K.segment P z δ).pressure ∧
    (∀ e, Fits (advanceWidth n u) ((K.segment P z δ).allocation e)) ∧
    Fits (sumWidth n (advanceWidth n u)) (Book.privateOutside P.privateBuyers (K.segment P z δ).allocation) := by
  let n := Fintype.card (Vertex B S)
  have hδf : Fits (eventWidth n u+budgetWidth n u) δ := by
    rcases hδ with rfl | rfl
    · exact (duration_fits K inputs z pressure hold).mono (Nat.le_add_right ..)
    · exact (budget_fits K inputs z hold).mono (Nat.le_add_left ..)
  have hf (e) : Fits (advanceWidth n u) ((K.segment P z δ).allocation e) := by
    rw [Book.segment,K.snapshot_eq]
    exact ((hold e).add (hδf.mul (change_fits K inputs _ e))).mono (by dsimp [advanceWidth,n] at *; omega)
  have hs : Fits 1 (K.speed z.allocation) := by
    unfold Book.speed; split; exact Fits.zero; exact Fits.one
  exact ⟨(pressure.add (hδf.mul hs)).mono (by dsimp [advanceWidth,n] at *; omega),hf,
    outside_fits (S := S) hf P.privateBuyers⟩

/-- In the project's schoolbook multiplication/division and Euclidean
normalization cost model, one rational operation on two `b`-bit inputs
has a `2b+2`-bit slot for the intermediate products and their sum. -/
theorem scalarBitCost_bound (b a c : ℕ) (hc : c.size ≤ 2*b+2) :
    StochasticGames.CompilationCost.rationalBitCost (2*b+2) a c ≤ 64*(2*b+2)^3 :=
  StochasticGames.CompilationCost.rationalBitCost_le (by omega) hc

end Kintali.QuotaSweep.OperandBounds
