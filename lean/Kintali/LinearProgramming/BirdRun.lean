module

public import Kintali.LinearProgramming.ArithmeticRun
public import Kintali.LinearProgramming.Bird
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Charged execution of Bird's determinant recurrence

Each address lookup, comparison, signed arithmetic operation, and stored array
cell is charged in the binary word model. The two dot products share the
stored input and previous-stage tables.
-/

@[expose] public section

namespace Kintali.LinearProgramming.BirdRun

open scoped BigOperators
open StochasticGames.CompilerRun
open Kintali.LinearProgramming

variable {n : ℕ}

def read (T : Bird.Table n) (i j : Fin n) : Run ℤ := do
  let row ← step n.size T[i.val]
  step n.size row[j.val]

/-- One comparison and two address reads. The fixed evaluation schedule
also charges the reads when the comparison masks the resulting term. -/
def diagTerm (F : Bird.Table n) (i k : Fin n) : Run ℤ :=
  ⟨if i < k then Bird.entries F k k else 0, ⟨3, n.size⟩⟩

/-- One comparison, four address reads, and a signed multiplication. -/
def rowTerm (A F : Bird.Table n) (i j k : Fin n) : Run ℤ :=
  let x := Bird.entries F i k
  let y := Bird.entries A k j
  ⟨if i < k then x * y else 0, ⟨6, max n.size (max x.natAbs.size y.natAbs.size + 1)⟩⟩

def entry (A F : Bird.Table n) (i j : Fin n) : Run ℤ := do
  let indices ← finRange n
  let diagonal ← ArithmeticRun.sum (diagTerm F i) indices
  let tail ← ArithmeticRun.sum (rowTerm A F i j) indices
  let a ← read A i j
  let d ← intMul diagonal a
  intSub tail d

@[simp] theorem read_value (T : Bird.Table n) (i j : Fin n) :
    (read T i j).value = Bird.entries T i j := rfl

@[simp] theorem diagTerm_value (F : Bird.Table n) (i k : Fin n) :
    (diagTerm F i k).value = if i < k then Bird.entries F k k else 0 := rfl

@[simp] theorem rowTerm_value (A F : Bird.Table n) (i j k : Fin n) :
    (rowTerm A F i j k).value =
      if i < k then Bird.entries F i k * Bird.entries A k j else 0 := rfl

private theorem tail_sum (i : Fin n) (f : Fin n → ℤ) :
    ((List.finRange n).map (fun k => if i < k then f k else 0)).sum =
      ∑ k ∈ Finset.Ioi i, f k := by
  rw [← Fin.sum_univ_def, ← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

@[simp] theorem entry_value (A F : Bird.Table n) (i j : Fin n) :
    (entry A F i j).value = BirdDet.Spec.stepEntry (Bird.entries A) (Bird.entries F) i j := by
  simp only [entry, Run.bind_value, finRange_value, ArithmeticRun.sum_value, diagTerm_value,
    rowTerm_value, read_value, intMul, intSub, step_value, tail_sum, BirdDet.Spec.stepEntry_eq,
    Matrix.of_apply]
  ring

private theorem read_bound (T : Bird.Table n) (i j : Fin n) {w : ℕ} (width : n.size ≤ w) :
    (read T i j).Bound 2 w := ⟨le_rfl, by simpa [read] using width⟩

private theorem word_abs {a : ℤ} {B : ℕ} (h : |a| ≤ (B : ℤ)) : a.natAbs ≤ B := by
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

/-- At stage height `b`, all words used by this entry fit the signed width
of `(n+1)(h+1)(b+1)` or the dimension's address width. -/
def stageWidth (n h b : ℕ) : ℕ := n.size + ((n+1)*(h+1)*(b+1)).size + 2

theorem entry_bound {h b : ℕ} (A F : Bird.Table n) (i j : Fin n)
    (input : ∀ u v, |Bird.entries A u v| ≤ (h : ℤ)) (prior : ∀ u v, |Bird.entries F u v| ≤ (b : ℤ)) :
    (entry A F i j).Bound (24*(n+1)) (stageWidth n h b) := by
  let cap := (n+1)*(h+1)*(b+1)
  let w := stageWidth n h b
  have indexWidth : n.size ≤ w := by dsimp [w, stageWidth]; omega
  have capWidth {T : ℕ} (hc : T ≤ cap) : T.size+1 ≤ w := by
    have := Nat.size_le_size hc
    dsimp only [w, stageWidth, cap] at *
    omega
  have triple {x y z : ℕ} (hx : x ≤ n+1) (hy : y ≤ h+1) (hz : z ≤ b+1) :
      x*y*z ≤ cap := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
  have bb : b ≤ cap := by simpa using triple (x := 1) (y := 1) (z := b) (by omega) (by omega) (by omega)
  have hh : h ≤ cap := by simpa using triple (x := 1) (y := h) (z := 1) (by omega) (by omega) (by omega)
  have nb : (n+1)*b ≤ cap := by simpa using triple (x := n+1) (y := 1) (z := b) le_rfl (by omega) (by omega)
  have nbh : (n+1)*(b*h) ≤ cap := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      triple (x := n+1) (y := h) (z := b) le_rfl (by omega) (by omega)
  have dm (k : Fin n) : (diagTerm F i k).value.natAbs ≤ b := by
    rw [diagTerm_value]
    split
    · exact word_abs (prior _ _)
    · exact Nat.zero_le _
  have rm (k : Fin n) : (rowTerm A F i j k).value.natAbs ≤ b*h := by
    rw [rowTerm_value]
    split
    · rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (word_abs (prior ..)) (word_abs (input ..))
    · exact Nat.zero_le _
  have dc (k : Fin n) : (diagTerm F i k).Bound 3 w := ⟨le_rfl, indexWidth⟩
  have rc (k : Fin n) : (rowTerm A F i j k).Bound 6 w := by
    have left := capWidth ((word_abs (prior i k)).trans bb)
    have right := capWidth ((word_abs (input k j)).trans hh)
    exact ⟨le_rfl, max_le indexWidth (by omega)⟩
  let xs := List.finRange n
  have count : xs.length ≤ n := by simp [xs]
  have dia := ArithmeticRun.sum_bound (n := n) _ dm dc (capWidth nb) xs count
  have tail := ArithmeticRun.sum_bound (n := n) _ rm rc (capWidth nbh) xs count
  let d := (ArithmeticRun.sum (diagTerm F i) xs).value
  let r := (ArithmeticRun.sum (rowTerm A F i j) xs).value
  let a := Bird.entries A i j
  have da : d.natAbs ≤ n*b := (ArithmeticRun.sum_magnitude _ dm xs).trans
    (Nat.mul_le_mul_right _ count)
  have ra : r.natAbs ≤ n*(b*h) := (ArithmeticRun.sum_magnitude _ rm xs).trans
    (Nat.mul_le_mul_right _ count)
  have aa : a.natAbs ≤ h := word_abs (input i j)
  have dn : d.natAbs ≤ cap := da.trans ((Nat.mul_le_mul_right _ (Nat.le_succ n)).trans nb)
  have rn : r.natAbs ≤ cap := ra.trans ((Nat.mul_le_mul_right _ (Nat.le_succ n)).trans nbh)
  have product : (d*a).natAbs ≤ cap := by
    rw [Int.natAbs_mul]
    have tripleBound := triple (x := n) (y := h) (z := b) (by omega) (by omega) (by omega)
    exact (Nat.mul_le_mul da aa).trans (by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using tripleBound)
  have cw {u v : ℤ} (hu : u.natAbs ≤ cap) (hv : v.natAbs ≤ cap) :
      max u.natAbs.size v.natAbs.size + 1 ≤ w := by
    obtain hu' := capWidth hu
    obtain hv' := capWidth hv
    omega
  have mulWork : (intMul d a).Bound 1 w := ⟨le_rfl, cw dn (aa.trans hh)⟩
  have subWork : (intSub r (d*a)).Bound 1 w := ⟨le_rfl, cw rn product⟩
  have reading := read_bound A i j indexWidth
  have ranging := (finRange_bound n).weaken le_rfl indexWidth
  constructor
  · simp only [entry, Run.bind_slots, finRange_value, read_value, intMul, intSub, step_value, step_slots]
    have rr := ranging.1
    have dd := dia.1
    have tt := tail.1
    have aa' := reading.1
    simp only [xs, List.length_finRange] at dd tt
    omega
  · simp only [entry, Run.bind_width, finRange_value, read_value, intMul, intSub, step_value,
      step_width, max_le_iff]
    exact ⟨ranging.2, dia.2, tail.2, reading.2, mulWork.2, subWork.2⟩

def stage (A F : Bird.Table n) : Run (Bird.Table n) :=
  ArithmeticRun.tabulate n (fun i => ArithmeticRun.tabulate n (entry A F i))

@[simp] theorem stage_value (A F : Bird.Table n) :
    (stage A F).value = Bird.tabulate (BirdDet.Spec.stepEntry (Bird.entries A) (Bird.entries F)) := by
  simp [stage, Bird.tabulate]

theorem stage_bound {h b : ℕ} (A F : Bird.Table n)
    (input : ∀ u v, |Bird.entries A u v| ≤ (h : ℤ)) (prior : ∀ u v, |Bird.entries F u v| ≤ (b : ℤ)) :
    (stage A F).Bound (32*(n+1)^3) (stageWidth n h b) := by
  have ind : n.size ≤ stageWidth n h b := by unfold stageWidth; omega
  have hrun := ArithmeticRun.tabulate_bound _ ind (fun i =>
    ArithmeticRun.tabulate_bound _ ind (entry_bound A F i · input prior))
  exact hrun.weaken (by ring_nf; omega) le_rfl

end Kintali.LinearProgramming.BirdRun
