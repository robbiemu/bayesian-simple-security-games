module

public import Kintali.InputOutput.CodecWork
public import Kintali.ContactSize.Rational

/-! # Reading public payoff tables in the direct cases

The endpoint best response compares two stored rational payoffs by cross
multiplication. Reading a table entry pays for traversing each list prefix.
-/

@[expose] public section

namespace Kintali.InputOutput.DirectWork

open Binary StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize

def width (S : ℕ) := 2*S+4

def indices {α : Type} (xs : List α) : Run (List (Fin xs.length)) :=
  let n := StochasticGames.CompilerRun.length xs
  let js := finRange n.value
  ⟨length_value xs ▸ js.value, n.work.seq js.work⟩

@[simp] theorem indices_value {α : Type} (xs : List α) : (indices xs).value = List.finRange xs.length := by
  have aux (n m : ℕ) (h : n = m) : h ▸ (finRange n).value = List.finRange m := by
    subst m; exact finRange_value _
  exact aux _ _ (length_value xs)

theorem indices_work {α : Type} (xs : List α) {S : ℕ} (h : xs.length ≤ S) :
    (indices xs).Bound (3*S+2) (width S) := by
  have n := length_bound xs
  have js := finRange_bound xs.length
  have size := (size_le_self _).trans h
  simp only [indices,Run.Bound,Work.seq,width] at *
  rw [length_value xs]
  omega

def atD {α : Type} (fallback : α) : List α → ℕ → Run α
  | [], _ => step 0 fallback
  | a::_, 0 => step 0 a
  | _::as, n+1 => do
    let j ← step (n+1).size n
    atD fallback as j

@[simp] theorem atD_value {α : Type} (fallback : α) (xs : List α) (i : ℕ) :
    (atD fallback xs i).value = xs[i]?.getD fallback := by
  induction xs generalizing i with
  | nil => rfl
  | cons a as ih => cases i <;> simp [atD,ih]

theorem atD_work {α : Type} (fallback : α) (xs : List α) (i : ℕ) :
    (atD fallback xs i).Bound (i+1) i.size := by
  induction xs generalizing i with
  | nil => exact (bound_step _ _).weaken (by omega) (Nat.zero_le _)
  | cons a as ih =>
    cases i with
    | zero => exact bound_step _ _
    | succ i =>
      have h := ih i
      have m := Nat.size_le_size (Nat.le_succ i)
      simp [atD,Run.Bound] at *
      omega

def offer (a : Input) (i : Fin a.types) (j : Fin a.targets) : Run Payoffs := do
  let row ← get a.2.2 i
  atD (0,0) row.2 j.val

@[simp] theorem offer_value (a : Input) (i : Fin a.types) (j : Fin a.targets) :
    (offer a i j).value = a.attack i j := by
  simp only [offer,Run.bind_value,atD_value,Input.attack,Input.offers]
  rw [get_value a.2.2 i]

theorem offer_work (a : Input) (i : Fin a.types) (j : Fin a.targets) :
    (offer a i j).Bound (2*lengthInput a+2) (width (lengthInput a)) := by
  let S := lengthInput a
  have h := dimensions a
  have isize := (size_le_self i.val).trans (i.isLt.le.trans h.2.1)
  have jsize := (size_le_self j.val).trans (j.isLt.le.trans h.1)
  have row := get_bound a.2.2 i
  have col := atD_work ((0,0) : Payoffs) (a.2.2.get i).2 j.val
  simp only [offer,Run.Bound,Run.bind_width,Run.bind_slots,width] at *
  rw [get_value a.2.2 i]
  have := i.isLt
  have := j.isLt
  omega

/-- Decide strict order, explicitly charging both signed cross products. -/
def less (q r : ℚ) : Run Bool := do
  let l ← intMul q.num r.den
  let u ← intMul r.num q.den
  step (max l.natAbs.size u.natAbs.size+1) (decide (l < u))

@[simp] theorem less_value (q r : ℚ) : (less q r).value = decide (q < r) := by
  change decide (q.num * (r.den : ℤ) < r.num * (q.den : ℤ)) = decide (q < r)
  exact decide_eq_decide.mpr (Rat.lt_iff q r).symm

theorem less_work (q r : ℚ) {S : ℕ} (hq : Fits S q) (hr : Fits S r) : (less q r).Bound 3 (width S) := by
  have l := size_mul_le q.num.natAbs r.den
  have u := size_mul_le r.num.natAbs q.den
  simp only [less,Run.Bound,Run.bind_width,Run.bind_slots,intMul,
    step_width,step_slots,step_value,Int.natAbs_mul,Int.natAbs_natCast,width,Fits] at *
  omega

private theorem fits_of_field (q : ℚ) {S : ℕ} (h : (rational q).length ≤ S) : Fits S q :=
  ⟨(parts q).1.trans h,(parts q).2.trans h⟩

theorem offer_fits (a : Input) (valid : a.Valid) (i : Fin a.types) (j : Fin a.targets) :
    Fits (lengthInput a) (a.attack i j).1 ∧ Fits (lengthInput a) (a.attack i j).2 :=
  ⟨fits_of_field _ (attack_widths a valid i j).1,fits_of_field _ (attack_widths a valid i j).2⟩

def gainPositive (a : Input) (j : Fin a.targets) : Run Bool := do
  let p ← get a.2.1 j
  less p.1 p.2

@[simp] theorem gainPositive_value (a : Input) (j : Fin a.targets) :
    (gainPositive a j).value = decide (0 < a.game.gain j) := by
  simp only [gainPositive,Run.bind_value,less_value,Input.game,Input.defense]
  rw [get_value a.2.1 j]
  simp

theorem gainPositive_work (a : Input) (j : Fin a.targets) :
    (gainPositive a j).Bound (lengthInput a+4) (width (lengthInput a)) := by
  have dim := (dimensions a).1
  have small := j.isLt.le.trans dim
  have size := (size_le_self j.val).trans small
  have g := get_bound a.2.1 j
  have h := defense_widths a j
  have c := less_work _ _ (fits_of_field _ h.1) (fits_of_field _ h.2)
  change (less (a.2.1.get j).1 (a.2.1.get j).2).Bound 3 (width (lengthInput a)) at c
  simp only [gainPositive,Run.Bound,Run.bind_slots,Run.bind_width,width] at *
  rw [get_value a.2.1 j]
  omega

end Kintali.InputOutput.DirectWork
