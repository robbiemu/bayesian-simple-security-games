module

public import Kintali.InputOutput.Tables
public import Mathlib.Computability.Encoding
public import Mathlib.Data.Num.Lemmas

/-!
# Binary encoding length of the explicit tables

The wire format follows the [Formal Conjectures bitstring encoding](https://github.com/google-deepmind/formal-conjectures/blob/9bd16c570aed942e00ae000c7522dd42ebbb25eb/FormalConjecturesForMathlib/Computability/BitstringEncoding.lean)
by the Formal Conjectures Authors (Apache-2.0). Products delimit their first
field. Lists delimit each entry. Integers use positive and negative parts,
and rationals use their reduced numerator and positive denominator.
-/

@[expose] public section

namespace Kintali.InputOutput.Binary

open Computability

def block : List Bool → List Bool
  | [] => [false]
  | b :: rest => true :: b :: block rest

def pair {α β : Type} (a : α → List Bool) (b : β → List Bool) (p : α × β) :=
  block (a p.1) ++ b p.2

def many {α : Type} (encode : α → List Bool) (xs : List α) :=
  xs.flatMap (fun x => block (encode x))

def integer (z : ℤ) := pair encodeNat encodeNat (z.toNat, (-z).toNat)
def rational (q : ℚ) := pair integer encodeNat (q.num, q.den)
def payoff := pair rational rational
def attacker := pair rational (many payoff)
def input := pair encodeNat (pair (many payoff) (many attacker))
def output := pair (many rational) (many (many rational))

@[simp] theorem length_block (xs : List Bool) : (block xs).length = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [block, ih]; omega

@[simp] theorem length_pair {α β : Type} (a : α → List Bool) (b : β → List Bool) (p : α × β) :
    (pair a b p).length = 2 * (a p.1).length + 1 + (b p.2).length := by
  simp [pair]

theorem length_many {α : Type} (f : α → List Bool) (xs : List α) :
    (many f xs).length = (xs.map (fun x => 2 * (f x).length + 1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [many] at *

theorem count_le_many {α : Type} (f : α → List Bool) (xs : List α) : xs.length ≤ (many f xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [many] at *; omega

theorem entry_le_many {α : Type} (f : α → List Bool) {xs : List α} {x : α} (h : x ∈ xs) :
    (f x).length ≤ (many f xs).length := by
  induction xs with
  | nil => simp at h
  | cons y xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [many]; omega
    · have he := ih h
      simp [many] at *
      omega

private theorem pos_length (n : PosNum) : (encodePosNum n).length = n.natSize := by
  induction n with
  | one => rfl
  | bit0 n ih | bit1 n ih => simp [encodePosNum, PosNum.natSize, ih]

@[simp] theorem length_nat (n : ℕ) : (encodeNat n).length = n.size := by
  have aux (v : Num) : (encodeNum v).length = (v : ℕ).size := by
    cases v with
    | zero => rfl
    | pos v => exact (pos_length v).trans (PosNum.natSize_to_nat _)
  simpa [encodeNat] using aux (n : Num)

def lengthInput (a : Input) := (input a).length

theorem dimensions (a : Input) :
    a.targets ≤ lengthInput a ∧ a.types ≤ lengthInput a ∧ a.1.size ≤ lengthInput a := by
  have ht := count_le_many payoff a.2.1
  have hk := count_le_many attacker a.2.2
  simp only [lengthInput, input, length_pair, length_nat, Input.targets, Input.types]
  omega

theorem parts (q : ℚ) : q.num.natAbs.size ≤ (rational q).length ∧
    q.den.size ≤ (rational q).length := by
  simp only [rational, integer, length_pair, length_nat]
  cases h : q.num with
  | ofNat n => simp; omega
  | negSucc n => simp; omega

private theorem payoff_widths (p : Payoffs) :
    (rational p.1).length ≤ (payoff p).length ∧ (rational p.2).length ≤ (payoff p).length := by
  simp only [payoff, length_pair]
  omega

theorem defense_widths (a : Input) (j : Fin a.targets) :
    (rational (a.defense j).1).length ≤ lengthInput a ∧
    (rational (a.defense j).2).length ≤ lengthInput a := by
  have h := entry_le_many payoff (a.2.1.get_mem j)
  have hp := payoff_widths (a.defense j)
  change (payoff (a.defense j)).length ≤ _ at h
  simp only [lengthInput, input, length_pair]
  omega

private theorem row_width (a : Input) (i : Fin a.types) :
    (rational (a.prior i)).length + (many payoff (a.offers i)).length ≤ lengthInput a := by
  have h := entry_le_many attacker (a.2.2.get_mem i)
  simp only [Input.prior, Input.offers, attacker, length_pair, lengthInput, input] at *
  omega

theorem prior_width (a : Input) (i : Fin a.types) : (rational (a.prior i)).length ≤ lengthInput a :=
  (Nat.le_add_right ..).trans (row_width a i)

theorem attack_widths (a : Input) (h : a.Valid) (i : Fin a.types) (j : Fin a.targets) :
    (rational (a.attack i j).1).length ≤ lengthInput a ∧
    (rational (a.attack i j).2).length ≤ lengthInput a := by
  have hj : j.val < (a.offers i).length := by rw [((a.valid_iff).1 h).2 i]; exact j.isLt
  have mem : a.attack i j ∈ a.offers i := by simp [Input.attack, hj, List.getElem_mem]
  have he := entry_le_many payoff mem
  have hr := row_width a i
  have hp := payoff_widths (a.attack i j)
  omega


/-- A B-bit bound for each reduced part gives a bound for the entire encoded
compact strategy, including every nested list and product delimiter. -/
theorem rational_width {q : ℚ} {B : ℕ} (hn : q.num.natAbs.size ≤ B) (hd : q.den.size ≤ B) :
    (rational q).length ≤ 5 * B + 3 := by
  simp only [rational, integer, length_pair, length_nat]
  cases h : q.num with
  | ofNat n => simp [h] at hn ⊢; omega
  | negSucc n => simp [h] at hn ⊢; omega

private theorem many_width {α : Type} {f : α → List Bool} (xs : List α) {B : ℕ}
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (many f xs).length ≤ xs.length * (2*B+1) := by
  induction xs with
  | nil => simp [many]
  | cons x xs ih =>
    have head := h x (by simp)
    have tail := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [many, List.flatMap_cons, List.length_append, length_block, List.length_cons, Nat.succ_mul] at *
    omega

theorem strategy_width {k m B : ℕ} (s : Strategy k m)
    (hx : ∀ j, (s.coverage j).num.natAbs.size ≤ B ∧ (s.coverage j).den.size ≤ B)
    (ha : ∀ i j, (s.attacks i j).num.natAbs.size ≤ B ∧ (s.attacks i j).den.size ≤ B) :
    let row := m * (2*(5*B+3)+1)
    (output (writeStrategy s)).length ≤ 2*row + 1 + k*(2*row+1) := by
  have row (f : Fin m → ℚ) (h : ∀ j, (f j).num.natAbs.size ≤ B ∧ (f j).den.size ≤ B) :
      (many rational (List.ofFn f)).length ≤ m*(2*(5*B+3)+1) := by
    apply (many_width (f := rational) (List.ofFn f) (B := 5*B+3) ?_).trans
    · simp
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact rational_width (h j).1 (h j).2
  have rows := many_width (f := many rational) (List.ofFn fun i => List.ofFn (s.attacks i))
    (B := m*(2*(5*B+3)+1)) (fun xs h => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
      exact row _ (ha i))
  have cov := row _ hx
  simp only [List.length_ofFn] at rows
  simp only [output, writeStrategy, length_pair]
  omega

end Kintali.InputOutput.Binary
