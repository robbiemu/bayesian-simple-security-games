module

public import Kintali.LinearProgramming.SlackWindow
public import Kintali.LinearProgramming.BorderMinor
import Mathlib.Data.List.ProdSigma

/-!
# Constructing a pivot by single-row, single-column extensions

Start with the empty nonsingular minor. Test each selected row together with
each column for a nonsingular border. Every successful extension increases
the rank. At termination the bordered determinant identity shows that all
selected rows are represented by the lifted adjugate.
-/

@[expose] public section

namespace Kintali.LinearProgramming

open scoped BigOperators

variable {m n : ℕ}

structure Minor (m n : ℕ) where
  rank : ℕ
  rows : Fin rank → Fin m
  cols : Fin rank → Fin n

namespace Minor

def empty (m n : ℕ) : Minor m n := ⟨0, Fin.elim0, Fin.elim0⟩

def matrix (s : Minor m n) (P : System (Fin m) (Fin n)) :
    Matrix (Fin s.rank) (Fin s.rank) ℤ := P.coeff.submatrix s.rows s.cols

def extend (s : Minor m n) (i : Fin m) (j : Fin n) : Minor m n :=
  ⟨s.rank + 1, Fin.cons i s.rows, Fin.cons j s.cols⟩

theorem rank_le (s : Minor m n) (P : System (Fin m) (Fin n)) (reg : (s.matrix P).det ≠ 0) :
    s.rank ≤ n := by
  have inject : Function.Injective s.cols := by
    intro a b eq
    by_contra ne
    exact reg (Matrix.det_zero_of_column_eq ne (fun t => congrArg (P.coeff (s.rows t)) eq))
  simpa using Fintype.card_le_of_injective s.cols inject

def pairs (m n : ℕ) : List (Fin m × Fin n) := (List.finRange m).product (List.finRange n)

theorem pair_mem (p : Fin m × Fin n) : p ∈ pairs m n := by
  obtain ⟨i,j⟩ := p
  simp [pairs]

theorem pairs_length (m n : ℕ) : (pairs m n).length = m * n :=
  (List.length_product (List.finRange m) (List.finRange n)).trans (by simp)

def next? (s : Minor m n) (P : System (Fin m) (Fin n)) (active : Fin m → Bool) :
    Option (Fin m × Fin n) :=
  (pairs m n).find? fun p =>
    active p.1 && decide (determinant ((s.extend p.1 p.2).matrix P) ≠ 0)

theorem next_spec {s : Minor m n} {P : System (Fin m) (Fin n)} {active : Fin m → Bool}
    {p : Fin m × Fin n} (found : s.next? P active = some p) :
    active p.1 = true ∧ ((s.extend p.1 p.2).matrix P).det ≠ 0 := by
  have check := List.find?_some (p := fun t : Fin m × Fin n =>
    active t.1 && decide (determinant ((s.extend t.1 t.2).matrix P) ≠ 0)) found
  simpa using check

def Maximal (s : Minor m n) (P : System (Fin m) (Fin n)) (active : Fin m → Bool) : Prop :=
  ∀ i, active i = true → ∀ j, ((s.extend i j).matrix P).det = 0

theorem no_next {s : Minor m n} {P : System (Fin m) (Fin n)} {active : Fin m → Bool}
    (noneLeft : s.next? P active = none) : s.Maximal P active := by
  intro i inSet j
  have rejected := List.find?_eq_none.mp noneLeft (i,j) (pair_mem _)
  simpa [inSet] using rejected

def grow (P : System (Fin m) (Fin n)) (active : Fin m → Bool) :
    ℕ → Minor m n → Minor m n
  | 0, s => s
  | t + 1, s => match s.next? P active with
    | none => s
    | some (i,j) => grow P active t (s.extend i j)

private theorem grow_spec (P : System (Fin m) (Fin n)) (active : Fin m → Bool)
    (fuel : ℕ) (s : Minor m n) (regular : (s.matrix P).det ≠ 0)
    (selected : ∀ t, active (s.rows t) = true) (enough : n ≤ s.rank + fuel) :
    let r := grow P active fuel s
    (r.matrix P).det ≠ 0 ∧ (∀ t, active (r.rows t) = true) ∧ r.Maximal P active := by
  induction fuel generalizing s with
  | zero =>
    refine ⟨regular, selected, fun i _ j => ?_⟩
    by_contra nz
    have count := (s.extend i j).rank_le P nz
    change s.rank + 1 ≤ n at count
    omega
  | succ t ih =>
    rw [grow]
    cases found : s.next? P active with
    | none => exact ⟨regular, selected, no_next found⟩
    | some p =>
      obtain ⟨i,j⟩ := p
      obtain ⟨on, nz⟩ := next_spec found
      exact ih _ nz (fun k => Fin.cases on (fun l => selected l) k)
        (show n ≤ s.rank + 1 + t by omega)

def choose (P : System (Fin m) (Fin n)) (active : Fin m → Bool) : Minor m n :=
  grow P active n (empty m n)

theorem choose_spec (P : System (Fin m) (Fin n)) (active : Fin m → Bool) :
    let s := choose P active
    (s.matrix P).det ≠ 0 ∧ (∀ t, active (s.rows t) = true) ∧ s.Maximal P active :=
  grow_spec P active n _ (by simp [empty, matrix]) (fun t => t.elim0) (by simp [empty])

def selector (s : Minor m n) : Matrix (Fin n) (Fin s.rank) ℤ :=
  .of fun j t => if s.cols t = j then 1 else 0

theorem mul_selector (s : Minor m n) (P : System (Fin m) (Fin n)) :
    P.coeff * s.selector = P.coeff.submatrix id s.cols := by
  ext i t
  simp [Matrix.mul_apply, selector, mul_ite]

def adjugate {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  .of fun i j => determinant (M.updateRow j (Pi.single i 1))

@[simp] theorem adjugate_eq {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) : adjugate M = M.adjugate := by
  ext i j
  simp [adjugate, Matrix.adjugate_apply]

def pivot (s : Minor m n) (P : System (Fin m) (Fin n)) : Pivot m n s.rank where
  rows := s.rows
  lift := s.selector * adjugate (s.matrix P)
  den := determinant (s.matrix P)

theorem represented (s : Minor m n) (P : System (Fin m) (Fin n)) (active : Fin m → Bool)
    (regular : (s.matrix P).det ≠ 0) (terminal : s.Maximal P active) {i : Fin m}
    (inSet : active i = true) : (s.pivot P).Represents P i := by
  intro j
  let M := s.matrix P
  let v := fun t => P.coeff i (s.cols t)
  let u := fun t => P.coeff (s.rows t) j
  have block : (s.extend i j).matrix P = Border.matrix (P.coeff i j) v u M := by
    ext a b
    exact Fin.cases (Fin.cases rfl (fun _ => rfl) b)
      (fun _ => Fin.cases rfl (fun _ => rfl) b) a
  have identity : P.coeff i j * M.det - v ⬝ᵥ M.adjugate.mulVec u = 0 :=
    (Border.det_matrix (P.coeff i j) v u M regular).symm.trans
      ((congrArg Matrix.det block).symm.trans (terminal i inSet j))
  have weights : (s.pivot P).weights P = P.coeff.submatrix id s.cols * M.adjugate := by
    change P.coeff * (s.selector * adjugate M) = _
    rw [← Matrix.mul_assoc, s.mul_selector P, adjugate_eq]
  rw [weights, Matrix.mul_assoc]
  change determinant M * P.coeff i j =
    v ⬝ᵥ (fun t => (M.adjugate * P.coeff.submatrix s.rows id) t j)
  change determinant M * P.coeff i j = v ⬝ᵥ (M.adjugate.mulVec u)
  rw [determinant_eq, mul_comm]
  exact sub_eq_zero.mp identity

private theorem minorBound_le {a b h : ℕ} (le : a ≤ b) (hp : 0 < h) :
    minorBound a h ≤ minorBound b h :=
  Nat.mul_le_mul (Nat.factorial_le le) (Nat.pow_le_pow_right hp le)

theorem pivot_bounds (s : Minor m n) (P : System (Fin m) (Fin n)) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.coeff i j| ≤ (h : ℤ)) (regular : (s.matrix P).det ≠ 0) :
    |(s.pivot P).den| ≤ (SlackWindow.height n h : ℤ) ∧
    ∀ j t, |(s.pivot P).lift j t| ≤ (SlackWindow.height n h : ℤ) := by
  let M := s.matrix P
  let d := s.rank
  have dn : d ≤ n := s.rank_le P regular
  have dh := minorBound_le (Nat.le_succ_of_le dn) hp
  have B (N : Matrix (Fin d) (Fin d) ℤ) (entries : ∀ i j, |N i j| ≤ (h : ℤ)) :
      |determinant N| ≤ (minorBound d h : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast determinant_natAbs_le _ entries
  refine ⟨(B M (fun i j => coeff _ _)).trans (by exact_mod_cast dh), ?_⟩
  have one : (1 : ℤ) ≤ h := by exact_mod_cast hp
  have adj (t l : Fin d) : |adjugate M t l| ≤ (minorBound d h : ℤ) := by
    apply B
    intro i j
    by_cases il : l = i
    · subst i
      by_cases tj : t = j <;> simp [Matrix.updateRow_apply, tj, one]
    · simpa [M, matrix, Matrix.updateRow_apply, il, Ne.symm il] using coeff (s.rows i) (s.cols j)
  intro j t
  have big : d * minorBound d h ≤ SlackWindow.height n h := by
    calc
      _ ≤ (n + 1) * minorBound n h :=
        Nat.mul_le_mul (Nat.le_succ_of_le dn) (minorBound_le dn hp)
      _ ≤ (n + 1) * minorBound n h * h := Nat.le_mul_of_pos_right _ hp
      _ = _ := by simp [SlackWindow.height, minorBound, Nat.factorial_succ, pow_succ, Nat.mul_assoc]
  change |∑ l, s.selector j l * adjugate M l t| ≤ _
  calc
    _ ≤ ∑ l, |s.selector j l * adjugate M l t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin d, (minorBound d h : ℤ) := Finset.sum_le_sum fun l _ => by
      by_cases hit : s.cols l = j
      · simpa [selector, hit] using adj l t
      · simp [selector, hit]
    _ = ((d * minorBound d h : ℕ) : ℤ) := by simp
    _ ≤ _ := by exact_mod_cast big

end Minor

end Kintali.LinearProgramming
