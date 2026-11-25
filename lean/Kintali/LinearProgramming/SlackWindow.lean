module

public import Kintali.LinearProgramming.Rounding
import Mathlib.Tactic.FieldSimp

/-! # Selecting an empty interval among the row slacks

There are `m+1` disjoint intervals and `m` rows. The selection scans their
endpoints and handles ties using an open lower and a closed upper endpoint.
The inverse starting precision has polynomial binary length.
-/

@[expose] public section

namespace Kintali.LinearProgramming

namespace SlackWindow

variable {m n k h : ℕ}

def lower (e K : ℚ) (l : ℕ) : ℚ := e * K ^ l

def Empty (s : Fin m → ℚ) (e K : ℚ) (l : Fin (m + 1)) : Prop :=
  ∀ i, ¬(lower e K l < s i ∧ s i ≤ lower e K (l + 1))

instance (s : Fin m → ℚ) (e K : ℚ) (l : Fin (m + 1)) : Decidable (Empty s e K l) :=
  inferInstanceAs (Decidable (∀ i, ¬(lower e K l < s i ∧ s i ≤ lower e K (l + 1))))

theorem exists_empty (s : Fin m → ℚ) {e K : ℚ} (epos : 0 ≤ e) (Klarge : 1 ≤ K) :
    ∃ l, Empty s e K l := by
  classical
  by_contra! busy
  have occupied (l : Fin (m + 1)) : ∃ i, lower e K l < s i ∧ s i ≤ lower e K (l + 1) := by
    by_contra none
    exact busy l (fun i pair => none ⟨i, pair⟩)
  choose i hi using occupied
  have ordered {a b : Fin (m + 1)} (ab : a < b) : i a ≠ i b := by
    intro eq
    have mono : lower e K (a + 1) ≤ lower e K b :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ Klarge (show a.val + 1 ≤ b.val from ab)) epos
    have left := (hi b).1
    rw [← eq] at left
    exact (not_lt_of_ge ((hi a).2.trans mono)) left
  have inj : Function.Injective i := by
    intro a b eq
    rcases lt_trichotomy a b with h | h | h
    · exact (ordered h eq).elim
    · exact h
    · exact (ordered h eq.symm).elim
  have more := Fintype.card_le_of_injective i inj
  simp at more

def select (s : Fin m → ℚ) (e K : ℚ) : Fin (m + 1) :=
  ((List.finRange (m + 1)).find? fun l => decide (Empty s e K l)).getD 0

theorem select_empty (s : Fin m → ℚ) {e K : ℚ} (epos : 0 ≤ e) (Klarge : 1 ≤ K) :
    Empty s e K (select s e K) := by
  obtain ⟨l, hl⟩ := exists_empty s epos Klarge
  unfold select
  cases opt : (List.finRange (m + 1)).find? (fun l => decide (Empty s e K l)) with
  | none =>
    have hn := List.find?_eq_none.mp opt l (List.mem_finRange _)
    simp [hl] at hn
  | some w =>
    have good : decide (Empty s e K w) = true := List.find?_some (p := fun l => decide (Empty s e K l)) opt
    exact of_decide_eq_true good

/-- A uniform cofactor bound, valid for all pivot sizes up to `n`. -/
def height (n h : ℕ) : ℕ := minorBound (n + 1) h

def amplification (n h : ℕ) : ℕ := n * n * h * height n h

def radix (n h : ℕ) : ℕ := amplification n h + 2

def divisor (m n h : ℕ) : ℕ := height n h * radix n h ^ (m + 1)

def precision (m n h : ℕ) : ℚ := 1 / (divisor m n h : ℚ)

theorem divisor_pos (m n : ℕ) {h : ℕ} (positive : 0 < h) : 0 < divisor m n h :=
  Nat.mul_pos (minorBound_pos _ positive) (Nat.pow_pos (by simp [radix]))

theorem precision_pos (m n : ℕ) {h : ℕ} (positive : 0 < h) : 0 < precision m n h := by
  exact one_div_pos.mpr (by exact_mod_cast divisor_pos m n positive)

theorem separated (s : Fin m → ℚ) {e K : ℚ} (epos : 0 ≤ e) (Klarge : 1 ≤ K)
    (near : ∀ i, -e ≤ s i) (l : Fin (m + 1)) (empty : Empty s e K l) (i : Fin m) :
    |s i| ≤ lower e K l ∨ K * lower e K l < s i := by
  have grow : e ≤ lower e K l := by
    simpa [lower] using mul_le_mul_of_nonneg_left (one_le_pow₀ Klarge (n := (l : ℕ))) epos
  by_cases small : s i ≤ lower e K l
  · exact Or.inl (abs_le.mpr ⟨(neg_le_neg grow).trans (near i), small⟩)
  · right
    have out : lower e K (l + 1) < s i := lt_of_not_ge (fun le => empty i ⟨lt_of_not_ge small, le⟩)
    simpa [lower, pow_succ, mul_assoc, mul_left_comm, mul_comm] using out

theorem tiny (m n : ℕ) {h : ℕ} (positive : 0 < h) (l : Fin (m + 1)) :
    (height n h : ℚ) *
      (lower (precision m n h) (radix n h) l +
        (amplification n h : ℚ) * lower (precision m n h) (radix n h) l) < 1 := by
  let H : ℚ := height n h
  let K : ℚ := radix n h
  let e := precision m n h
  have Hp : 0 < H := by
    change (0 : ℚ) < (minorBound (n + 1) h : ℚ)
    exact_mod_cast minorBound_pos (n + 1) positive
  have Klarge : 1 ≤ K := by
    change (1 : ℚ) ≤ ((amplification n h + 2 : ℕ) : ℚ)
    exact_mod_cast (show 1 ≤ amplification n h + 2 by omega)
  have Kp : 0 < K := by linarith
  have ep : 0 < e := precision_pos m n positive
  have gap : 1 + (amplification n h : ℚ) < K := by dsimp [K, radix]; push_cast; linarith
  have geometric : (K ^ (l : ℕ)) ≤ K ^ m := pow_le_pow_right₀ Klarge (by omega)
  have last : H * K * (e * K ^ m) = 1 := by
    dsimp [e, precision, divisor, H, K]
    push_cast
    rw [pow_succ]
    field_simp [ne_of_gt (show (0 : ℚ) < height n h from Hp),
      ne_of_gt (show (0 : ℚ) < radix n h from Kp)]
  change H * (e * K ^ (l : ℕ) + (amplification n h : ℚ) * (e * K ^ (l : ℕ))) < 1
  calc
    _ = H * (1 + (amplification n h : ℚ)) * (e * K ^ (l : ℕ)) := by ring
    _ < H * K * (e * K ^ (l : ℕ)) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left gap Hp) (mul_pos ep (pow_pos Kp _))
    _ ≤ H * K * (e * K ^ m) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left geometric ep.le) (mul_nonneg Hp.le Kp.le)
    _ = 1 := last

theorem divisor_size (m n h : ℕ) :
    (divisor m n h).size ≤ (height n h).size + (1 + (m + 1) * (radix n h).size) :=
  (StochasticGames.BinarySize.size_mul_le _ _).trans
    (Nat.add_le_add_left (power_size_le _ _) _)

end SlackWindow

end Kintali.LinearProgramming
