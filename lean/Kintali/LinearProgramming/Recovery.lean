module

public import Kintali.LinearProgramming.PivotSelection
import all StochasticGames.BoundedLinearProgram

/-!
# Exact recovery of a supplied near-feasible point

`System.recover_feasible` is the external theorem. Its hypotheses are an
integer coefficient bound and an explicit residual bound at the supplied
rational point. The procedure searches slack intervals and bordered
minors, with no call to an LP solver.
-/

@[expose] public section

namespace Kintali.LinearProgramming.System

open SlackWindow

variable {m n : ℕ} (P : System (Fin m) (Fin n))

def cutoff (h : ℕ) (x : Fin n → ℚ) : ℚ :=
  let e := precision m n h
  let K : ℚ := radix n h
  lower e K (select (P.slack x) e K)

def nearlyTight (h : ℕ) (x : Fin n → ℚ) (i : Fin m) : Bool :=
  decide (|P.slack x i| ≤ P.cutoff h x)

def recover (h : ℕ) (x : Fin n → ℚ) : Fin n → ℚ :=
  ((Minor.choose P (P.nearlyTight h x)).pivot P).repair P x

theorem recover_feasible (h : ℕ) (x : Fin n → ℚ) (positive : 0 < h)
    (coeff : ∀ i j, |P.coeff i j| ≤ (h : ℤ))
    (approximate : ∀ i, -(precision m n h) ≤ P.slack x i) :
    P.Feasible (P.recover h x) := by
  let e := precision m n h
  let K : ℚ := radix n h
  let l := select (P.slack x) e K
  let a := lower e K l
  let g := height n h
  let s := Minor.choose P (P.nearlyTight h x)
  have ep : 0 < e := precision_pos m n positive
  have Kbig : 1 ≤ K := by
    change (1 : ℚ) ≤ ((amplification n h + 2 : ℕ) : ℚ)
    exact_mod_cast (show 1 ≤ amplification n h + 2 by omega)
  have an : 0 ≤ a := mul_nonneg ep.le (pow_nonneg (by linarith : 0 ≤ K) _)
  obtain ⟨reg, active, terminal⟩ := Minor.choose_spec P (P.nearlyTight h x)
  have regS : (s.matrix P).det ≠ 0 := reg
  obtain ⟨dBound, liftBound⟩ := s.pivot_bounds P positive coeff regS
  have count := s.rank_le P regS
  have le : s.rank * n * h * g ≤ amplification n h :=
    Nat.mul_le_mul_right g (Nat.mul_le_mul_right h (Nat.mul_le_mul_right n count))
  have ratio : ((s.rank * n * h * g : ℕ) : ℚ) ≤ (amplification n h : ℚ) := by exact_mod_cast le
  have enlarged : ((s.rank * n * h * g : ℕ) : ℚ) * a ≤ (amplification n h : ℚ) * a :=
    mul_le_mul_of_nonneg_right ratio an
  apply (s.pivot P).repair_feasible P x (h := h) (g := g) (a := a)
  · simpa [Minor.pivot] using regS
  · exact coeff
  · exact liftBound
  · exact dBound
  · intro t
    exact of_decide_eq_true (active t)
  · intro i close
    exact s.represented P _ regS terminal (i := i) (decide_eq_true close)
  · intro i
    rcases separated (P.slack x) ep.le Kbig approximate l
      (select_empty _ ep.le Kbig) i with close | far
    · exact Or.inl close
    · have Kge : (amplification n h : ℚ) ≤ K := by
        change (amplification n h : ℚ) ≤ ((amplification n h + 2 : ℕ) : ℚ)
        exact_mod_cast (show amplification n h ≤ amplification n h + 2 by omega)
      exact Or.inr (enlarged.trans ((mul_le_mul_of_nonneg_right Kge an).trans far.le))
  · exact (mul_le_mul_of_nonneg_left (add_le_add (le_refl a) enlarged) (by positivity : (0 : ℚ) ≤ g)).trans_lt
      (tiny m n positive l)

/-- A rowwise residual bound for the original rational input. Each tolerance
is divided by the positive multiplier actually used to clear its row. -/
theorem recover_rational_feasible (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (h : ℕ) (x : Fin n → ℚ) (positive : 0 < h)
    (coeff : ∀ i j, |(ofRational A b).coeff i j| ≤ (h : ℤ))
    (approximate : ∀ i, A.mulVec x i ≤ b i + precision m n h / rowScale (A i) (b i)) :
    StochasticGames.BoundedLinearProgram.Feasible A b ((ofRational A b).recover h x) := by
  apply (feasible_ofRational_iff ..).mp
  apply recover_feasible _ _ x positive coeff
  intro i
  rw [slack, ofRational_mulVec, ofRational_rhs]
  let D : ℚ := rowScale (A i) (b i)
  have pos : 0 < D := by
    change (0 : ℚ) < (rowScale (A i) (b i) : ℚ)
    exact_mod_cast rowScale_pos (A i) (b i)
  have inequality : A.mulVec x i - b i ≤ precision m n h / D := by linarith [approximate i]
  have multiplied := (le_div_iff₀ pos).mp inequality
  change _ ≤ D * _ - D * _
  linarith only [multiplied]

end Kintali.LinearProgramming.System
