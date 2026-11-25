module

public import Kintali.LinearProgramming.PivotRun
public import Kintali.LinearProgramming.RationalBounds

/-! # Charged integer dot products and positive powers for recovery -/

@[expose] public section

namespace Kintali.LinearProgramming.ScalarRun

open StochasticGames.CompilerRun

variable {n : ℕ}

theorem absWord {x : ℤ} {H : ℕ} (h : |x| ≤ (H : ℤ)) : x.natAbs ≤ H := by
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

theorem signedWidth {u v : ℤ} {U V w : ℕ} (hu : u.natAbs ≤ U) (hv : v.natAbs ≤ V)
    (ub : U.size+1 ≤ w) (vb : V.size+1 ≤ w) : max u.natAbs.size v.natAbs.size + 1 ≤ w := by
  have := Nat.size_le_size hu
  have := Nat.size_le_size hv
  omega

def dot (a b : Fin n → Run ℤ) : Run ℤ := do
  let xs ← finRange n
  ArithmeticRun.sum (fun k => do
    let u ← a k
    let v ← b k
    intMul u v) xs

@[simp] theorem dot_value (a b : Fin n → Run ℤ) :
    (dot a b).value = (fun i => (a i).value) ⬝ᵥ (fun i => (b i).value) := by
  simp only [dot, Run.bind_value, finRange_value, ArithmeticRun.sum_value, intMul, step_value,
    ← Fin.sum_univ_def, dotProduct]

theorem dot_bound (a b : Fin n → Run ℤ) {U V ucost vcost w : ℕ}
    (au : ∀ i, (a i).value.natAbs ≤ U) (bv : ∀ i, (b i).value.natAbs ≤ V)
    (ac : ∀ i, (a i).Bound ucost w) (bc : ∀ i, (b i).Bound vcost w)
    (indices : n.size ≤ w) (hu : U.size+1 ≤ w) (hv : V.size+1 ≤ w)
    (hs : ((n+1)*(U*V)).size+1 ≤ w) :
    (dot a b).Bound (4+n*(ucost+vcost+5)) w := by
  let term := fun i => do
    let u ← a i
    let v ← b i
    intMul u v
  have value (i : Fin n) : (term i).value.natAbs ≤ U*V := by
    change ((a i).value*(b i).value).natAbs ≤ _
    rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (au i) (bv i)
  have cost (i : Fin n) : (term i).Bound (ucost+(vcost+1)) w :=
    bound_bind (f := fun u => b i >>= intMul u) (ac i)
      (bound_bind (f := intMul (a i).value) (bc i) ⟨le_rfl,signedWidth (au i) (bv i) hu hv⟩)
  have collection := ArithmeticRun.sum_bound (n := n) term value cost hs (List.finRange n) (by simp)
  have range := (finRange_bound n).weaken le_rfl indices
  have same : (finRange n).value = List.finRange n := finRange_value n
  exact (bound_bind (f := ArithmeticRun.sum term) range (same ▸ collection)).weaken
    (by simp [Nat.mul_add]; omega) le_rfl

def power (v : ℕ) : ℕ → Run ℕ
  | 0 => step 0 1
  | t+1 => do
    let _ ← step (t+1).size t
    let x ← power v t
    natMul x v

@[simp] theorem power_value (v t : ℕ) : (power v t).value = v^t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [power, ih, natMul, pow_succ]

theorem power_work (v t T w : ℕ) (le : t ≤ T) (positive : 0 < v)
    (counter : T.size ≤ w) (base : v.size ≤ w) (total : (v^T).size ≤ w) :
    (power v t).Bound (1+2*t) w := by
  induction t with
  | zero => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | succ t ih =>
    have prior := ih (Nat.le_of_succ_le le)
    have tmp := Nat.size_le_size (Nat.pow_le_pow_right positive (Nat.le_of_succ_le le))
    have counter' := (Nat.size_le_size le).trans counter
    constructor
    · simp only [power, Run.bind_slots, step_slots, natMul]
      have := prior.1
      omega
    · simp only [power, Run.bind_width, step_width, natMul, power_value, max_le_iff]
      exact ⟨counter',prior.2,tmp.trans total,base⟩

def factorial : ℕ → Run ℕ
  | 0 => step 0 1
  | t+1 => do
    let _ ← step (t+1).size t
    let f ← factorial t
    natMul (t+1) f

@[simp] theorem factorial_value (t : ℕ) : (factorial t).value = t.factorial := by
  induction t with
  | zero => rfl
  | succ t ih => simp [factorial, ih, Nat.factorial_succ, natMul]

theorem factorial_work {t T w : ℕ} (le : t ≤ T) (count : T.size ≤ w) (total : T.factorial.size ≤ w) :
    (factorial t).Bound (1+2*t) w := by
  induction t with
  | zero => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | succ t ih =>
    have prior := ih (Nat.le_of_succ_le le)
    have tmp := (Nat.size_le_size (Nat.factorial_le (Nat.le_of_succ_le le))).trans total
    have count' := (Nat.size_le_size le).trans count
    constructor
    · simp only [factorial, Run.bind_slots, step_slots, natMul]
      have := prior.1
      omega
    · simp only [factorial, Run.bind_width, step_width, natMul, factorial_value, max_le_iff]
      exact ⟨count',prior.2,count',tmp⟩

end Kintali.LinearProgramming.ScalarRun
