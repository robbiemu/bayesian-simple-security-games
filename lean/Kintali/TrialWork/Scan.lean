module

public import Kintali.TrialWork.Arithmetic
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! Explicit list scans for rational sums and early-stopping Boolean tests. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize

variable {α : Type}

def qsum (read : α → Run ℚ) : List α → Run ℚ
  | [] => step 0 0
  | a::as => do
    let i ← step 0 a
    let x ← read i
    let tail ← qsum read as
    plus x tail

@[simp] theorem qsum_value (read : α → Run ℚ) (l : List α) :
    (qsum read l).value = (l.map fun i => (read i).value).sum := by
  induction l <;> simp_all [qsum]

theorem list_sum_univ [DecidableEq α] [Fintype α] (f : α → ℚ) (l : List α)
    (unique : l.Nodup) (complete : ∀ a, a ∈ l) : (l.map f).sum = ∑ i, f i := by
  rw [Finset.sum_list_map_count]
  have eq : l.toFinset = Finset.univ := Finset.ext (by simp [complete])
  rw [eq]
  simp [List.count_eq_one_of_mem unique (complete _)]

def sumBits (n w : ℕ) := 1+n*(w+1)

theorem list_sum_fits (read : α → Run ℚ) (xs : List α) {w : ℕ}
    (fit : ∀ i, Fits w (read i).value) : Fits (sumBits xs.length w) (qsum read xs).value := by
  induction xs with
  | nil => simpa [qsum,sumBits] using Fits.zero
  | cons x xs ih =>
    rw [qsum,Run.bind_value,step_value,Run.bind_value,Run.bind_value,plus_value]
    exact ((fit x).add ih).mono (by simp only [sumBits,List.length_cons,Nat.add_mul,Nat.one_mul]; omega)

def addWidth (n w : ℕ) := sumBits n w+w
def sumSlots (n w c : ℕ) := 1+n*(1+c+scalarSlots (addWidth n w))

theorem qsum_work (read : α → Run ℚ) (xs : List α) {n w c u : ℕ} (count : xs.length ≤ n)
    (item : ∀ i, (read i).Bound c u) (fit : ∀ i, Fits w (read i).value)
    (space : scalarWidth (addWidth n w) ≤ u) :
    (qsum read xs).Bound (sumSlots n w c) u := by
  let b := addWidth n w
  have aux (ls : List α) (hl : ls.length ≤ n) :
      (qsum read ls).Bound (1+ls.length*(1+c+scalarSlots b)) u := by
    induction ls with
    | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
    | cons x ls ih =>
      have len : ls.length ≤ n := (Nat.le_succ _).trans hl
      have tail := ih len
      have tailBits : sumBits ls.length w ≤ b :=
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ len) _).trans (Nat.le_add_right ..)
      have ar := plus_work ((fit x).mono (show w ≤ b from Nat.le_add_left ..))
        ((list_sum_fits read ls fit).mono tailBits)
      have h := bound_bind ((bound_step 0 x).weaken le_rfl (Nat.zero_le u)) (f := fun i => do
        let a ← read i
        let t ← qsum read ls
        plus a t) (bound_bind (item x) (bound_bind tail (ar.weaken le_rfl space)))
      apply h.weaken _ le_rfl
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact (aux xs count).weaken (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) 1) le_rfl

def sumFin (n : ℕ) (read : Fin n → Run ℚ) : Run ℚ := finRange n >>= qsum read

@[simp] theorem sumFin_value (n : ℕ) (read : Fin n → Run ℚ) :
    (sumFin n read).value = ∑ i, (read i).value := by
  simp only [sumFin,Run.bind_value,finRange_value,qsum_value]
  exact list_sum_univ _ (List.finRange n) (List.nodup_finRange n) List.mem_finRange

theorem sumFin_work (n : ℕ) (read : Fin n → Run ℚ) {N w c u : ℕ} (count : n ≤ N)
    (idx : n.size ≤ u) (item : ∀ i, (read i).Bound c u) (fit : ∀ i, Fits w (read i).value)
    (space : scalarWidth (addWidth N w) ≤ u) :
    (sumFin n read).Bound (2*N+1+sumSlots N w c) u := by
  apply bound_bind ((finRange_bound n).weaken (by omega) idx)
  rw [finRange_value]
  exact qsum_work read _ (by simpa using count) item fit space

def anyM (test : α → Run Bool) : List α → Run Bool
  | [] => step 0 false
  | a::as => do
    let i ← step 0 a
    let b ← test i
    if b then pure true else anyM test as

@[simp] theorem anyM_value (test : α → Run Bool) (l : List α) :
    (anyM test l).value = l.any (fun a => (test a).value) := by
  induction l with
  | nil => rfl
  | cons a as ih => cases h : (test a).value <;> simp [anyM,h,ih]

theorem anyM_work (test : α → Run Bool) (l : List α) {c w : ℕ}
    (ok : ∀ i, (test i).Bound c w) : (anyM test l).Bound (1+l.length*(c+1)) w := by
  induction l with
  | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
  | cons a as ih =>
    have step' : (if (test a).value then (pure true : Run Bool) else anyM test as).Bound
        (1+as.length*(c+1)) w := by
      cases h : (test a).value
      · exact ih
      · exact (bound_pure _ _).weaken (Nat.zero_le _) le_rfl
    have work := bound_bind ((bound_step 0 a).weaken le_rfl (Nat.zero_le w))
      (f := fun i => do let b ← test i; if b then pure true else anyM test as) (bound_bind (ok a) step')
    apply work.weaken _ le_rfl
    rw [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

end Kintali.TrialWork
