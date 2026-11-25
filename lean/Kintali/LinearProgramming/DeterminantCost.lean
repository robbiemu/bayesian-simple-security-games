module

public import Kintali.LinearProgramming.BirdRun
public import Kintali.LinearProgramming.Bounds
import Mathlib.Algebra.Ring.Parity

/-!
# Polynomial binary work for a dense integer determinant

The charged execution returns exactly the determinant of its input table.
It uses at most `40 (n+1)^4` word operations, and the maximum observed signed
word width is quadratic in an upper bound for the dimension and input heights
in bits. The final theorem applies the repository's binary word pricing.
-/

@[expose] public section

namespace Kintali.LinearProgramming.BirdRun

open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {n : ℕ}

def wordWidth (n h t : ℕ) : ℕ :=
  2*n.size + 2*h.size + (t+1)*(n.size+h.size+3) + t.size + 8

private theorem height_bits (n h t : ℕ) :
    ((2*n*h)^t*h).size ≤ 1 + t*(n.size+h.size+2) + h.size := by
  have two : (2 : ℕ).size = 2 := by decide
  have h1 := size_mul_le 2 n
  have h2 := size_mul_le (2*n) h
  have h3 : (2*n*h).size ≤ n.size + h.size + 2 := by omega
  have h4 := (power_size_le (2*n*h) t).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left t h3) 1)
  exact (size_mul_le _ _).trans (Nat.add_le_add_right h4 _)

private theorem stage_width_le {t T : ℕ} (smaller : t ≤ T) (n h : ℕ) :
    stageWidth n h ((2*n*h)^t*h) ≤ wordWidth n h T := by
  let b := (2*n*h)^t*h
  have bz : b.size ≤ 1 + T * (n.size+h.size+3) + h.size := by
    have h1 : t*(n.size+h.size+2) ≤ T*(n.size+h.size+3) := Nat.mul_le_mul smaller (by omega)
    have h2 := height_bits n h t
    dsimp [b]
    omega
  have ns := size_succ_le n
  have hs := size_succ_le h
  have bs := size_succ_le b
  have p := size_mul_le (n+1) (h+1)
  have all := size_mul_le ((n+1)*(h+1)) (b+1)
  change n.size + ((n+1)*(h+1)*(b+1)).size + 2 ≤ _
  unfold wordWidth
  rw [Nat.succ_mul T (n.size+h.size+3)]
  omega

private theorem height_width_le {t T : ℕ} (smaller : t ≤ T) (n h : ℕ) :
    ((2*n*h)^t*h).size + 1 ≤ wordWidth n h T := by
  have tBound := height_bits n h t
  have growth : t*(n.size+h.size+2) ≤ (T+1)*(n.size+h.size+3) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold wordWidth
  omega

def stages (A : Bird.Table n) : ℕ → Run (Bird.Table n)
  | 0 => step n.size A
  | t+1 => do
    let _ ← step (t+1).size t
    let F ← stages A t
    stage A F

@[simp] theorem stages_value (A : Bird.Table n) (t : ℕ) :
    (stages A t).value = Bird.stages A t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [stages, Bird.stages, ih]

theorem stages_work (A : Bird.Table n) {h : ℕ}
    (input : ∀ u v, |Bird.entries A u v| ≤ (h : ℤ)) (t T : ℕ) (enough : t ≤ T) :
    (stages A t).Bound (1 + t*(1+32*(n+1)^3)) (wordWidth n h T) := by
  induction t with
  | zero =>
    exact (bound_step _ _).weaken (by simp) (by unfold wordWidth; omega)
  | succ t ih =>
    have prior := ih (Nat.le_of_succ_le enough)
    have fBound := Bird.stages_bound A input t
    have next := (stage_bound A (Bird.stages A t) input fBound).weaken le_rfl
      (stage_width_le (Nat.le_of_succ_le enough) n h)
    have index : (t+1).size ≤ wordWidth n h T := by
      have hle := Nat.size_le_size enough
      unfold wordWidth
      omega
    constructor
    · simp only [stages, Run.bind_slots, stages_value, step_slots]
      have hp := prior.1
      have hq := next.1
      rw [Nat.succ_mul]
      omega
    · simp only [stages, Run.bind_width, stages_value, step_width, max_le_iff]
      exact ⟨index, prior.2, next.2⟩

/-- The input is an already stored square table. The final sign is one
parity test on the number of stages. -/
def compute : {n : ℕ} → Bird.Table n → Run ℤ
  | 0, _ => step 0 1
  | t+1, A => do
    let F ← stages A t
    let last ← read F 0 0
    let sign ← step (t+1).size (if Even t then (1 : ℤ) else -1)
    intMul sign last

theorem compute_value (A : Bird.Table n) : (compute A).value = (Bird.entries A).det := by
  rw [← determinant_eq]
  cases n with
  | zero => rfl
  | succ t =>
    simp only [compute, Run.bind_value, stages_value, read_value, step_value, intMul, determinant,
      neg_one_pow_eq_ite]
    have equal : Bird.tabulate (Bird.entries A) = A := by
      apply Vector.ext
      intro i h
      apply Vector.ext
      intro j hj
      simp [Bird.tabulate, Bird.entries]
    rw [equal]

theorem compute_work (A : Bird.Table n) {h : ℕ} (input : ∀ u v, |Bird.entries A u v| ≤ (h : ℤ)) :
    (compute A).Bound (40*(n+1)^4) (wordWidth n h n) := by
  cases n with
  | zero => exact ⟨by change 1 ≤ 40*(0+1)^4; decide, Nat.zero_le _⟩
  | succ t =>
    let n := t+1
    let w := wordWidth n h n
    have it := stages_work A input t n (by omega)
    have iw : n.size ≤ w := by dsimp [w,wordWidth]; omega
    have last := Bird.stages_bound A input t (0 : Fin n) 0
    rw [← Int.natCast_natAbs] at last
    have lastNat : (Bird.entries (Bird.stages A t) 0 0).natAbs ≤ (2*n*h)^t*h := by exact_mod_cast last
    have lw : (Bird.entries (Bird.stages A t) 0 0).natAbs.size + 1 ≤ w :=
      (Nat.add_le_add_right (Nat.size_le_size lastNat) 1).trans (height_width_le (by omega : t ≤ n) n h)
    have sw : (if Even t then (1 : ℤ) else -1).natAbs.size + 1 ≤ w := by
      split <;> change 2 ≤ w <;> dsimp [w,wordWidth] <;> omega
    have finalWidth : max (if Even t then (1 : ℤ) else -1).natAbs.size
        (Bird.entries (Bird.stages A t) 0 0).natAbs.size + 1 ≤ w := by omega
    constructor
    · change (stages A t).work.slots + 4 ≤ 40*(t+1+1)^4
      exact (Nat.add_le_add_right it.1 4).trans (by ring_nf; omega)
    · simp only [compute, Run.bind_width, stages_value, read, step_width, intMul,
        step_value, max_le_iff]
      exact ⟨it.2, ⟨iw,iw⟩, iw, finalWidth⟩

theorem wordWidth_polynomial {n h t L : ℕ} (dim : n ≤ L) (bits : h.size ≤ L) (iter : t ≤ L) :
    wordWidth n h t ≤ 24*(L+2)^2 := by
  have nn := (size_le_self n).trans dim
  have tt := (size_le_self t).trans iter
  change 2*n.size + 2*h.size + (t+1)*(n.size+h.size+3) + t.size + 8 ≤ _
  calc
    _ ≤ 2*L + 2*L + (L+1)*(L+L+3) + L + 8 := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem compute_binary_cost (A : Bird.Table n) {h L : ℕ}
    (input : ∀ u v, |Bird.entries A u v| ≤ (h : ℤ)) (dim : n ≤ L) (bits : h.size ≤ L) :
    (compute A).work.slots * wordCost (compute A).work.width ≤
      (40*(L+1)^4) * (64*(24*(L+2)^2+1)^3) := by
  have hrun := compute_work A input
  have slotBound : (compute A).work.slots ≤ 40*(L+1)^4 := hrun.1.trans (by gcongr)
  exact Nat.mul_le_mul slotBound (wordCost_mono (hrun.2.trans (wordWidth_polynomial dim bits dim)))

end Kintali.LinearProgramming.BirdRun
