module

public import Kintali.LinearProgramming.RationalInput

/-! # Materializing a generated integer system -/

@[expose] public section

namespace Kintali.LinearProgramming.PivotRun.Input

open StochasticGames.CompilerRun

variable {m n : ℕ}

def ofSystem (P : System (Fin m) (Fin n)) : Input m n :=
  ⟨Vector.ofFn (fun i => Vector.ofFn (P.coeff i)), Vector.ofFn P.rhs⟩

@[simp] theorem system_ofSystem (P : System (Fin m) (Fin n)) : (ofSystem P).system = P := by
  cases P with
  | mk A b =>
    unfold ofSystem system
    congr 1
    · ext i j
      simp
    · funext i
      simp

/-- The callbacks price the application-specific generation of an integer
entry. The outer run charges the row/column traversal and dense table writes. -/
def read (coeff : Fin m → Fin n → Run ℤ) (rhs : Fin m → Run ℤ) : Run (Input m n) := do
  let A ← ArithmeticRun.tabulate m fun i => ArithmeticRun.tabulate n (coeff i)
  let b ← ArithmeticRun.tabulate m rhs
  step 0 ⟨A,b⟩

@[simp] theorem read_value (coeff : Fin m → Fin n → Run ℤ) (rhs : Fin m → Run ℤ) :
    (read coeff rhs).value =
      ofSystem ⟨.of fun i j => (coeff i j).value, fun i => (rhs i).value⟩ := by
  simp only [read, Run.bind_value, step_value, ArithmeticRun.tabulate_value, ofSystem]
  rfl

theorem read_work (coeff : Fin m → Fin n → Run ℤ) (rhs : Fin m → Run ℤ) {c d w : ℕ}
    (rows : m.size ≤ w) (cols : n.size ≤ w) (coeffWork : ∀ i j, (coeff i j).Bound c w)
    (rhsWork : ∀ i, (rhs i).Bound d w) :
    (read coeff rhs).Bound (3*(m+1)+m*(3*(n+1)+n*c) + (3*(m+1)+m*d+1)) w := by
  have A := ArithmeticRun.tabulate_bound _ rows (fun i => ArithmeticRun.tabulate_bound _ cols (coeffWork i))
  have b := ArithmeticRun.tabulate_bound _ rows rhsWork
  exact ⟨Nat.add_le_add A.1 (Nat.add_le_add_right b.1 1),
    max_le A.2 (max_le b.2 (Nat.zero_le _))⟩

end Kintali.LinearProgramming.PivotRun.Input
