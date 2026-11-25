module

public import Kintali.LinearProgramming.OutputEncoding
public import Kintali.LinearProgramming.RationalOutput
import all StochasticGames.BinaryEncoding

/-! # Reading the output stream and checking the complete recovery contract -/

@[expose] public section

namespace Kintali.LinearProgramming.AnswerStream

open PivotRun CramerRun StochasticGames.CompilerRun StochasticGames.CompilationCost StochasticGames.BinaryEncoding

variable {m n : ℕ}

def readFields : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bs => some ([],bs)
  | k+1, bs => do
    let (a,tail) ← readInt bs
    let (as,rest) ← readFields k tail
    pure (a::as,rest)

def read (bs : List Bool) : Option (ℤ × List ℤ) := do
  let (n,rest) ← readNat bs
  let (d,tail) ← readInt rest
  let (nums,last) ← readFields n tail
  if last.isEmpty then some (d,nums) else none

private theorem readFields_values (xs : List ℤ) (tail : List Bool) :
    readFields xs.length (xs.flatMap intBits ++ tail) = some (xs,tail) := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readFields,
      readInt_append, Option.bind_eq_bind, Option.bind_some, ih, pure]

theorem read_bits (A : Answer n) :
    read (OutputEncoding.bits A) = some (A.den, (List.finRange n).map (fun j => A.num[j.val])) := by
  let nums := (List.finRange n).map (fun j => A.num[j.val])
  have len : nums.length = n := by simp [nums]
  have flat : nums.flatMap intBits = (List.finRange n).flatMap (fun j => intBits A.num[j.val]) := by
    simp [nums, List.flatMap_map]
  have correct := readFields_values nums []
  rw [len,flat,List.append_nil] at correct
  simp only [read, OutputEncoding.bits, List.append_assoc, readNat_append, readInt_append,
    Option.bind_eq_bind, Option.bind_some, correct, List.isEmpty_nil, ite_true]
  rfl

/-- The produced bitstream decodes to rational coordinates with a nonzero
denominator satisfying every inequality. The bound prices the same run,
including serialization, in terms of the stored input length. -/
theorem correct (P : Input m n) (x : Vector ℚ n) {h : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ))
    (approximate : ∀ i, -SlackWindow.precision m n h ≤ P.system.slack (PointEncoding.input x) i) :
    let a := (RationalInput.run P x h).value
    let z := OutputEncoding.run P x h
    read z.value = some (a.den,(List.finRange n).map (fun j => a.num[j.val])) ∧
      a.den ≠ 0 ∧ P.system.Feasible a.value ∧
      RecoveryRun.binaryWork (RationalInput.inputLength P x h) z.work ≤
        OutputEncoding.binaryLimit (RationalInput.inputLength P x h) := by
  dsimp only
  rw [OutputEncoding.run_value]
  exact ⟨read_bits _, RationalInput.run_den_ne_zero P x h, RationalInput.run_feasible P x hp coeff approximate,
    OutputEncoding.run_binary_work P x hp coeff⟩

end Kintali.LinearProgramming.AnswerStream
