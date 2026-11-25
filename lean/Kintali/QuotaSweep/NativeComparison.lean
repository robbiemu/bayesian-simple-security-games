module

public import Kintali.QuotaSweep.RankComparison

/-! # Native bit lengths for the charged sparse key comparison

The last tie-break can have thousands of bits. Each comparison measures
its width as part of the work record. Lean's native logarithm computes the
same width as Mathlib's binary recursion in `Nat.size`. The compiler
substitution below preserves the comparison result, slots and peak width.
-/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun.NativeComparison

open Kintali.ExactRecovery StochasticGames.CompilerRun

def wordBits (n : ℕ) := if n=0 then 0 else n.log2+1

theorem wordBits_eq (n : ℕ) : wordBits n = n.size := by
  by_cases h : n=0
  · simp [h,wordBits]
  · simp only [wordBits,h,↓reduceIte]
    exact Nat.le_antisymm ((Nat.log2_lt h).2 (Nat.lt_size_self n))
      (Nat.size_le.2 ((Nat.log2_lt h).1 (Nat.lt_succ_self _)))

def lessNat (x y : ℕ) : Run Bool := step (max (wordBits x) (wordBits y)) (decide (x<y))
def eqNat (x y : ℕ) : Run Bool := step (max (wordBits x) (wordBits y)) (decide (x=y))

def product (a b : ℤ) : Run ℤ := step (max (wordBits a.natAbs) (wordBits b.natAbs)+1) (a*b)

def ratLE (q r : ℚ) : Run Bool := do
  let a ← product q.num r.den
  let b ← product r.num q.den
  step (max (wordBits a.natAbs) (wordBits b.natAbs)+1) (decide (a≤b))

def ratEq (q r : ℚ) : Run Bool := do
  let n ← step (max (wordBits q.num.natAbs) (wordBits r.num.natAbs)+1) (q.num == r.num)
  let d ← step (max (wordBits q.den) (wordBits r.den)) (q.den == r.den)
  step 1 (n && d)

def primaryLt (x y : WithTop ℚ) : Run Bool := do
  let t ← step 0 (x,y)
  match t.1,t.2 with
  | some q,some r => do let z ← ratLE r q; step 1 (!z)
  | none,_ => step 1 false
  | some _,none => step 1 true

def primaryEq (x y : WithTop ℚ) : Run Bool := do
  let t ← step 0 (x,y)
  match t.1,t.2 with
  | some q,some r => ratEq q r
  | none,none => step 1 true
  | _,_ => step 1 false

def quickKey (x y : Expanded.Key) : Run Bool :=
  let a := ofLex x
  let b := ofLex y
  let c := ofLex a.2
  let d := ofLex b.2
  let e := ofLex c.2
  let f := ofLex d.2
  RankRun.lex (primaryLt a.1 b.1) (primaryEq a.1 b.1)
    (RankRun.lex (lessNat c.1 d.1) (eqNat c.1 d.1)
      (RankRun.lex (lessNat e.1 f.1) (eqNat e.1 f.1) (lessNat e.2 f.2)))

private theorem quickKey_eq : quickKey = RankRun.keyLess := by
  have leE : ratLE = TrialWork.le := by
    funext q r
    simp only [ratLE,TrialWork.le,product,intMul,wordBits_eq]
  have eqE : ratEq = TrialWork.eqRat := by
    funext q r
    simp only [ratEq,TrialWork.eqRat,wordBits_eq]
  have pl : primaryLt = RankRun.nullableLess := by
    funext x y
    cases x using WithTop.recTopCoe <;> cases y using WithTop.recTopCoe <;>
      simp [primaryLt,RankRun.nullableLess,leE,TrialWork.lt] <;> rfl
  have pe : primaryEq = RankRun.nullableEqual := by
    funext x y
    cases x using WithTop.recTopCoe <;> cases y using WithTop.recTopCoe <;>
      simp [primaryEq,RankRun.nullableEqual,eqE] <;> rfl
  funext x y
  simp only [quickKey,RankRun.keyLess,RankRun.natLess,RankRun.natEqual,lessNat,eqNat,pl,pe,wordBits_eq]


@[csimp] theorem keyLess_compiled : RankRun.keyLess = quickKey := quickKey_eq.symm

end Kintali.QuotaSweep.RankRun.NativeComparison
