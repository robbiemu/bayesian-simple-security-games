module

public import Kintali.InputOutput.CodecWorkRead
public import Kintali.InputOutput.CodecWorkOutput
public import Kintali.LinearProgramming.RecoveryCost

/-! # Addressed binary word work of the public input and output codecs

These bounds price the representation boundary of the exact solver. They
start with the input bit list or the stored list of compact rational strategy
coordinates. The arithmetic inside the game solver has its own costs.
-/

@[expose] public section

namespace Kintali.InputOutput.CodecWork

open Binary StochasticGames.CompilerRun StochasticGames.BinarySize

private theorem pair_fields {α β : Type} {a : Codec α} {b : Codec β} {xs : Stream} {x : α} {y : β}
    (h : (pairCodec a b).decode xs = some (x,y)) :
    ∃ f t : Stream, splitBlock xs = some (f,t) ∧ a.decode f = some x ∧ b.decode t = some y := by
  change (Option.bind (splitBlock xs) _) = _ at h
  obtain ⟨⟨f,t⟩,hs,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨x',hx,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y',hy,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨f,t,hs,hx,hy⟩

private theorem field_widths {xs : Stream} {n m : ℕ}
    (h : (pairCodec natCodec natCodec).decode xs = some (n,m)) :
    n.size ≤ xs.length+1 ∧ m.size ≤ xs.length+1 := by
  obtain ⟨f,t,hs,hn,hm⟩ := pair_fields h
  have len := split_lengths hs
  have nf := number_width hn
  have mt := number_width hm
  omega

def intLimit (S : ℕ) := pairLimit (·+2) (·+2) S+2

def intReader : Reader intCodec intLimit where
  run xs := next ((pairReader natReader natReader).run xs) fun p =>
    step (max p.1.size p.2.size+1) (some ((p.1 : ℤ)-p.2))
  correct xs := by
    cases hd : (pairCodec natCodec natCodec).decode xs <;>
      simp [next_value,Reader.correct,intCodec,hd]
  work xs S fit := by
    apply next_work (j := 1) ((pairReader natReader natReader).work xs S fit)
    rintro ⟨x,y⟩ h
    rw [Reader.correct] at h
    have hw := field_widths h
    exact (bound_step _ _).weaken le_rfl (by dsimp only; omega)

theorem integer_width {xs : Stream} {z : ℤ} (h : intCodec.decode xs = some z) :
    z.natAbs.size ≤ xs.length+1 := by
  change (Option.map _ ((pairCodec natCodec natCodec).decode xs)) = some z at h
  obtain ⟨⟨n,m⟩,hd,rfl⟩ := Option.map_eq_some_iff.mp h
  have hw := field_widths hd
  have small : ((n : ℤ)-m).natAbs ≤ max n m := by
    cases h : (n : ℤ)-m <;> simp only [Int.ofNat_eq_natCast,Int.negSucc_eq] at h <;> simp <;> omega
  change ((n : ℤ)-m).natAbs.size ≤ _
  have := Nat.size_le_size small
  rw [Nat.max_def] at this
  split at this <;> omega

def ratLimit (S : ℕ) := pairLimit intLimit (·+2) S+1+(5*(S+1)+7+1)

def ratReader : Reader ratCodec ratLimit where
  run xs := next ((pairReader intReader natReader).run xs) fun p => do
    let q ← reduce p.1 p.2
    step 0 (some q)
  correct xs := by
    cases hd : (pairCodec intCodec natCodec).decode xs <;>
      simp [next_value,Reader.correct,reduce_value,ratCodec,hd]
  work xs S fit := by
    apply next_work ((pairReader intReader natReader).work xs S fit)
    rintro ⟨z,d⟩ h
    rw [Reader.correct] at h
    obtain ⟨f,t,hs,hz,hd⟩ := pair_fields h
    have len := split_lengths hs
    have iz := integer_width hz
    have nd := number_width hd
    have r := (reduce_work z d (W := S+1) (by omega) (by omega)).weaken le_rfl
      (by omega : S+1+2 ≤ S+8)
    exact bound_bind r ((bound_step _ _).weaken le_rfl (Nat.zero_le _))

def payoffLimit := pairLimit ratLimit ratLimit
def inputLimit := pairLimit (·+2) (pairLimit (listLimit payoffLimit)
  (listLimit (pairLimit ratLimit (listLimit payoffLimit))))

def inputReader : Reader inputCodec inputLimit :=
  let payoff := pairReader ratReader ratReader
  pairReader natReader (pairReader (listReader payoff) (listReader (pairReader ratReader (listReader payoff))))

theorem inputLimit_eq (S : ℕ) : inputLimit S = 22*S^3+110*S^2+125*S+16 := by
  unfold inputLimit payoffLimit pairLimit listLimit ratLimit intLimit pairLimit
  ring

theorem input_value (xs : Stream) : (inputReader.run xs).value = inputCodec.decode xs :=
  inputReader.correct xs

theorem input_work (xs : Stream) : (inputReader.run xs).Bound (inputLimit xs.length) (xs.length+8) :=
  inputReader.work xs _ le_rfl

/-- The addressed pricing function used for the certified LP recovery. -/
def binaryLimit (cells k w : ℕ) := k*(64*(cells+k+3*w+16)^3)

theorem addressed_bound {α : Type} (cells : ℕ) {p : Run α} {k w : ℕ} (h : p.Bound k w) :
    LinearProgramming.RecoveryRun.binaryWork cells p.work ≤ binaryLimit cells k w := by
  have cw := size_le_self (cells+1)
  have sw := size_le_self (p.work.slots+1)
  have ww := size_le_self (p.work.width+1)
  have hw : max p.work.width (addressWidth cells p.work.slots p.work.width)+1 ≤ cells+k+3*w+16 := by
    unfold addressWidth
    obtain ⟨h₁,h₂⟩ := h
    omega
  exact Nat.mul_le_mul h.1 (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hw 3))

theorem input_binary_work (xs : Stream) :
    LinearProgramming.RecoveryRun.binaryWork xs.length (inputReader.run xs).work ≤
      binaryLimit xs.length (inputLimit xs.length) (xs.length+8) := addressed_bound _ (input_work xs)

/-- A bound in the size of the stored compact output and its word addresses. -/
theorem output_binary_work (cells : ℕ) (e : Output) :
    LinearProgramming.RecoveryRun.binaryWork cells (outputWriter.run e).work ≤
      binaryLimit cells (72*((output e).length+1)) ((output e).length+3) :=
  addressed_bound _ (output_work e)

end Kintali.InputOutput.CodecWork
