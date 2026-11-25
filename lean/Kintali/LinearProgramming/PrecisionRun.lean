module

public import Kintali.LinearProgramming.ScalarRun

/-! # Computing the radix and inverse precision for repair -/

@[expose] public section

namespace Kintali.LinearProgramming.PrecisionRun

open StochasticGames.CompilerRun StochasticGames.BinarySize

structure Parameters where
  radix : ℕ
  divisor : ℕ

def setup (m n h : ℕ) : Run Parameters := do
  let a ← natAdd n 1
  let b ← natAdd m 1
  let f ← ScalarRun.factorial a
  let p ← ScalarRun.power h a
  let H ← natMul f p
  let nn ← natMul n n
  let nnh ← natMul nn h
  let amp ← natMul nnh H
  let K ← natAdd amp 2
  let R ← ScalarRun.power K b
  let Q ← natMul H R
  step 0 ⟨K,Q⟩

@[simp] theorem setup_value (m n h : ℕ) :
    (setup m n h).value = ⟨SlackWindow.radix n h, SlackWindow.divisor m n h⟩ := by
  simp [setup, natAdd, natMul, SlackWindow.amplification, SlackWindow.height, SlackWindow.radix,
    SlackWindow.divisor, minorBound]

theorem power_le_divisor (m n : ℕ) {h : ℕ} (hp : 0 < h) :
    SlackWindow.radix n h^(m+1) ≤ SlackWindow.divisor m n h :=
  Nat.le_mul_of_pos_left _ (minorBound_pos (n+1) hp)

theorem setup_work {m n h L w : ℕ} (hp : 0 < h) (hm : m+1 ≤ L) (hn : n+1 ≤ L)
    (indices : L.size ≤ w) (hfit : h.size ≤ w) (qfit : (SlackWindow.divisor m n h).size ≤ w)
    (two : 2 ≤ w) : (setup m n h).Bound (16*(L+2)) w := by
  let H := SlackWindow.height n h
  let K := SlackWindow.radix n h
  let Q := SlackWindow.divisor m n h
  have Hpos : 0 < H := minorBound_pos (n+1) hp
  have Kpos : 0 < K := by dsimp [K,SlackWindow.radix]; omega
  have pow_le : K^(m+1) ≤ Q := power_le_divisor m n hp
  have K_le : K ≤ K^(m+1) := by
    calc
      _ = K^1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right Kpos (by omega)
  have H_le : H ≤ Q := Nat.le_mul_of_pos_right _ (pow_pos Kpos _)
  have bits {a : ℕ} (le : a ≤ Q) : a.size ≤ w := (Nat.size_le_size le).trans qfit
  have nfit : n.size ≤ w := (Nat.size_le_size (by omega : n ≤ L)).trans indices
  have mfit : m.size ≤ w := (Nat.size_le_size (by omega : m ≤ L)).trans indices
  have a := (Nat.size_le_size hn).trans indices
  have b := (Nat.size_le_size hm).trans indices
  have f := bits ((Nat.le_mul_of_pos_right ((n+1).factorial) (pow_pos hp (n+1))).trans H_le)
  have p := bits ((Nat.le_mul_of_pos_left (h^(n+1)) (Nat.factorial_pos _)).trans H_le)
  have hs := bits H_le
  have ks := bits (K_le.trans pow_le)
  have ps := bits pow_le
  have amp_le : n*n*h*H ≤ K := Nat.le_add_right _ _
  have amps := bits (amp_le.trans (K_le.trans pow_le))
  have nh_le : n*n*h ≤ n*n*h*H := Nat.le_mul_of_pos_right _ Hpos
  have nh := bits (nh_le.trans (amp_le.trans (K_le.trans pow_le)))
  have nn := bits ((Nat.le_mul_of_pos_right (n*n) hp).trans (nh_le.trans (amp_le.trans (K_le.trans pow_le))))
  have fac := ScalarRun.factorial_work (le_rfl : n+1 ≤ n+1) a f
  have base := ScalarRun.power_work h (n+1) (n+1) w le_rfl hp a hfit p
  have raised := ScalarRun.power_work K (m+1) (m+1) w le_rfl Kpos b ks ps
  constructor
  · simp only [setup, Run.bind_slots, natAdd, natMul, step_slots, step_value,
      ScalarRun.factorial_value, ScalarRun.power_value]
    have fact := fac.1
    have exp := base.1
    have high := raised.1
    change (ScalarRun.power (n*n*h*((n+1).factorial*h^(n+1))+2) (m+1)).work.slots ≤ _ at high
    omega
  · simp only [setup, Run.bind_width, natAdd, natMul, step_width, step_value,
      ScalarRun.factorial_value, ScalarRun.power_value, max_le_iff]
    have one : (1 : ℕ).size ≤ w := by change 1 ≤ w; omega
    exact ⟨⟨nfit,one⟩, ⟨mfit,one⟩, fac.2, base.2, ⟨f,p⟩, ⟨nfit,nfit⟩, ⟨nn,hfit⟩,
      ⟨nh,hs⟩, ⟨amps,two⟩, raised.2, ⟨hs,ps⟩, Nat.zero_le _⟩

end Kintali.LinearProgramming.PrecisionRun
