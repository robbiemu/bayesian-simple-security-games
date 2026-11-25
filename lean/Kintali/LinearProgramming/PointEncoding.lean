module

public import Kintali.LinearProgramming.RecoveryCost

/-! # Reading a vector of ordinary rational inputs

The common denominator is formed once. Each stored numerator then uses one
exact unsigned quotient and one signed product. The quotient is priced at
the same binary-word bound as the project's schoolbook long division.
-/

@[expose] public section

namespace Kintali.LinearProgramming.PointEncoding

open StochasticGames.CompilerRun StochasticGames.BinarySize PointRun

variable {n : ℕ}

def product (x : Vector ℚ n) : List (Fin n) → Run ℕ
  | [] => step 0 1
  | j :: js => do
    let b ← step n.size x[j.val].den
    let d ← product x js
    natMul b d

@[simp] theorem product_value (x : Vector ℚ n) (js : List (Fin n)) :
    (product x js).value = (js.map (fun j => x[j.val].den)).prod := by
  induction js with
  | nil => rfl
  | cons i js ih => simp [product, ih, natMul]

theorem product_size (x : Vector ℚ n) (js : List (Fin n)) {S : ℕ}
    (bits : ∀ j : Fin n, x[j.val].den.size ≤ S) :
    (product x js).value.size ≤ 1+js.length*S := by
  induction js with
  | nil => simp [product, step, Work.one]
  | cons j js ih =>
    change (x[j.val].den * (product x js).value).size ≤ 1+(js.length+1)*S
    exact (size_mul_le ..).trans (by
      have hb := bits j
      rw [Nat.add_mul]
      omega)

theorem product_work (x : Vector ℚ n) (js : List (Fin n)) {S : ℕ}
    (bits : ∀ j : Fin n, x[j.val].den.size ≤ S) :
    (product x js).Bound (1+2*js.length) (n.size+S+1+js.length*S) := by
  induction js with
  | nil => exact ⟨by simp [product], by simp [product]⟩
  | cons j js ih =>
    have hb := bits j
    have ps := product_size x js bits
    constructor
    · change 1+((product x js).work.slots+1) ≤ 1+2*(js.length+1)
      have h := ih.1
      omega
    · change max n.size (max (product x js).work.width (max x[j.val].den.size (product x js).value.size)) ≤
        n.size+S+1+(js.length+1)*S
      rw [Nat.add_mul]
      have h := ih.2
      omega

def quotient (a b : ℕ) : Run ℕ := step (max a.size b.size) (a/b)

def numerator (x : Vector ℚ n) (D : ℕ) (j : Fin n) : Run ℤ := do
  let q ← step n.size x[j.val]
  let a ← quotient D q.den
  intMul q.num (a : ℤ)

def raw (x : Vector ℚ n) : Run (Vector ℤ n × ℕ) := do
  let js ← finRange n
  let D ← product x js
  let nums ← ArithmeticRun.tabulate n (numerator x D)
  step 0 (nums,D)

def input (x : Vector ℚ n) : Fin n → ℚ := fun j => x[j.val]

theorem denominator_value (x : Vector ℚ n) :
    (product x (List.finRange n)).value = ScaledPoint.denominator (input x) := by
  simp only [product_value, ScaledPoint.denominator, input, ← Fin.prod_univ_def]

theorem raw_value (x : Vector ℚ n) :
    (raw x).value = (Vector.ofFn (ScaledPoint.encode (input x)).num,(ScaledPoint.encode (input x)).den) := by
  simp only [raw, Run.bind_value, finRange_value, denominator_value, step_value, ArithmeticRun.tabulate_value, numerator, quotient, intMul]
  rfl

def encode (x : Vector ℚ n) : Run (Point n) :=
  let r := raw x
  ⟨⟨r.value.1,r.value.2, by rw [show r.value = _ from raw_value x]; exact (ScaledPoint.encode (input x)).positive⟩,
    r.work⟩

@[simp] theorem encode_value (x : Vector ℚ n) : (encode x).value.scaled = ScaledPoint.encode (input x) := by
  simp [encode, Point.scaled, raw_value]

@[simp] theorem encode_point (x : Vector ℚ n) : (encode x).value.scaled.value = input x := by
  simp

def wordLimit (S : ℕ) := 4*(S+2)^2

theorem encode_work (x : Vector ℚ n) {S : ℕ} (dim : n ≤ S)
    (numerators : ∀ j : Fin n, x[j.val].num.natAbs.size ≤ S)
    (denominators : ∀ j : Fin n, x[j.val].den.size ≤ S) :
    (encode x).Bound (16*(S+2)) (wordLimit S) := by
  let js := List.finRange n
  let D := (product x js).value
  let w := wordLimit S
  have idx := (size_le_self n).trans dim
  have tally := product_work x js denominators
  have ds : D.size ≤ 1+n*S := by simpa [D,js] using product_size x js denominators
  have pw : (product x js).Bound (1+2*n) w := by
    simp only [js, List.length_finRange] at tally ⊢
    have nn := Nat.mul_le_mul_right S dim
    apply tally.weaken le_rfl
    dsimp [w,wordLimit]
    ring_nf at nn ⊢
    omega
  have fitS : S+1 ≤ w := by dsimp [w,wordLimit]; ring_nf; omega
  have nn := Nat.mul_le_mul_right S dim
  have fitD : D.size+1 ≤ w := by dsimp [w,wordLimit]; ring_nf at nn ⊢; omega
  have sub (j : Fin n) : (numerator x D j).Bound 3 w := by
    have num := numerators j
    have den := denominators j
    have div := Nat.size_le_size (Nat.div_le_self D x[j.val].den)
    exact ⟨le_rfl, max_le (by omega : n.size ≤ w) (max_le (by change max D.size x[j.val].den.size ≤ w; omega)
      (by change max x[j.val].num.natAbs.size (D/x[j.val].den).size+1 ≤ w
          omega))⟩
  have nums := ArithmeticRun.tabulate_bound _ (by omega : n.size ≤ w) sub
  have ran := finRange_bound n
  constructor
  · change (raw x).work.slots ≤ _
    simp only [raw, Run.bind_slots, finRange_value, step_slots]
    change (finRange n).work.slots + ((product x js).work.slots +
      ((ArithmeticRun.tabulate n (numerator x D)).work.slots + 1)) ≤ _
    have a := ran.1
    have b := pw.1
    have c := nums.1
    omega
  · change (raw x).work.width ≤ _
    simp only [raw, Run.bind_width, finRange_value, step_width]
    exact max_le (ran.2.trans (by omega)) (max_le pw.2 (max_le nums.2 (Nat.zero_le _)))

end Kintali.LinearProgramming.PointEncoding
