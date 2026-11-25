module

public import Kintali.InputOutput.CodecWorkArithmetic
public import Kintali.ContactSize.Rational
public import Kintali.LinearProgramming.ArithmeticRun

/-! Normalized rational operations for trial scans. Cross products, signs,
division, Euclidean remainders and construction of a reduced pair are
charged by the addressed-word model. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize InputOutput.CodecWork

def scalarWidth (w : ℕ) := 2*w+6
def scalarSlots (w : ℕ) := 10*w+25

def plus (q r : ℚ) : Run ℚ := do
  let a ← intMul q.num r.den
  let b ← intMul (q.den : ℤ) r.num
  let n ← intAdd a b
  let d ← natMul q.den r.den
  reduce n d

def times (q r : ℚ) : Run ℚ := do
  let n ← intMul q.num r.num
  let d ← natMul q.den r.den
  reduce n d

/-- A reduced fraction only needs a sign transfer and a field swap for
reciprocation. The zero case uses denominator one. -/
def inverse (q : ℚ) : Run ℚ :=
  let sign := step q.num.natAbs.size q.num.sign
  let n := intMul sign.value q.den
  let d := step q.num.natAbs.size (if q.num = 0 then 1 else q.num.natAbs)
  let r : ℚ := ⟨n.value,d.value, by simpa only [d,step_value,← Rat.den_inv] using (q⁻¹).den_nz,
    by simpa only [n,sign,d,intMul,step_value,← Rat.num_inv,← Rat.den_inv] using (q⁻¹).reduced⟩
  ⟨r,sign.work.seq (n.work.seq (d.work.seq (Work.one 0)))⟩

def divide (q r : ℚ) : Run ℚ := inverse r >>= times q

def le (q r : ℚ) : Run Bool := do
  let n ← intMul q.num r.den
  let m ← intMul r.num q.den
  step (max n.natAbs.size m.natAbs.size+1) (decide (n ≤ m))

def lt (q r : ℚ) : Run Bool := do
  let b ← le r q
  step 1 (!b)

def eqRat (q r : ℚ) : Run Bool := do
  let n ← step (max q.num.natAbs.size r.num.natAbs.size+1) (q.num == r.num)
  let d ← step (max q.den.size r.den.size) (q.den == r.den)
  step 1 (n && d)

@[simp] theorem plus_value (q r : ℚ) : (plus q r).value = q+r := by
  simp only [plus,Run.bind_value,intMul,intAdd,natMul,step_value,reduce_value]
  rw [Rat.add_num_den, Rat.divInt_eq_div]
  push_cast
  rfl

@[simp] theorem times_value (q r : ℚ) : (times q r).value = q*r := by
  simp only [times,Run.bind_value,intMul,natMul,step_value,reduce_value]
  rw [Rat.mul_eq_mkRat,Rat.mkRat_eq_div]

@[simp] theorem inverse_value (q : ℚ) : (inverse q).value = q⁻¹ :=
  Rat.ext (Rat.num_inv q).symm (Rat.den_inv q).symm

@[simp] theorem divide_value (q r : ℚ) : (divide q r).value = q/r := by simp [divide,div_eq_mul_inv]

@[simp] theorem le_value (q r : ℚ) : (le q r).value = decide (q ≤ r) :=
  decide_eq_decide.mpr (Rat.le_iff q r).symm

@[simp] theorem lt_value (q r : ℚ) : (lt q r).value = decide (q < r) := by
  by_cases hr : r ≤ q
  · simp [lt,hr,not_lt.mpr hr]
  · simp [lt,hr,lt_of_not_ge hr]

@[simp] theorem eqRat_value (q r : ℚ) : (eqRat q r).value = decide (q = r) := by
  apply Bool.eq_iff_iff.mpr
  simp only [eqRat,Run.bind_value,step_value,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  exact ⟨fun h => Rat.ext h.1 h.2, fun e => e ▸ ⟨rfl,rfl⟩⟩

private theorem sum_bits (x y : ℤ) {w : ℕ} (a : x.natAbs.size ≤ w) (b : y.natAbs.size ≤ w) :
    (x+y).natAbs.size ≤ w+1 := by
  apply (Nat.size_le_size (Int.natAbs_add_le ..)).trans
  rw [Nat.size_le,pow_succ]
  have h₁ := Nat.size_le.mp a
  have h₂ := Nat.size_le.mp b
  omega

theorem plus_work {q r : ℚ} {w : ℕ} (a : Fits w q) (b : Fits w r) :
    (plus q r).Bound (scalarSlots w) (scalarWidth w) := by
  have prod {i j : ℕ} (h : i.size ≤ w) (h' : j.size ≤ w) :
      (i*j).size ≤ 2*w := (size_mul_le ..).trans (by omega)
  have left : (q.num*(r.den : ℤ)).natAbs.size ≤ 2*w := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using prod a.1 b.2
  have right : ((q.den : ℤ)*r.num).natAbs.size ≤ 2*w := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using prod a.2 b.1
  have z := reduce_work _ _ (sum_bits _ _ left right) ((prod a.2 b.2).trans (Nat.le_succ _))
  obtain ⟨wn,wd⟩ := a
  obtain ⟨vn,vd⟩ := b
  simp only [plus,Run.Bound,Run.bind_slots,Run.bind_width,intMul,intAdd,natMul,step_value,step_slots,
    step_width,Int.natAbs_natCast,scalarSlots,scalarWidth] at z ⊢
  omega

theorem times_work {q r : ℚ} {w : ℕ} (a : Fits w q) (b : Fits w r) :
    (times q r).Bound (scalarSlots w) (scalarWidth w) := by
  have num : (q.num*r.num).natAbs.size ≤ 2*w := by
    rw [Int.natAbs_mul]
    exact (size_mul_le ..).trans (by have := a.1; have := b.1; omega)
  have den : (q.den*r.den).size ≤ 2*w := (size_mul_le ..).trans (by have := a.2; have := b.2; omega)
  have z := reduce_work _ _ num den
  obtain ⟨wn,wd⟩ := a
  obtain ⟨vn,vd⟩ := b
  simp only [times,Run.Bound,Run.bind_slots,Run.bind_width,intMul,natMul,step_value,step_slots,
    step_width,scalarSlots,scalarWidth] at z ⊢
  omega

theorem inverse_work {q : ℚ} {w : ℕ} (a : Fits w q) : (inverse q).Bound 4 (scalarWidth w) := by
  obtain ⟨hn,hd⟩ := a
  simp only [inverse,Run.Bound,Work.seq,Work.one,intMul,step_value,step_slots,step_width,
    Int.natAbs_natCast,Int.natAbs_sign,scalarWidth]
  split <;> simp <;> omega

theorem divide_work {q r : ℚ} {w : ℕ} (a : Fits w q) (b : Fits w r) :
    (divide q r).Bound (4+scalarSlots w) (scalarWidth w) := by
  unfold divide
  apply bound_bind (inverse_work b)
  rw [inverse_value]
  exact times_work a b.inv

theorem le_work {q r : ℚ} {w : ℕ} (a : Fits w q) (b : Fits w r) :
    (le q r).Bound 3 (scalarWidth w) := by
  have s := size_mul_le q.num.natAbs r.den
  have t := size_mul_le r.num.natAbs q.den
  obtain ⟨hn,hd⟩ := a
  obtain ⟨rn,rd⟩ := b
  simp only [le,Run.Bound,Run.bind_width,Run.bind_slots,intMul,step_width,step_slots,step_value,
    Int.natAbs_mul,Int.natAbs_natCast,scalarWidth]
  omega

theorem lt_work {q r : ℚ} {w : ℕ} (a : Fits w q) (b : Fits w r) :
    (lt q r).Bound 4 (scalarWidth w) :=
  bound_bind (le_work b a) ((bound_step 1 _).weaken le_rfl (by unfold scalarWidth; omega))

theorem eqRat_work {q r : ℚ} {w : ℕ} (a : Fits w q) (b : Fits w r) :
    (eqRat q r).Bound 3 (scalarWidth w) := by
  obtain ⟨hn,hd⟩ := a
  obtain ⟨rn,rd⟩ := b
  simp only [eqRat,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,scalarWidth]
  omega

end Kintali.TrialWork
