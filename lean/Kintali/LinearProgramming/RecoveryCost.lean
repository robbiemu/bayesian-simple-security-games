module

public import Kintali.LinearProgramming.RecoveryRun

/-! # Binary word-work bound from the stored input size

The input parameter bounds the dimensions and the binary lengths of the
coefficient, right-hand-side, numerator and common-denominator magnitudes.
The algorithm returns signed binary numerators and one shared denominator.
-/

@[expose] public section

namespace Kintali.LinearProgramming.RecoveryRun

open StochasticGames.CompilerRun StochasticGames.BinarySize PivotRun PointRun

def scale (S : ℕ) : ℕ := 64*(S+2)^3

def repairedHeight (n h B U D : ℕ) := max h (residualBound n h B U D)

private theorem size_add_le (a b : ℕ) : (a+b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have ha := (Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right a.size b.size))
  omega

structure InputBits (m n h B U D S : ℕ) : Prop where
  rows : m+2 ≤ S
  columns : n+1 ≤ S
  coefficients : h.size ≤ S
  rhs : B.size ≤ S
  numerators : U.size ≤ S
  denominator : D.size ≤ S

private structure Room (m n h B U D L : ℕ) : Prop where
  rows : m+2 ≤ L
  cols : n+1 ≤ L
  base : h.size+1 ≤ L
  rhs : B.size+1 ≤ L
  num : U.size+1 ≤ L
  den : D.size+1 ≤ L
  radix : (SlackWindow.radix n h).size ≤ L
  divisor : (SlackWindow.divisor m n h).size+1 ≤ L
  power : (SlackWindow.radix n h^(m+1)).size ≤ L
  endpoint : (D*SlackWindow.radix n h^(m+1)).size+1 ≤ L
  scaled : (SlackWindow.divisor m n h*residualBound n h B U D).size+1 ≤ L
  dot : ((n+1)*(h*U)).size+1 ≤ L
  residual : (residualBound n h B U D).size+1 ≤ L
  height : (repairedHeight n h B U D).size ≤ L
  minor : (minorBound n (repairedHeight n h B U D)).size+1 ≤ L
  shift : ((n+1)*minorBound n (repairedHeight n h B U D)).size+1 ≤ L
  product : (minorBound n (repairedHeight n h B U D)*U).size+1 ≤ L

private theorem room {m n h B U D S : ℕ} (hp : 0 < h) (input : InputBits m n h B U D S) :
    Room m n h B U D (scale S) := by
  obtain ⟨rows,cols,hb,bb,ub,db⟩ := input
  let R := residualBound n h B U D
  let H := repairedHeight n h B U D
  let C := minorBound n H
  let K := SlackWindow.radix n h
  let Q := SlackWindow.divisor m n h
  have sq : S+1 ≤ scale S := by unfold scale; ring_nf; omega
  unfold scale at sq
  have basepos : 0 < (S+2)^3 := by positivity
  have ns : n.size ≤ S := (size_le_self n).trans (by omega)
  have inc : (n+1).size ≤ S := (size_le_self _).trans cols
  have term : (h*U).size ≤ S+S := (size_mul_le ..).trans (Nat.add_le_add hb ub)
  have left : (D*B).size ≤ S+S := (size_mul_le ..).trans (Nat.add_le_add db bb)
  have nh : (n*h).size ≤ S+S := (size_mul_le ..).trans (Nat.add_le_add ns hb)
  have right : (n*h*U).size ≤ S+S+S := (size_mul_le ..).trans (Nat.add_le_add nh ub)
  have dot := (size_mul_le (n+1) (h*U)).trans (Nat.add_le_add inc term)
  have residual : R.size ≤ 3*S+1 := by
    apply (size_add_le _ _).trans
    omega
  have height : H.size ≤ 3*S+1 := by
    change (max h R).size ≤ _
    by_cases small : h ≤ R
    · rw [max_eq_right small]
      exact residual
    · rw [max_eq_left (by omega)]
      omega
  have minor : C.size ≤ 1+S*(S+(3*S+1)) := by
    apply (minorBound_size n H).trans
    gcongr; omega
  have shift := (size_mul_le (n+1) C).trans (Nat.add_le_add inc minor)
  have product := (size_mul_le C U).trans (Nat.add_le_add minor ub)
  have qp : Q.size ≤ 16*(S+2)^3 :=
    SlackWindow.divisor_size_polynomial (by omega) (by omega) hb
  have powLe : K^(m+1) ≤ Q := PrecisionRun.power_le_divisor m n hp
  have kpos : 0 < K := by dsimp [K,SlackWindow.radix]; omega
  have kLe : K ≤ K^(m+1) := by
    calc
      _ = K^1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right kpos (by omega)
  have raised := (Nat.size_le_size powLe).trans qp
  have radix := (Nat.size_le_size kLe).trans raised
  have ep := (size_mul_le D (K^(m+1))).trans (Nat.add_le_add db raised)
  have scaled := (size_mul_le Q R).trans (Nat.add_le_add qp residual)
  change Room m n h B U D (64*(S+2)^3)
  constructor
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · change K.size ≤ _
    omega
  · change Q.size+1 ≤ _
    omega
  · change (K^(m+1)).size ≤ _
    omega
  · change (D*K^(m+1)).size+1 ≤ _
    ring_nf at ep ⊢
    omega
  · change (Q*R).size+1 ≤ _
    ring_nf at scaled ⊢
    omega
  · ring_nf at dot ⊢
    omega
  · change R.size+1 ≤ _
    ring_nf at residual ⊢
    omega
  · change H.size ≤ _
    ring_nf at height ⊢
    omega
  · change C.size+1 ≤ _
    ring_nf at minor ⊢
    omega
  · change ((n+1)*C).size+1 ≤ _
    ring_nf at shift ⊢
    omega
  · change (C*U).size+1 ≤ _
    ring_nf at product ⊢
    omega

def transitionLimit (S : ℕ) : ℕ := 512*(scale S+2)^7

def operandLimit (S : ℕ) : ℕ := width (scale S)

/-- Complete word trace for the stored repair, including computation of its
precision. The input magnitude bounds are mathematical bounds and are not
read by the run. -/
theorem run_work {m n : ℕ} (P : Input m n) (X : Point n) {h B U S : ℕ} (hp : 0 < h)
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) (rhs : ∀ i, |P.system.rhs i| ≤ (B : ℤ))
    (nums : ∀ j, |X.scaled.num j| ≤ (U : ℤ)) (bits : InputBits m n h B U X.den S) :
    (run P X h).Bound (transitionLimit S) (operandLimit S) := by
  let L := scale S
  let w := width L
  let R := residualBound n h B U X.den
  let H := repairedHeight n h B U X.den
  let Q := SlackWindow.divisor m n h
  let K := SlackWindow.radix n h
  let p := (PrecisionRun.setup m n h).value
  let res := (PointRun.residuals P X).value
  let z := (PointRun.scaledResiduals Q res).value
  let mask := (classify res X.den p).value
  let s := (PivotRun.choose P mask).value
  have cap := room hp bits
  have ml : m+2 ≤ L := cap.rows
  have nl : n+1 ≤ L := cap.cols
  have lw : L ≤ w := by dsimp [w,width]; ring_nf; omega
  have iL : L.size ≤ w := (size_le_self _).trans lw
  have im : m.size ≤ w := (size_le_self _).trans (by omega)
  have ix : (m+2).size ≤ w := (size_le_self _).trans (ml.trans lw)
  have in' : n.size ≤ w := (size_le_self _).trans (by omega)
  have two : 2 ≤ w := by omega
  have hw : h.size+1 ≤ w := cap.base.trans lw
  have uw : U.size+1 ≤ w := cap.num.trans lw
  have bw : B.size+1 ≤ w := cap.rhs.trans lw
  have dw : X.den.size+1 ≤ w := cap.den.trans lw
  have qw : Q.size+1 ≤ w := cap.divisor.trans lw
  have rw' : R.size+1 ≤ w := cap.residual.trans lw
  have natural (j : Fin n) : (X.scaled.num j).natAbs ≤ U := ScalarRun.absWord (nums j)
  have bb (i : Fin m) : |res[i.val]| ≤ (R : ℤ) := by
    simp only [res, PointRun.residuals_value, Vector.getElem_ofFn]
    exact X.scaled.residual_bound P.system coeff rhs nums i
  have rn (i : Fin m) : res[i.val].natAbs ≤ R := ScalarRun.absWord (bb i)
  have zn (i : Fin m) : z[i.val].natAbs.size+1 ≤ w := by
    have mag : z[i.val].natAbs ≤ Q*R := by
      simp only [z, PointRun.scaledResiduals_value, Vector.getElem_ofFn, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul_left _ (rn i)
    exact (Nat.add_le_add_right (Nat.size_le_size mag) 1).trans (cap.scaled.trans lw)
  have init := PrecisionRun.setup_work hp (by omega : m+1 ≤ L) nl iL (by omega : h.size ≤ w)
    (by omega : Q.size ≤ w) two
  have tab := PointRun.residuals_work P X coeff rhs natural (by omega : m ≤ L) (by omega : n ≤ L)
    im in' hw uw bw dw (cap.dot.trans lw) rw'
  have sc := PointRun.scaledResiduals_work Q res rn (by omega : m ≤ L) im rw' qw
  have kpos : 0 < K := by dsimp [K,SlackWindow.radix]; omega
  have window := WindowRun.mark_work z X.den K L w kpos ml ix (by omega)
    (cap.radix.trans lw) (cap.power.trans lw) (cap.endpoint.trans lw) zn
  have cl : (classify res X.den p).Bound (6*(L+2)+48*(L+2)^3) w := by
    have pv : p = ⟨K,Q⟩ := PrecisionRun.setup_value ..
    rw [pv]
    exact bound_bind (f := fun z => WindowRun.mark z X.den K) sc window
  have hb : h.size+1 ≤ L := cap.base
  have selection := PivotRun.choose_work P mask coeff (by omega : m ≤ L) (by omega : n ≤ L) (by omega : h.size ≤ L)
  have reg : (s.view.matrix P.system).det ≠ 0 := by
    rw [show s.view = _ from PivotRun.choose_value P mask]
    exact (Minor.choose_spec ..).1
  have rank : s.rank ≤ n := s.view.rank_le P.system reg
  have hH : h ≤ H := le_max_left _ _
  have rH : R ≤ H := le_max_right _ _
  have height (i : Fin m) (j : Fin n) : |P.system.coeff i j| ≤ (H : ℤ) :=
    (coeff i j).trans (by exact_mod_cast hH)
  have rb (i : Fin m) : |res[i.val]| ≤ (H : ℤ) := (bb i).trans (by exact_mod_cast rH)
  have final := CramerRun.repair_work P X res s (hp.trans_le hH) height rb natural
    (by omega : m ≤ L) (by omega : n ≤ L) rank cap.height
    (cap.minor.trans lw) uw dw (cap.shift.trans lw) (cap.product.trans lw)
  constructor
  · change (PrecisionRun.setup m n h).work.slots + ((PointRun.residuals P X).work.slots +
      ((classify res X.den p).work.slots + ((PivotRun.choose P mask).work.slots +
        (CramerRun.repair P X res s).work.slots))) ≤ _
    apply Nat.le_trans (Nat.add_le_add init.1 (Nat.add_le_add tab.1 (Nat.add_le_add cl.1
      (Nat.add_le_add selection.1 final.1))))
    change _ ≤ 512*(L+2)^7
    ring_nf
    omega
  · exact max_le init.2 (max_le tab.2 (max_le cl.2 (max_le selection.2 final.2)))

/-- A dense binary input of dimensions and field widths bounded by S fits
within this many cells, including sign, length and record counters. -/
def cellAllowance (S : ℕ) := 8*(S+2)^3

def binaryWork (inputCells : ℕ) (work : Work) :=
  work.slots * wordCost (max work.width (addressWidth inputCells work.slots work.width))

def binaryLimit (S : ℕ) := transitionLimit S *
  (64*(cellAllowance S+transitionLimit S+3*operandLimit S+16)^3)

/-- Prices every observed transition at the existing binary word and
address cost. All functions on the right are explicit polynomials in S. -/
theorem run_binary_work {m n : ℕ} (P : Input m n) (X : Point n) {h B U S cells : ℕ}
    (hp : 0 < h) (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ))
    (rhs : ∀ i, |P.system.rhs i| ≤ (B : ℤ)) (nums : ∀ j, |X.scaled.num j| ≤ (U : ℤ))
    (bits : InputBits m n h B U X.den S) (cellsFit : cells ≤ cellAllowance S) :
    binaryWork cells (run P X h).work ≤ binaryLimit S := by
  let W := (run P X h).work
  have bounds := run_work P X hp coeff rhs nums bits
  have slots : W.slots ≤ transitionLimit S := bounds.1
  have operands : W.width ≤ operandLimit S := bounds.2
  have cw := size_le_self (cells+1)
  have sw := size_le_self (W.slots+1)
  have ww := size_le_self (W.width+1)
  have addrs : max W.width (addressWidth cells W.slots W.width)+1 ≤
      cellAllowance S+transitionLimit S+3*operandLimit S+16 := by
    unfold addressWidth
    omega
  exact Nat.mul_le_mul slots (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left addrs 3))

end Kintali.LinearProgramming.RecoveryRun
