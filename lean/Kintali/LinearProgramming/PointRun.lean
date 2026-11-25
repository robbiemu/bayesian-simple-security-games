module

public import Kintali.LinearProgramming.ScalarRun

/-! # Stored integer input points and computation of every row residual -/

@[expose] public section

namespace Kintali.LinearProgramming.PointRun

open StochasticGames.CompilerRun
open PivotRun

variable {m n : ℕ}

structure Point (n : ℕ) where
  num : Vector ℤ n
  den : ℕ
  positive : 0 < den

def Point.scaled (X : Point n) : ScaledPoint n :=
  ⟨fun j => X.num[j.val], X.den, X.positive⟩

def residual (P : Input m n) (X : Point n) (i : Fin m) : Run ℤ := do
  let dot ← ScalarRun.dot
    (fun j : Fin n => (⟨P.system.coeff i j,⟨2, max m.size n.size⟩⟩ : Run ℤ))
    (fun j : Fin n => step n.size X.num[j.val])
  let b ← step m.size P.rhs[i.val]
  let rhs ← intMul (X.den : ℤ) b
  intSub rhs dot

def residuals (P : Input m n) (X : Point n) : Run (Vector ℤ m) :=
  ArithmeticRun.tabulate m (residual P X)

def scaledResiduals (Q : ℕ) (res : Vector ℤ m) : Run (Vector ℤ m) :=
  ArithmeticRun.tabulate m fun i => do
    let r ← step m.size res[i.val]
    intMul (Q : ℤ) r

@[simp] theorem residual_value (P : Input m n) (X : Point n) (i : Fin m) :
    (residual P X i).value = X.scaled.residual P.system i := by
  simp [residual, ScaledPoint.residual, intSub, intMul, Point.scaled, Input.system, Matrix.mulVec]

@[simp] theorem residuals_value (P : Input m n) (X : Point n) :
    (residuals P X).value = Vector.ofFn (X.scaled.residual P.system) := by
  simp [residuals]

@[simp] theorem scaledResiduals_value (Q : ℕ) (res : Vector ℤ m) :
    (scaledResiduals Q res).value = Vector.ofFn (fun i : Fin m => (Q : ℤ) * res[i.val]) := by
  simp [scaledResiduals, intMul]

def residualBound (n h B U D : ℕ) := D*B + n*h*U

theorem residuals_work (P : Input m n) (X : Point n) {h B U L w : ℕ}
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) (rhs : ∀ i, |P.system.rhs i| ≤ (B : ℤ))
    (numerators : ∀ j, (X.scaled.num j).natAbs ≤ U)
    (hm : m ≤ L) (hn : n ≤ L) (mw : m.size ≤ w) (nw : n.size ≤ w)
    (hw : h.size+1 ≤ w) (uw : U.size+1 ≤ w) (bw : B.size+1 ≤ w) (dw : X.den.size+1 ≤ w)
    (dotWidth : ((n+1)*(h*U)).size+1 ≤ w) (resWidth : (residualBound n h B U X.den).size+1 ≤ w) :
    (residuals P X).Bound (24*(L+2)^2) w := by
  have single (i : Fin m) : (residual P X i).Bound (7+n*8) w := by
    let a := fun j : Fin n => (⟨P.system.coeff i j,⟨2,max m.size n.size⟩⟩ : Run ℤ)
    let b := fun j : Fin n => step n.size X.num[j.val]
    have dot := ScalarRun.dot_bound a b
      (fun j => ScalarRun.absWord (coeff i j)) (fun j => numerators j)
      (fun _ => (show (a _).Bound 2 w from ⟨le_rfl,max_le mw nw⟩))
      (fun _ => (show (b _).Bound 1 w from ⟨le_rfl,nw⟩)) nw hw uw dotWidth
    have absB : (P.rhs[i.val]).natAbs ≤ B := ScalarRun.absWord (rhs i)
    have dnat : (X.den : ℤ).natAbs ≤ X.den := by simp
    have multW := ScalarRun.signedWidth dnat absB dw bw
    have rh : (((X.den : ℤ)*P.rhs[i.val]).natAbs) ≤ X.den*B := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul dnat absB
    have dotmag : (ScalarRun.dot a b).value.natAbs ≤ n*(h*U) := by
      unfold ScalarRun.dot
      simp only [Run.bind_value, finRange_value]
      have each (j : Fin n) : ((a j).value*(b j).value).natAbs ≤ h*U := by
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (ScalarRun.absWord (coeff i j)) (numerators j)
      exact (ArithmeticRun.sum_magnitude _ each _).trans (by simp)
    have rhsWide : (X.den*B).size+1 ≤ w :=
      (Nat.add_le_add_right (Nat.size_le_size (Nat.le_add_right _ _)) 1).trans resWidth
    have dotLe : n*(h*U) ≤ (n+1)*(h*U) := Nat.mul_le_mul_right _ (Nat.le_succ _)
    have subW := ScalarRun.signedWidth rh (dotmag.trans dotLe) rhsWide dotWidth
    constructor
    · change (ScalarRun.dot a b).work.slots + (1+(1+1)) ≤ _
      have ds := dot.1
      omega
    · exact max_le dot.2 (max_le mw (max_le multW subW))
  have table := ArithmeticRun.tabulate_bound _ mw single
  apply table.weaken _ le_rfl
  calc
    _ ≤ 3*(L+1) + L*(7+L*8) := by gcongr
    _ ≤ _ := by ring_nf; omega

theorem scaledResiduals_work (Q : ℕ) (res : Vector ℤ m) {B L w : ℕ}
    (bounded : ∀ i : Fin m, res[i.val].natAbs ≤ B) (hm : m ≤ L) (mw : m.size ≤ w)
    (bw : B.size+1 ≤ w) (qw : Q.size+1 ≤ w) :
    (scaledResiduals Q res).Bound (6*(L+2)) w := by
  have single (i : Fin m) :
      (step m.size res[i.val] >>= fun r => intMul (Q : ℤ) r).Bound 2 w := by
    have q : (Q : ℤ).natAbs ≤ Q := by simp
    exact ⟨le_rfl,max_le mw (ScalarRun.signedWidth q (bounded i) qw bw)⟩
  exact (ArithmeticRun.tabulate_bound _ mw single).weaken (by omega) le_rfl

end Kintali.LinearProgramming.PointRun
