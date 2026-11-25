module

public import Kintali.LinearProgramming.CramerRun

/-! # Work and operand sizes of the cached Cramer repair -/

@[expose] public section

namespace Kintali.LinearProgramming.CramerRun

open StochasticGames.CompilerRun StochasticGames.BinarySize PivotRun PointRun

variable {m n : ℕ}

private theorem selector_mag (s : State m n) (j : Fin n) (t : Fin s.rank) :
    (s.view.selector j t).natAbs ≤ 1 := by
  change (if s.view.cols t = j then (1 : ℤ) else 0).natAbs ≤ 1
  split <;> decide

private theorem place_magnitude (s : State m n) (v : Vector ℤ s.rank) (j : Fin n) {C : ℕ}
    (bounded : ∀ t : Fin s.rank, v[t.val].natAbs ≤ C) :
    (place s v j).value.natAbs ≤ s.rank*C := by
  unfold place ScalarRun.dot
  simp only [Run.bind_value, finRange_value]
  apply (ArithmeticRun.sum_magnitude _ (B := C) _ _).trans
  · simp
  · intro t
    change ((s.view.selector j t) * v[t.val]).natAbs ≤ C
    rw [Int.natAbs_mul]
    simpa using Nat.mul_le_mul (selector_mag s j t) (bounded t)

theorem output_work (X : Point n) (s : State m n) (v : Vector ℤ s.rank) (d : ℤ) {C U L w : ℕ}
    (hk : s.rank ≤ n) (hn : n ≤ L) (fit : n.size ≤ w) (two : 2 ≤ w)
    (bounds : ∀ t : Fin s.rank, v[t.val].natAbs ≤ C) (det : d.natAbs ≤ C)
    (nums : ∀ j, (X.scaled.num j).natAbs ≤ U)
    (cb : C.size+1 ≤ w) (ub : U.size+1 ≤ w) (db : X.den.size+1 ≤ w)
    (shift : ((n+1)*C).size+1 ≤ w) (prod : (C*U).size+1 ≤ w) :
    (output X s v d).Bound (24*(L+2)^2) w := by
  have ki := (Nat.size_le_size hk).trans fit
  have sh (t : ℕ) (le : t ≤ n+1) : (t*C).size+1 ≤ w :=
    (Nat.add_le_add_right (Nat.size_le_size (Nat.mul_le_mul_right C le)) 1).trans shift
  have cell (j : Fin n) :
      (place s v j >>= fun z => step n.size X.num[j.val] >>= fun x => intMul d x >>= fun dx => intAdd dx z).Bound
        (7+s.rank*9) w := by
    let a := fun t : Fin s.rank => (⟨s.view.selector j t,⟨3,max n.size s.rank.size⟩⟩ : Run ℤ)
    let b := fun t : Fin s.rank => step s.rank.size v[t.val]
    have pc := ScalarRun.dot_bound a b (fun t => selector_mag s j t) bounds
      (fun _ => (show (a _).Bound 3 w from ⟨le_rfl,max_le fit ki⟩))
      (fun _ => (show (b _).Bound 1 w from ⟨le_rfl,ki⟩)) ki two cb (by simpa using sh (s.rank+1) (by omega))
    have source := nums j
    have dw := ScalarRun.signedWidth det source cb ub
    have dx : (d*X.num[j.val]).natAbs ≤ C*U := by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul det source
    have zw := place_magnitude s v j bounds
    have last := ScalarRun.signedWidth dx zw prod (sh s.rank (by omega))
    constructor
    · change (place s v j).work.slots + (1+(1+1)) ≤ _
      have pcs := pc.1
      change (place s v j).work.slots ≤ _ at pcs
      omega
    · exact max_le pc.2 (max_le fit (max_le dw last))
  have table := ArithmeticRun.tabulate_bound _ fit cell
  have den : (X.den : ℤ).natAbs ≤ X.den := by simp
  have wden := ScalarRun.signedWidth det den cb db
  constructor
  · change _ + (1+1) ≤ _
    exact (Nat.add_le_add_right table.1 2).trans (by
      calc
        _ ≤ 3*(L+1)+L*(7+L*9)+2 := by gcongr; omega
        _ ≤ _ := by ring_nf; omega)
  · exact max_le table.2 (max_le wden (Nat.zero_le _))

theorem repair_work (P : Input m n) (X : Point n) (res : Vector ℤ m) (s : State m n)
    {H U L : ℕ} (hp : 0 < H) (coeff : ∀ i j, |P.system.coeff i j| ≤ (H : ℤ))
    (rb : ∀ i : Fin m, |res[i.val]| ≤ (H : ℤ)) (nums : ∀ j, (X.scaled.num j).natAbs ≤ U)
    (hm : m ≤ L) (hn : n ≤ L) (hk : s.rank ≤ n) (height : H.size ≤ L)
    (cb : (minorBound n H).size+1 ≤ width L)
    (ub : U.size+1 ≤ width L) (db : X.den.size+1 ≤ width L)
    (shift : ((n+1)*minorBound n H).size+1 ≤ width L)
    (prod : (minorBound n H*U).size+1 ≤ width L) :
    (repair P X res s).Bound (96*(L+2)^5) (width L) := by
  let C := minorBound n H
  have mag : minorBound s.rank H ≤ C := Nat.mul_le_mul (Nat.factorial_le hk) (Nat.pow_le_pow_right hp hk)
  have small := hk.trans hn
  have ni : n.size ≤ width L := (size_le_self n).trans (hn.trans (by unfold width; ring_nf; omega))
  have ki := (Nat.size_le_size hk).trans ni
  have first := determinantOf_work P s coeff hm hn small height
  have all := ArithmeticRun.tabulate_bound _ ki (fun t => determinantAt_work P s res t coeff rb hm hn small height)
  let d := (determinantOf P s).value
  let v := (corrections P s res).value
  have vd (t : Fin s.rank) : v[t.val].natAbs ≤ C := by
    simp only [v, corrections, ArithmeticRun.tabulate_value, Vector.getElem_ofFn, determinantAt_value]
    rw [← determinant_eq]
    exact (determinant_natAbs_le _ (replace_bound P s res coeff rb t)).trans mag
  have dd : d.natAbs ≤ C := by
    simp only [d, determinantOf_value]
    rw [← determinant_eq]
    exact (determinant_natAbs_le _ (fun _ _ => coeff _ _)).trans mag
  have last := output_work X s v d hk hn ni (by unfold width; ring_nf; omega) vd dd nums cb ub db shift prod
  constructor
  · change (determinantOf P s).work.slots + ((corrections P s res).work.slots + (output X s v d).work.slots) ≤ _
    apply Nat.le_trans (Nat.add_le_add first.1 (Nat.add_le_add all.1 last.1))
    calc
      _ ≤ detSlots L + (3*(L+1)+L*detSlots L + 24*(L+2)^2) := by gcongr
      _ ≤ _ := by unfold detSlots; ring_nf; omega
  · exact max_le first.2 (max_le all.2 last.2)

end Kintali.LinearProgramming.CramerRun
