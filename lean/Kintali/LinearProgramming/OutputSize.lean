module

public import Kintali.LinearProgramming.RationalInput

/-! # Binary lengths of the actual stored answer fields -/

@[expose] public section

namespace Kintali.LinearProgramming.OutputSize

open StochasticGames.CompilerRun StochasticGames.BinarySize PivotRun PointRun CramerRun

variable {m n : ℕ}

private theorem cell_le {α : Type} (f : Fin n → Run α) (j : Fin n) :
    (f j).work.width ≤ (ArithmeticRun.tabulate n f).work.width := by
  simp only [ArithmeticRun.tabulate, Vector.getElem_ofFn]
  exact (Finset.le_sup (f := fun i : Fin n => (f i).work.width) (Finset.mem_univ j)).trans (le_max_right _ _)

private theorem add_size (a b : ℤ) :
    (a+b).natAbs.size ≤ max a.natAbs.size b.natAbs.size+1 := by
  apply (Nat.size_le_size (Int.natAbs_add_le ..)).trans
  rw [Nat.size_le, pow_succ]
  have ha := (Nat.lt_size_self a.natAbs).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left a.natAbs.size b.natAbs.size))
  have hb := (Nat.lt_size_self b.natAbs).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right a.natAbs.size b.natAbs.size))
  omega

theorem output_fields (X : Point n) (s : State m n) (v : Vector ℤ s.rank) (d : ℤ) :
    let z := output X s v d
    z.value.den.natAbs.size ≤ 2*z.work.width ∧
      ∀ j : Fin n, z.value.num[j.val].natAbs.size ≤ z.work.width := by
  let cell := fun j : Fin n => do
    let shift ← place s v j
    let x ← step n.size X.num[j.val]
    let dx ← intMul d x
    intAdd dx shift
  let table := ArithmeticRun.tabulate n cell
  let z := output X s v d
  have tw : table.work.width ≤ z.work.width := le_max_left _ _
  have dw : (intMul d (X.den : ℤ)).work.width ≤ z.work.width :=
    (le_max_left _ _).trans (le_max_right _ _)
  have den : z.value.den.natAbs.size ≤ 2*z.work.width := by
    change (d*(X.den : ℤ)).natAbs.size ≤ _
    rw [Int.natAbs_mul]
    apply (size_mul_le ..).trans
    change max d.natAbs.size (X.den : ℤ).natAbs.size+1 ≤ z.work.width at dw
    omega
  refine ⟨den,?_⟩
  intro j
  have width := (cell_le cell j).trans tw
  let dx := d*X.num[j.val]
  let shift := (place s v j).value
  have addw : max dx.natAbs.size shift.natAbs.size+1 ≤ (cell j).work.width :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have num : z.value.num[j.val] = dx+shift := by
    simp only [z, output, Run.bind_value, ArithmeticRun.tabulate_value, step_value, intMul, intAdd,
      Vector.getElem_ofFn]
    rfl
  rw [num]
  exact (add_size ..).trans (addw.trans width)

theorem repair_fields (P : Input m n) (X : Point n) (res : Vector ℤ m) (s : State m n) :
    let z := CramerRun.repair P X res s
    z.value.den.natAbs.size ≤ 2*z.work.width ∧
      ∀ j : Fin n, z.value.num[j.val].natAbs.size ≤ z.work.width := by
  let z := output X s (corrections P s res).value (determinantOf P s).value
  have le : z.work.width ≤ (CramerRun.repair P X res s).work.width :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨den,nums⟩ := output_fields X s (corrections P s res).value (determinantOf P s).value
  exact ⟨den.trans (Nat.mul_le_mul_left 2 le), fun j => (nums j).trans le⟩

theorem run_fields (P : Input m n) (X : Point n) (h : ℕ) :
    let z := RecoveryRun.run P X h
    z.value.den.natAbs.size ≤ 2*z.work.width ∧
      ∀ j : Fin n, z.value.num[j.val].natAbs.size ≤ z.work.width := by
  let p := (PrecisionRun.setup m n h).value
  let res := (PointRun.residuals P X).value
  let mask := (RecoveryRun.classify res X.den p).value
  let s := (PivotRun.choose P mask).value
  have le : (CramerRun.repair P X res s).work.width ≤ (RecoveryRun.run P X h).work.width :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  obtain ⟨den,nums⟩ := repair_fields P X res s
  exact ⟨den.trans (Nat.mul_le_mul_left 2 le), fun j => (nums j).trans le⟩

theorem rational_fields (P : Input m n) (x : Vector ℚ n) (h : ℕ) :
    let z := RationalInput.run P x h
    z.value.den.natAbs.size ≤ 2*z.work.width ∧
      ∀ j : Fin n, z.value.num[j.val].natAbs.size ≤ z.work.width := by
  let X := (PointEncoding.encode x).value
  have le : (RecoveryRun.run P X h).work.width ≤ (RationalInput.run P x h).work.width :=
    le_max_right _ _
  obtain ⟨den,nums⟩ := run_fields P X h
  exact ⟨den.trans (Nat.mul_le_mul_left 2 le), fun j => (nums j).trans le⟩

end Kintali.LinearProgramming.OutputSize
