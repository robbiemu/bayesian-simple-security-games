module

public import Kintali.LinearProgramming.PointRun

/-! # Stored Cramer numerators for a selected pivot

The pivot determinant and each replaced-column determinant are evaluated
once. The stored correction vector is then scattered into the output
coordinates, all of which share one signed denominator.
-/

@[expose] public section

namespace Kintali.LinearProgramming.CramerRun

open StochasticGames.CompilerRun StochasticGames.BinarySize PivotRun PointRun

variable {m n : ℕ}

def column (s : State m n) (res : Vector ℤ m) : Fin s.rank → ℤ :=
  fun i => res[(s.view.rows i).val]

def replace (P : Input m n) (s : State m n) (res : Vector ℤ m) (t : Fin s.rank) :
    Matrix (Fin s.rank) (Fin s.rank) ℤ :=
  (s.view.matrix P.system).updateCol t (column s res)

/-- Materializing a candidate uses the row and column maps, the stored
matrix or residual vector, and the column equality test. -/
def determinantAt (P : Input m n) (s : State m n) (res : Vector ℤ m) (t : Fin s.rank) : Run ℤ := do
  let M ← ArithmeticRun.tabulate s.rank fun i => ArithmeticRun.tabulate s.rank fun j =>
    (⟨replace P s res t i j, ⟨6,m.size+n.size+s.rank.size+2⟩⟩ : Run ℤ)
  BirdRun.compute M

def corrections (P : Input m n) (s : State m n) (res : Vector ℤ m) : Run (Vector ℤ s.rank) :=
  ArithmeticRun.tabulate s.rank (determinantAt P s res)

@[simp] theorem determinantAt_value (P : Input m n) (s : State m n) (res : Vector ℤ m) (t : Fin s.rank) :
    (determinantAt P s res t).value = (replace P s res t).det := by
  simp only [determinantAt, Run.bind_value, ArithmeticRun.tabulate_value, BirdRun.compute_value]
  exact congrArg Matrix.det (Bird.entries_tabulate _)

@[simp] theorem corrections_value (P : Input m n) (s : State m n) (res : Vector ℤ m) :
    (corrections P s res).value = Vector.ofFn ((s.view.matrix P.system).cramer (column s res)) := by
  simp only [corrections, ArithmeticRun.tabulate_value, determinantAt_value]
  apply congrArg Vector.ofFn
  funext t
  exact (Matrix.cramer_apply _ _ _).symm

theorem replace_bound (P : Input m n) (s : State m n) (res : Vector ℤ m) {H : ℕ}
    (coeff : ∀ i j, |P.system.coeff i j| ≤ (H : ℤ)) (rb : ∀ i : Fin m, |res[i.val]| ≤ (H : ℤ))
    (t i j : Fin s.rank) : |replace P s res t i j| ≤ (H : ℤ) := by
  by_cases same : j = t
  · subst j
    unfold replace
    rw [Matrix.updateCol_self]
    exact rb (s.view.rows i)
  · unfold replace
    rw [Matrix.updateCol_ne same]
    exact coeff (s.view.rows i) (s.view.cols j)

theorem determinantAt_work (P : Input m n) (s : State m n) (res : Vector ℤ m)
    (t : Fin s.rank) {H L : ℕ} (coeff : ∀ i j, |P.system.coeff i j| ≤ (H : ℤ))
    (rb : ∀ i : Fin m, |res[i.val]| ≤ (H : ℤ)) (hm : m ≤ L) (hn : n ≤ L)
    (hk : s.rank ≤ L) (bits : H.size ≤ L) :
    (determinantAt P s res t).Bound (detSlots L) (width L) := by
  let cell := fun i j : Fin s.rank =>
    (⟨replace P s res t i j, ⟨6,m.size+n.size+s.rank.size+2⟩⟩ : Run ℤ)
  let A := ArithmeticRun.tabulate s.rank fun i => ArithmeticRun.tabulate s.rank (cell i)
  have im := (size_le_self m).trans hm
  have in' := (size_le_self n).trans hn
  have ik := (size_le_self s.rank).trans hk
  have iw : m.size+n.size+s.rank.size+2 ≤ width L := by unfold width; ring_nf; omega
  have idx : s.rank.size ≤ width L := by omega
  have cells (i j : Fin s.rank) : (cell i j).Bound 6 (width L) := ⟨le_rfl,iw⟩
  have cap := ArithmeticRun.tabulate_bound _ idx (fun i => ArithmeticRun.tabulate_bound _ idx (cells i))
  have val : Bird.entries A.value = replace P s res t := by
    simp only [A, ArithmeticRun.tabulate_value]
    exact Bird.entries_tabulate _
  have hA (i j : Fin s.rank) : |Bird.entries A.value i j| ≤ (H : ℤ) := by
    rw [val]
    exact replace_bound P s res coeff rb t i j
  have d := BirdRun.compute_work A.value hA
  have wd := BirdRun.wordWidth_polynomial hk bits hk
  have dw : (BirdRun.compute A.value).work.width ≤ width L :=
    d.2.trans (wd.trans (by unfold width; omega))
  have calls : 3*(s.rank+1)+s.rank*(3*(s.rank+1)+s.rank*6) + 40*(s.rank+1)^4 ≤ detSlots L := by
    calc
      _ ≤ 3*(L+1)+L*(3*(L+1)+L*6) + 40*(L+1)^4 := by gcongr
      _ ≤ _ := by unfold detSlots; ring_nf; omega
  exact (bound_bind (f := BirdRun.compute) cap ⟨d.1,dw⟩).weaken calls le_rfl

structure Answer (n : ℕ) where
  num : Vector ℤ n
  den : ℤ
  deriving Repr

def Answer.value (A : Answer n) (j : Fin n) : ℚ := Rat.divInt A.num[j.val] A.den

def place (s : State m n) (v : Vector ℤ s.rank) (j : Fin n) : Run ℤ :=
  ScalarRun.dot (fun t => (⟨s.view.selector j t,⟨3,max n.size s.rank.size⟩⟩ : Run ℤ))
    (fun t => step s.rank.size v[t.val])

def output (X : Point n) (s : State m n) (v : Vector ℤ s.rank) (d : ℤ) : Run (Answer n) := do
  let nums ← ArithmeticRun.tabulate n fun j => do
    let shift ← place s v j
    let x ← step n.size X.num[j.val]
    let dx ← intMul d x
    intAdd dx shift
  let den ← intMul d (X.den : ℤ)
  step 0 ⟨nums,den⟩

def repair (P : Input m n) (X : Point n) (res : Vector ℤ m) (s : State m n) : Run (Answer n) := do
  let d ← determinantOf P s
  let v ← corrections P s res
  output X s v d

@[simp] theorem place_value (s : State m n) (v : Vector ℤ s.rank) (j : Fin n) :
    (place s v j).value = s.view.selector.mulVec (fun t => v[t.val]) j := by
  simp [place, Matrix.mulVec]

theorem repair_value (P : Input m n) (X : Point n) (res : Vector ℤ m) (s : State m n)
    (rows : ∀ i : Fin m, res[i.val] = X.scaled.residual P.system i)
    (regular : (s.view.matrix P.system).det ≠ 0) :
    (repair P X res s).value.value = (s.view.pivot P.system).repair P.system X.scaled.value := by
  let M := s.view.matrix P.system
  let r := column s res
  have lift : (s.view.pivot P.system).lift.mulVec r = s.view.selector.mulVec (M.cramer r) := by
    change (s.view.selector * Minor.adjugate M).mulVec r = _
    rw [Minor.adjugate_eq, ← Matrix.mulVec_mulVec, Matrix.cramer_eq_adjugate_mulVec]
  have rr : (fun t => X.scaled.residual P.system ((s.view.pivot P.system).rows t)) = r :=
    funext fun t => (rows (s.view.rows t)).symm
  funext j
  rw [X.scaled.repair_eq_divInt P.system _ (by simpa [Minor.pivot] using regular)]
  simp only [repair, output, Run.bind_value, determinantOf_value, corrections_value, Answer.value,
    step_value, ArithmeticRun.tabulate_value, intMul, intAdd, Vector.getElem_ofFn]
  unfold ScaledPoint.numerator
  rw [rr, lift]
  simp [Minor.pivot, Point.scaled, M, r, place_value]

end Kintali.LinearProgramming.CramerRun
