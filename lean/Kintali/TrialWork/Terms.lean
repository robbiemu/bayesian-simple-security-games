module

public import Kintali.TrialWork.Fields

/-! Direct charged evaluation of the affine atoms and terms used by
the relaxed row checks. Each rational sum visits only types or sites. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun ContactSize ExactRecovery

variable {k m : ℕ}

def Fields.atom (d : Fields k m) (v : Point k m) : Atom (Fin k) (Fin m) → Run ℚ
  | .zero => step 0 0
  | .one => step 0 1
  | .budget => step d.budget.size (d.budget : ℚ)
  | .prior i => d.prior i
  | .coverage j => v.readX j
  | .coverageSum => sumFin m v.readX
  | .flow i j => v.readQ i j
  | .flowSum i => sumFin m (v.readQ i)
  | .cost i j => d.pointCost v i j
  | .pressure j => do
    let total ← sumFin k (fun i => v.readQ i j)
    let gain ← d.gain j
    times total gain
  | .threshold => step 0 v.threshold

@[simp] theorem Fields.atom_value (d : Fields k m) (v : Point k m) (a : Atom (Fin k) (Fin m)) :
    (d.atom v a).value = a.value d.game v.x v.q v.threshold := by
  cases a <;> simp [Fields.atom,Atom.value,Fields.game,Game.pressure,Game.cost]

def atomBits (n w : ℕ) := sumBits n w+3*w+2
def termBits (n w : ℕ) := atomBits n w+w+1
def checkWidth (n w : ℕ) := scalarWidth (termBits n w)
def atomSlots (n c w : ℕ) := 4+2*n+sumSlots n w 2+c+costSlots c w+scalarSlots (atomBits n w)
def termSlots (n c w : ℕ) := atomSlots n c w+1+scalarSlots (atomBits n w)

private theorem fitSum {n N w : ℕ} (f : Fin n → ℚ) (dim : n ≤ N) (fits : ∀ i, Fits w (f i)) :
    Fits (sumBits N w) (∑ i, f i) := by
  have h := Fits.sum Finset.univ f (fun i _ => fits i)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  exact h.mono (Nat.add_le_add_left (Nat.mul_le_mul_right _ dim) 1)

theorem Fields.atom_fits (d : Fields k m) {v : Point k m} {c n w : ℕ} (ok : FieldBound d c w)
    (point : PointBound v w) (hk : k ≤ n) (hm : m ≤ n) (a : Atom (Fin k) (Fin m)) :
    Fits (atomBits n w) (d.atom v a).value := by
  rw [Fields.atom_value]
  have u : w ≤ atomBits n w := by unfold atomBits; omega
  have s : sumBits n w ≤ atomBits n w := by unfold atomBits; omega
  cases a with
  | zero => exact Fits.zero.mono (ok.positive.trans u)
  | one => exact Fits.one.mono (ok.positive.trans u)
  | budget => exact ok.budget.mono u
  | prior i => exact (ok.prior i).2.mono u
  | coverage j => exact (point.coverage j).mono u
  | coverageSum => exact (fitSum _ hm point.coverage).mono s
  | flow i j => exact (point.joint i j).mono u
  | flowSum i => exact (fitSum _ hm (point.joint i)).mono s
  | cost i j => exact (d.cost_fits ok i j (point.coverage j)).mono (by unfold atomBits; omega)
  | pressure j =>
    exact ((fitSum _ hk (fun i => point.joint i j)).mul (ok.gain j).2).mono (by unfold atomBits; omega)
  | threshold => exact point.threshold.mono u

theorem Fields.atom_work (d : Fields k m) {v : Point k m} {c n w : ℕ} (ok : FieldBound d c w)
    (point : PointBound v w) (hk : k ≤ n) (hm : m ≤ n) (a : Atom (Fin k) (Fin m)) :
    (d.atom v a).Bound (atomSlots n c w) (checkWidth n w) := by
  let U := checkWidth n w
  let C := atomSlots n c w
  have wn : w ≤ U := by unfold U checkWidth scalarWidth termBits atomBits; omega
  have space : scalarWidth (addWidth n w) ≤ U := by
    unfold U checkWidth scalarWidth termBits atomBits addWidth; omega
  have width : scalarWidth (atomBits n w) ≤ U := by unfold U checkWidth scalarWidth termBits; omega
  have one : 1 ≤ C := by unfold C atomSlots; omega
  have summ (N : ℕ) (dim : N ≤ n) (idx : N.size ≤ w) (read : Fin N → Run ℚ)
      (each : ∀ i, (read i).Bound 2 w) (bits : ∀ i, Fits w (read i).value) :
      (sumFin N read).Bound (2*n+1+sumSlots n w 2) U :=
    sumFin_work N read dim (idx.trans wn) (fun i => (each i).weaken le_rfl wn) bits space
  cases a with
  | zero | one | threshold => exact (bound_step 0 _).weaken one (Nat.zero_le _)
  | budget =>
    have hb : d.budget.size ≤ w := by simpa using ok.budget.1
    exact (bound_step _ _).weaken one (hb.trans wn)
  | prior i => exact (ok.prior i).1.weaken (by unfold atomSlots; omega) wn
  | coverage j => exact (v.readX_bound j ok.mSize).weaken one wn
  | flow i j => exact (v.readQ_bound i j ok.kSize ok.mSize).weaken (by unfold atomSlots; omega) wn
  | coverageSum =>
    exact (summ m hm ok.mSize v.readX (fun j => (v.readX_bound j ok.mSize).weaken (by decide) le_rfl)
      point.coverage).weaken (by unfold atomSlots; omega) le_rfl
  | flowSum i =>
    exact (summ m hm ok.mSize (v.readQ i) (fun j => v.readQ_bound i j ok.kSize ok.mSize)
      (point.joint i)).weaken (by unfold atomSlots; omega) le_rfl
  | cost i j =>
    exact (d.pointCost_work ok point i j).weaken (by unfold atomSlots; omega)
      (by simp only [checkWidth,scalarWidth,termBits,atomBits,costWidth]; omega)
  | pressure j =>
    have total := summ k hk ok.kSize (fun i => v.readQ i j)
      (fun i => v.readQ_bound i j ok.kSize ok.mSize) (fun i => point.joint i j)
    have fit : Fits (atomBits n w) (sumFin k (fun i => v.readQ i j)).value := by
      rw [sumFin_value]
      exact (fitSum _ hk (fun i => point.joint i j)).mono (by unfold atomBits; omega)
    apply Run.Bound.weaken (k := (2*n+1+sumSlots n w 2)+(c+scalarSlots (atomBits n w))) (w := U) ?_
      (by unfold atomSlots; omega) le_rfl
    apply bound_bind total
    apply bound_bind ((ok.gain j).1.weaken le_rfl wn)
    exact (times_work fit ((ok.gain j).2.mono (by unfold atomBits; omega))).weaken le_rfl width

def Fields.term (d : Fields k m) (v : Point k m) (t : Term (Fin k) (Fin m)) : Run ℚ := do
  let a ← d.atom v t.atom
  let e ← step 1 (if t.residual then v.tolerance else 0)
  plus a e

@[simp] theorem Fields.term_value (d : Fields k m) (v : Point k m) (t : Term (Fin k) (Fin m)) :
    (d.term v t).value = t.value d.game v.x v.q v.threshold v.tolerance := by
  simp [Fields.term,Term.value]

theorem Fields.term_work (d : Fields k m) {v : Point k m} {n c w : ℕ} (ok : FieldBound d c w)
    (point : PointBound v w) (hk : k ≤ n) (hm : m ≤ n) (t : Term (Fin k) (Fin m)) :
    (d.term v t).Bound (termSlots n c w) (checkWidth n w) ∧ Fits (termBits n w) (d.term v t).value := by
  have eb : Fits w (if t.residual then v.tolerance else 0) := by
    split
    · exact point.tolerance
    · exact Fits.zero.mono ok.positive
  have small := d.atom_fits ok point hk hm t.atom
  constructor
  · unfold Fields.term
    apply Run.Bound.weaken (k := atomSlots n c w+(1+scalarSlots (atomBits n w))) (w := checkWidth n w) ?_
      (by unfold termSlots; omega) le_rfl
    apply bound_bind (d.atom_work ok point hk hm t.atom)
    apply bound_bind ((bound_step 1 _).weaken le_rfl (by unfold checkWidth scalarWidth; omega))
    exact (plus_work small (eb.mono (by unfold atomBits; omega))).weaken le_rfl
      (by unfold checkWidth scalarWidth termBits; omega)
  · simp only [Fields.term,Run.bind_value,step_value,plus_value]
    exact small.add eb

end Kintali.TrialWork
