module

public import Kintali.InputOutput.DatumWork

/-! # Computing the recovery denominator and numerator magnitude

The denominator multiplies each *distinct rational's* denominator, matching
the project's finite set even when two different values share a denominator.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.InputOutput.DatumWork

open Binary NormalizedWork TrialWork ContactSize ExactRecovery StochasticGames.CompilerRun StochasticGames.BinarySize

structure ScaleData where
  denominator : ℕ
  magnitude : ℕ

def factors : List ℚ → Run ScaleData
  | [] => step 0 ⟨1,1⟩
  | x::xs => do
    let tail ← factors xs
    let d ← natMul x.den tail.denominator
    let n ← step (x.num.natAbs.size+1) x.num.natAbs
    let m ← step (max n.size tail.magnitude.size) (max n tail.magnitude)
    step 0 ⟨d,m⟩

theorem factors_value (xs : List ℚ) (h : xs.Nodup) :
    (factors xs).value = ⟨∏ q ∈ xs.toFinset, q.den, max 1 (xs.toFinset.sup fun q => q.num.natAbs)⟩ := by
  induction xs with
  | nil => simp [factors]
  | cons q xs ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp h
    simp only [factors,Run.bind_value,natMul,step_value,ih nd,List.toFinset_cons]
    rw [Finset.prod_insert (by simpa using fresh),Finset.sup_insert]
    congr 1
    change max q.num.natAbs (max 1 _) = max 1 (max q.num.natAbs _)
    ac_rfl

theorem factors_size (xs : List ℚ) {w : ℕ} (one : 1 ≤ w) (fit : ∀ q ∈ xs, Fits w q) :
    (factors xs).value.denominator.size ≤ 1+xs.length*w ∧ (factors xs).value.magnitude.size ≤ w := by
  induction xs with
  | nil => simpa [factors] using one
  | cons q xs ih =>
    have t := ih (fun z hz => fit z (List.mem_cons_of_mem _ hz))
    have qf := fit q (by simp)
    have d := size_mul_le q.den (factors xs).value.denominator
    simp only [factors,Run.bind_value,step_value,natMul,List.length_cons,Nat.succ_mul]
    have hn := qf.1
    have hd := qf.2
    rw [Nat.max_def]
    split <;> omega

theorem factors_work (xs : List ℚ) {N w : ℕ} (len : xs.length ≤ N) (one : 1 ≤ w)
    (fit : ∀ q ∈ xs, Fits w q) : (factors xs).Bound (4*xs.length+1) (1+N*w+w) := by
  induction xs with
  | nil => exact (bound_step _ _).weaken le_rfl (Nat.zero_le _)
  | cons q xs ih =>
    have qf := fit q (by simp)
    have tf (z) (hz : z ∈ xs) := fit z (List.mem_cons_of_mem _ hz)
    have l : xs.length ≤ N := by simp at len; omega
    have tail := ih l tf
    have ts := factors_size xs one tf
    have mul := Nat.mul_le_mul_right w l
    have hn := qf.1
    have hd := qf.2
    simp only [factors,Run.Bound,Run.bind_slots,Run.bind_width,natMul,step_value,step_slots,step_width,List.length_cons] at *
    omega

def collect {k m : ℕ} (d : Fields k m) : Run ScaleData := do
  let xs ← enumerate d
  let us ← unique xs
  factors us

theorem collect_value {k m : ℕ} (d : Fields k m) :
    (collect d).value = ⟨denominator d.game,magnitude d.game⟩ := by
  have spec := unique_spec (elements d)
  simp only [collect,Run.bind_value,enumerate_value,factors_value _ spec.2.1,spec.1,elements_set,denominator,magnitude]

def scaleSlots (S : ℕ) := enumSlots S 2 + (1+listBound S*(4*listBound S+2))+(4*listBound S+1)
def scaleWidth (S : ℕ) := scalarWidth (2*S+1)+1+listBound S*(2*S+1)+(2*S+1)

theorem collect_work (a : Input) (v : a.Valid) (t : Tables a.types a.targets) (ht : t.game = a.game) :
    (collect t.fields).Bound (scaleSlots (lengthInput a)) (scaleWidth (lengthInput a)) := by
  let S := lengthInput a
  let W := 2*S+1
  let N := listBound S
  let d := t.fields
  let xs := elements d
  let us := (unique xs).value
  have kd : a.types ≤ S := (dimensions a).2.1
  have md : a.targets ≤ S := (dimensions a).1
  have budget := (dimensions a).2.2
  have eq : d.game = a.game := ht
  have b : d.budget = a.1 := congrArg Game.resources eq
  have field := fields_bound a v t ht
  have en := enumerate_work d field kd md (by rw [b]; omega)
  have len : xs.length ≤ N := by
    rw [show xs.length = _ from elements_length d]
    dsimp [N,listBound]
    gcongr
  have fit (q) (mem : q ∈ xs) : Fits W q := by
    have hm := List.mem_toFinset.mpr mem
    change q ∈ (elements d).toFinset at hm
    rw [elements_set,eq] at hm
    exact Binary.datum_parts a v hm
  have u := unique_work N W xs len fit
  have sp := unique_spec xs
  have ul : us.length ≤ N := sp.2.2.trans len
  have work := factors_work us ul (by dsimp [W]; omega : 1 ≤ W) (fun q h => by
    apply fit
    have hm := List.mem_toFinset.mpr h
    change q ∈ (unique xs).value.toFinset at hm
    rwa [sp.1,List.mem_toFinset] at hm)
  have a₁ := u.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ len) 1)
  have a₂ := work.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 ul) 1)
  simp only [collect,Run.Bound,Run.bind_width,Run.bind_slots,enumerate_value,scaleSlots,scaleWidth] at *
  dsimp only [S,N,W,d,xs,us] at *
  omega

end Kintali.InputOutput.DatumWork
