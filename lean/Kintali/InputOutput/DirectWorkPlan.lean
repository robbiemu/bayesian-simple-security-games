module

public import Kintali.InputOutput.DirectWorkTables

/-! # Recognizing the direct case and constructing the stable defense order -/

@[expose] public section
namespace Kintali.InputOutput.DirectWork

open Binary StochasticGames.CompilerRun StochasticGames.BinarySize

def targetIDs (a : Input) : Run (List (Fin a.targets)) := indices a.2.1

@[simp] theorem targetIDs_value (a : Input) : (targetIDs a).value = List.finRange a.targets :=
  indices_value a.2.1

/-- A single pass preserves target order within both groups. -/
def partition (a : Input) : List (Fin a.targets) → Run (List (Fin a.targets) × List (Fin a.targets))
  | [] => step 0 ([],[])
  | j::js => do
    let yes ← gainPositive a j
    let tails ← partition a js
    step 0 (if yes then (j::tails.1,tails.2) else (tails.1,j::tails.2))

theorem partition_value (a : Input) (js : List (Fin a.targets)) :
    (partition a js).value = (js.filter (fun j => decide (0 < a.game.gain j)),
      js.filter (fun j => !(decide (0 < a.game.gain j)))) := by
  induction js with
  | nil => rfl
  | cons j js ih => by_cases h : 0 < a.game.gain j <;> simp [partition,ih,h]

theorem partition_work (a : Input) (js : List (Fin a.targets)) :
    (partition a js).Bound (js.length*(lengthInput a+5)+1) (width (lengthInput a)) := by
  induction js with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons j js ih =>
    have g := gainPositive_work a j
    simp only [partition,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,
      List.length_cons,Nat.succ_mul] at *
    omega

def take {α : Type} : ℕ → List α → Run (List α)
  | 0, _ => step 0 []
  | _+1, [] => step 0 []
  | n+1, x::xs => do
    let k ← step (n+1).size n
    let t ← take k xs
    step 0 (x::t)

@[simp] theorem take_value {α : Type} (n : ℕ) (xs : List α) :
    (take n xs).value = xs.take n := by
  induction n generalizing xs with
  | zero => simp [take]
  | succ k ih => cases xs <;> simp [take,ih]

theorem take_work {α : Type} (n : ℕ) (xs : List α) : (take n xs).Bound (2*n+1) n.size := by
  induction n generalizing xs with
  | zero => simpa [take] using bound_step 0 ([] : List α)
  | succ n ih =>
    cases xs with
    | nil => exact (bound_step _ _).weaken (by omega) (Nat.zero_le _)
    | cons x xs =>
      have h := ih xs
      have mono := Nat.size_le_size (Nat.le_succ n)
      simp [take,Run.Bound] at *
      omega

def chosen (a : Input) := a.game.defenseOrder.take a.1

theorem chosen_mem (a : Input) (j : Fin a.targets) : j ∈ chosen a ↔ j ∈ a.game.earlyDefense := by
  simp [chosen,Game.earlyDefense,Input.game]

theorem chosen_length (a : Input) (valid : a.Valid) : (chosen a).length ≤ lengthInput a := by
  exact ((List.length_take_le ..).trans valid.2.1).trans (dimensions a).1

def plan (a : Input) : Run (Bool × List (Fin a.targets)) := do
  let js ← targetIDs a
  let groups ← partition a js
  let m ← StochasticGames.CompilerRun.length js
  let p ← StochasticGames.CompilerRun.length groups.1
  let zero ← step a.1.size (a.1 == 0)
  let full ← step (max a.1.size m.size) (a.1 == m)
  let enough ← step (max p.size a.1.size) (decide (p ≤ a.1))
  let order ← StochasticGames.CompilerRun.append groups.1 groups.2
  let selected ← take a.1 order
  step 0 (zero || full || enough,selected)

theorem plan_value (a : Input) : (plan a).value = (decide a.game.DirectCase,chosen a) := by
  simp only [plan,Run.bind_value,targetIDs_value,length_value,step_value,
    List.length_finRange,append_value,take_value]
  rw [partition_value a (List.finRange a.targets)]
  apply Prod.ext
  · apply Bool.eq_iff_iff.mpr
    simp [Game.DirectCase,Game.positiveTargets,Input.game,Input.targets,or_assoc]
  · rfl

def planSlots (S : ℕ) := S*(S+5)+12*S+16

theorem plan_work (a : Input) (valid : a.Valid) : (plan a).Bound (planSlots (lengthInput a)) (width (lengthInput a)) := by
  let js := List.finRange a.targets
  let pos := js.filter (fun j => decide (0 < a.game.gain j))
  let neg := js.filter (fun j => !(decide (0 < a.game.gain j)))
  let S := lengthInput a
  have mfit : a.targets ≤ S := (dimensions a).1
  have rfit : a.1 ≤ S := valid.2.1.trans mfit
  have rsize := (size_le_self a.1).trans rfit
  have jlen : js.length = a.targets := List.length_finRange
  have plen : pos.length ≤ S := (List.length_filter_le ..).trans (jlen.symm ▸ mfit)
  have msize := (size_le_self a.targets).trans mfit
  have psize := (size_le_self pos.length).trans plen
  have kinds := indices_work a.2.1 mfit
  change (targetIDs a).Bound (3*S+2) (width S) at kinds
  have part := (partition_work a js).weaken (Nat.add_le_add_right (Nat.mul_le_mul_right _ (jlen.symm ▸ mfit)) 1) le_rfl
  have ml := length_bound js
  have pl := length_bound pos
  have join := append_bound pos neg (width S)
  have tk := take_work a.1 (pos ++ neg)
  have pv : (partition a js).value = (pos,neg) := partition_value a js
  simp only [plan,Run.Bound,Run.bind_slots,Run.bind_width,targetIDs_value,
    length_value,step_width,step_slots,step_value,append_value] at *
  rw [pv]
  change _ ≤ planSlots S ∧ _ ≤ width S
  change (targetIDs a).work.slots + ((partition a js).work.slots +
    ((StochasticGames.CompilerRun.length js).work.slots + ((StochasticGames.CompilerRun.length pos).work.slots +
    (1+(1+(1+((StochasticGames.CompilerRun.append pos neg).work.slots+
    ((take a.1 (pos++neg)).work.slots+1)))))))) ≤ _ ∧ _
  unfold planSlots width at *
  simp only [show List.finRange a.targets = js from rfl] at *
  have jsize := (size_le_self js.length).trans (jlen.symm ▸ mfit)
  dsimp only [S] at *
  omega

end Kintali.InputOutput.DirectWork
