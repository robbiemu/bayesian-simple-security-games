module

public import Kintali.InputOutput.NormalizedWork
public import Kintali.TrialWork.Scan
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Total charged validity test on public rational tables

Every stored attack row is traversed in its actual length. The checks and
width bounds therefore also cover short or overlong rows, negative priors,
and violated payoff inequalities. No game validity hypothesis is required.
-/

open scoped BigOperators

@[expose] public section
namespace Kintali.InputOutput.ValidityWork

open Binary TrialWork ContactSize StochasticGames.CompilerRun StochasticGames.BinarySize

def every {α : Type} (test : α → Run Bool) : List α → Run Bool
  | [] => step 0 true
  | x::xs => do
    let v ← test x
    if ← step 0 v then every test xs else pure false

@[simp] theorem every_value {α : Type} (test : α → Run Bool) (xs : List α) :
    (every test xs).value = xs.all (fun x => (test x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (test x).value <;> simp [every,h,ih]

theorem every_work {α : Type} (test : α → Run Bool) (xs : List α) {k w : ℕ}
    (ok : ∀ x ∈ xs, (test x).Bound k w) : (every test xs).Bound (1+xs.length*(k+1)) w := by
  induction xs with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons x xs ih =>
    have a := ok x (by simp)
    have b := ih (fun y m => ok y (List.mem_cons_of_mem _ m))
    cases h : (test x).value <;>
      simp only [every,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,step_value,
        h,ite_true,Bool.false_eq_true,ite_false,List.length_cons,Nat.succ_mul] at *
    · change _ + (1+0) ≤ _ ∧ max _ (max 0 0) ≤ _
      omega
    · omega

def testRow (m : ℕ) (r : ℚ × List Payoffs) : Run Bool := do
  let n ← StochasticGames.CompilerRun.length r.2
  let shape ← step (max n.size m.size) (n == m)
  let p ← le 0 r.1
  let cols ← every (fun v : Payoffs => le v.2 v.1) r.2
  let ok ← step 0 (shape && p)
  step 0 (ok && cols)

theorem testRow_true (m : ℕ) (r : ℚ × List Payoffs) : (testRow m r).value = true ↔
    0 ≤ r.1 ∧ r.2.length = m ∧ ∀ v ∈ r.2, v.2 ≤ v.1 := by
  simp [testRow,and_assoc,and_left_comm]

def sumPriors (a : Input) : Run ℚ := do
  let is ← DirectWork.indices a.2.2
  qsum (NormalizedWork.prior a) is

theorem sumPriors_value (a : Input) : (sumPriors a).value = ∑ i, a.prior i := by
  rw [sumPriors,Run.bind_value,DirectWork.indices_value]
  change (qsum (NormalizedWork.prior a) (List.finRange a.types)).value = _
  rw [qsum_value]
  exact (list_sum_univ _ _ (List.nodup_finRange a.types) List.mem_finRange).trans
    (Finset.sum_congr rfl (fun i _ => NormalizedWork.prior_value a i))

def run (a : Input) : Run Bool := do
  let m ← StochasticGames.CompilerRun.length a.2.1
  let positive ← step m.size (decide (0 < m))
  let budget ← step (max m.size a.1.size) (decide (a.1 ≤ m))
  let defenses ← every (fun p : Payoffs => le p.1 p.2) a.2.1
  let rows ← every (testRow m) a.2.2
  let prior ← sumPriors a
  let one ← eqRat prior 1
  let dims ← step 0 (positive && budget)
  let entry ← step 0 (defenses && rows)
  let shape ← step 0 (dims && entry)
  step 0 (shape && one)

private theorem row_iff (a : Input) (i : Fin a.types) (shape : (a.offers i).length = a.targets) :
    (∀ p ∈ a.offers i, p.2 ≤ p.1) ↔ ∀ j : Fin a.targets, (a.attack i j).2 ≤ (a.attack i j).1 := by
  rw [List.forall_mem_iff_get]
  constructor
  · intro h j
    have hj : j.val < (a.offers i).length := by rw [shape]; exact j.isLt
    simpa [Input.attack,hj] using h ⟨j.val,hj⟩
  · intro h j
    have hj : j.val < a.targets := j.isLt.trans_le shape.le
    have small := h ⟨j.val,hj⟩
    simpa [Input.attack,j.isLt] using small

theorem run_true (a : Input) : (run a).value = true ↔ a.Valid := by
  simp only [run,Run.bind_value,length_value,step_value,Bool.and_eq_true,decide_eq_true_eq,
    eqRat_value,sumPriors_value,every_value,List.all_eq_true,le_value,testRow_true]
  rw [List.forall_mem_iff_get,List.forall_mem_iff_get]
  change (((0 < a.targets ∧ a.1 ≤ a.targets) ∧
    ((∀ j, (a.defense j).1 ≤ (a.defense j).2) ∧
      ∀ i, 0 ≤ a.prior i ∧ (a.offers i).length = a.targets ∧ ∀ p ∈ a.offers i, p.2 ≤ p.1)) ∧
      (∑ i, a.prior i) = 1) ↔ a.Valid
  constructor
  · rintro ⟨⟨⟨hm,b⟩,d,rows⟩,p⟩
    exact ⟨hm,b,p,d,fun i => ⟨(rows i).1,(rows i).2.1,(row_iff a i (rows i).2.1).mp (rows i).2.2⟩⟩
  · rintro ⟨hm,b,p,d,rows⟩
    exact ⟨⟨⟨hm,b⟩,d,fun i => ⟨(rows i).1,(rows i).2.1,(row_iff a i (rows i).2.1).mpr (rows i).2.2⟩⟩,p⟩

private theorem pair_width (p : Payoffs) {S : ℕ} (h : (payoff p).length ≤ S) : Fits S p.1 ∧ Fits S p.2 := by
  have f := parts p.1
  have g := parts p.2
  simp only [payoff,length_pair] at h
  unfold Fits
  omega

private theorem row_width (a : Input) (r : ℚ × List Payoffs) (mem : r ∈ a.2.2) :
    (rational r.1).length+(many payoff r.2).length ≤ lengthInput a := by
  have entry := entry_le_many attacker mem
  simp only [attacker,lengthInput,input,length_pair] at *
  omega

def width (S : ℕ) := scalarWidth (addWidth S (S+1))+scalarWidth (S+1)+S+8
def rowSlots (S : ℕ) := 5*S+9
def slots (S : ℕ) := S+1+2+(1+4*S)+(1+S*(rowSlots S+1))+
  (3*S+2+sumSlots S (S+1) (NormalizedWork.fieldSlots S))+3+4

theorem testRow_work (a : Input) (r : ℚ × List Payoffs) (mem : r ∈ a.2.2) :
    (testRow a.targets r).Bound (rowSlots (lengthInput a)) (width (lengthInput a)) := by
  let S := lengthInput a
  have rw' := row_width a r mem
  have rl : r.2.length ≤ S := (count_le_many payoff r.2).trans (by dsimp [S]; omega)
  have rs := (size_le_self r.2.length).trans rl
  have ms := (size_le_self a.targets).trans (dimensions a).1
  have part := parts r.1
  have prior : Fits (S+1) r.1 := by unfold Fits; dsimp [S]; omega
  have sign := le_work (Fits.zero.mono (by omega : 1 ≤ S+1)) prior
  have htest (x : Payoffs) (hx : x ∈ r.2) : (le x.2 x.1).Bound 3 (scalarWidth (S+1)) := by
    have pay := entry_le_many payoff hx
    have vals := pair_width x (S := S+1) (by dsimp [S]; omega)
    exact le_work vals.2 vals.1
  have all := every_work _ r.2 htest
  have len := length_bound r.2
  simp only [testRow,Run.Bound,Run.bind_slots,Run.bind_width,length_value,step_slots,step_width,
    width,rowSlots] at *
  dsimp only [S] at *
  omega

theorem sumPriors_work (a : Input) :
    (sumPriors a).Bound (3*lengthInput a+2+sumSlots (lengthInput a) (lengthInput a+1)
      (NormalizedWork.fieldSlots (lengthInput a))) (width (lengthInput a)) ∧
    Fits (addWidth (lengthInput a) (lengthInput a+1)) (sumPriors a).value := by
  let S := lengthInput a
  let is := List.finRange a.types
  have kd : a.types ≤ S := (dimensions a).2.1
  have idx := DirectWork.indices_work a.2.2 kd
  have iw : DirectWork.width S ≤ width S := by unfold DirectWork.width width scalarWidth; omega
  have sw : scalarWidth S ≤ width S := by unfold width scalarWidth; omega
  have aw : scalarWidth (addWidth S (S+1)) ≤ width S := by unfold width; omega
  have wk (i : Fin a.types) := (NormalizedWork.prior_work a i).weaken le_rfl sw
  have sm (i : Fin a.types) : Fits (S+1) (NormalizedWork.prior a i).value := by
    rw [NormalizedWork.prior_value]
    have h := prior_width a i
    have b := parts (a.prior i)
    change Fits (S+1) (a.prior i)
    unfold Fits
    dsimp only [S]
    omega
  have len : is.length ≤ S := by simpa [is] using kd
  have q := qsum_work (NormalizedWork.prior a) is len wk sm aw
  have b := list_sum_fits (NormalizedWork.prior a) is sm
  have small : sumBits is.length (S+1) ≤ addWidth S (S+1) :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ len) 1).trans (Nat.le_add_right ..)
  constructor
  · unfold sumPriors
    apply bound_bind (idx.weaken le_rfl iw)
    rw [DirectWork.indices_value a.2.2]
    exact q
  · unfold sumPriors
    rw [Run.bind_value,DirectWork.indices_value a.2.2]
    exact b.mono small

theorem run_work (a : Input) : (run a).Bound (slots (lengthInput a)) (width (lengthInput a)) := by
  let S := lengthInput a
  have kd : a.types ≤ S := (dimensions a).2.1
  have md : a.targets ≤ S := (dimensions a).1
  have size := (size_le_self a.targets).trans md
  have res := (dimensions a).2.2
  have len := length_bound a.2.1
  have w : scalarWidth (S+1) ≤ width S := by unfold width; omega
  have c (x : Payoffs) (hx : x ∈ a.2.1) : (le x.1 x.2).Bound 3 (width S) := by
    have z := entry_le_many payoff hx
    have fit : (payoff x).length ≤ lengthInput a := by simp only [lengthInput,input,length_pair]; omega
    obtain ⟨f,g⟩ := pair_width x (fit.trans (Nat.le_succ _))
    exact (le_work f g).weaken le_rfl w
  have ds := every_work _ a.2.1 c
  have rows := every_work (testRow a.targets) a.2.2 (testRow_work a)
  have mRow := Nat.mul_le_mul_right (rowSlots S+1) kd
  obtain ⟨ps,pv⟩ := sumPriors_work a
  have eq := eqRat_work pv (Fits.one.mono (by unfold addWidth sumBits; omega))
  simp only [run,Run.Bound,Run.bind_slots,Run.bind_width,length_value,step_slots,step_width,slots] at *
  change _ ≤ _ ∧ _ ≤ width S
  change a.2.1.length ≤ S at md
  change a.2.2.length ≤ S at kd
  dsimp only [S] at *
  unfold Input.targets Input.types width at *
  omega

theorem run_binary_work (a : Input) :
    LinearProgramming.RecoveryRun.binaryWork (lengthInput a) (run a).work ≤
      CodecWork.binaryLimit (lengthInput a) (slots (lengthInput a)) (width (lengthInput a)) :=
  CodecWork.addressed_bound _ (run_work a)

theorem slots_eq (S : ℕ) : slots S = 10*S^3+47*S^2+97*S+15 := by
  unfold slots rowSlots sumSlots NormalizedWork.fieldSlots scalarSlots addWidth sumBits
  ring

theorem width_eq (S : ℕ) : width S = 2*S^2+9*S+26 := by
  unfold width scalarWidth addWidth sumBits
  ring

theorem polynomial : ∃ p : Polynomial ℕ, ∀ a : Input,
    LinearProgramming.RecoveryRun.binaryWork (lengthInput a) (run a).work ≤ p.eval (lengthInput a) := by
  let K : Polynomial ℕ := 10*Polynomial.X^3+47*Polynomial.X^2+97*Polynomial.X+15
  let W : Polynomial ℕ := 2*Polynomial.X^2+9*Polynomial.X+26
  use K*(64*(Polynomial.X+K+3*W+16)^3)
  intro a
  apply (run_binary_work a).trans_eq
  simp [K,W,CodecWork.binaryLimit,slots_eq,width_eq]

end Kintali.InputOutput.ValidityWork

/-! The public writer can also consume explicit charged coordinate readers.
This form carries each input callback's execution into the work count. -/

namespace Kintali.InputOutput.StrategyWork

open StochasticGames.CompilerRun StochasticGames.BinarySize

def withReaders {k m : ℕ} (x : Fin m → Run ℚ) (q : Fin k → Fin m → Run ℚ) : Run Output := do
  let js ← finRange m
  let is ← finRange k
  let cov ← StochasticGames.CompilerRun.mapM x js
  let rows ← StochasticGames.CompilerRun.mapM (fun i => StochasticGames.CompilerRun.mapM (q i) js) is
  step 0 (cov,rows)

theorem withReaders_value {k m : ℕ} (s : Strategy k m) (x : Fin m → Run ℚ) (q : Fin k → Fin m → Run ℚ)
    (coverage : ∀ j, (x j).value = s.coverage j) (attacks : ∀ i j, (q i j).value = s.attacks i j) :
    (withReaders x q).value = writeStrategy s := by
  simp [withReaders,writeStrategy,coverage,attacks,List.ofFn_eq_map]

def readerSlots (S c : ℕ) := 2*(2*S+1)+(S*(c+2)+1)+(S*(S*(c+2)+3)+1)+1

theorem withReaders_work {k m S c w : ℕ} (x : Fin m → Run ℚ) (q : Fin k → Fin m → Run ℚ)
    (kd : k ≤ S) (md : m ≤ S) (ki : k.size ≤ w) (mi : m.size ≤ w)
    (xc : ∀ j, (x j).Bound c w) (qc : ∀ i j, (q i j).Bound c w) :
    (withReaders x q).Bound (readerSlots S c) w := by
  have row (f : Fin m → Run ℚ) (h : ∀ j, (f j).Bound c w) :
      (StochasticGames.CompilerRun.mapM f (List.finRange m)).Bound (S*(c+2)+1) w :=
    (mapM_bound f _ c w (fun j _ => h j)).weaken
      (by rw [List.length_finRange]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ md) 1) le_rfl
  have xy := row x xc
  have rows := mapM_bound (fun i => StochasticGames.CompilerRun.mapM (q i) (List.finRange m))
    (List.finRange k) (S*(c+2)+1) w (fun i _ => row _ (qc i))
  have pr := Nat.mul_le_mul_right (S*(c+2)+3) kd
  have ix := finRange_bound k
  have jx := finRange_bound m
  simp only [withReaders,Run.Bound,Run.bind_width,Run.bind_slots,finRange_value,
    step_width,step_slots,List.length_finRange,readerSlots] at *
  change _ ≤ k*(S*(c+2)+3)+1 ∧ _ at rows
  omega

end Kintali.InputOutput.StrategyWork
