module

public import Kintali.InputOutput.DirectWorkTables
public import Kintali.TrialWork.Arithmetic

/-! # Materializing the normalized game consumed by interior preparation

The stored vectors contain priors, defense gains, and the pair of attack
intercept and slope at each cell. Input lengths, list lookups, normalization,
vector reservations and indexed writes are included.
-/

@[expose] public section
namespace Kintali.InputOutput.NormalizedWork

open Binary DirectWork ContactSize TrialWork LinearProgramming.ArithmeticRun
open StochasticGames.CompilerRun StochasticGames.BinarySize

def countedTab {α β : Type} (source : List α) (f : Fin source.length → Run β) :
    Run (Vector β source.length) :=
  let n := StochasticGames.CompilerRun.length source
  let e := length_value source
  let tab := tabulate n.value (fun j => f (Fin.cast e j))
  ⟨e ▸ tab.value,n.work.seq tab.work⟩

@[simp] theorem countedTab_value {α β : Type} (source : List α) (f : Fin source.length → Run β) :
    (countedTab source f).value = Vector.ofFn (fun j => (f j).value) := by
  have aux (m n : ℕ) (e : n = m) (f : Fin m → Run β) :
      (e ▸ (tabulate n (fun j => f (Fin.cast e j))).value) = Vector.ofFn (fun j => (f j).value) := by
    subst n; simp
  exact aux _ _ (length_value source) f

theorem countedTab_get {α β : Type} (source : List α) (f : Fin source.length → Run β) (i : Fin source.length) :
    (countedTab source f).value[i.val] = (f i).value := by rw [countedTab_value]; simp

theorem countedTab_work {α β : Type} (source : List α) (f : Fin source.length → Run β)
    {S W K : ℕ} (dim : source.length ≤ S) (ws : S ≤ W) (hf : ∀ j, (f j).Bound K W) :
    (countedTab source f).Bound (4*(S+1)+S*K) W := by
  let n := StochasticGames.CompilerRun.length source
  have size := (size_le_self _).trans (dim.trans ws)
  have each := tabulate_bound (fun j => f (Fin.cast (length_value source) j)) (w := W)
    (by rw [length_value source]; exact size) (fun j => hf _)
  have len := length_bound source
  have prod := Nat.mul_le_mul_right K dim
  rw [← length_value source] at prod
  simp only [countedTab,Run.Bound,Work.seq] at *
  have exactLength := length_value source
  omega

def neg (q : ℚ) : Run ℚ :=
  let n := step (q.num.natAbs.size+1) (-q.num)
  let out : ℚ := ⟨n.value,q.den,q.den_ne_zero,by simpa [n] using q.reduced⟩
  ⟨out,n.work.seq (Work.one 0)⟩

@[simp] theorem neg_value (q : ℚ) : (neg q).value = -q := Rat.ext (by simp [neg]) (by simp [neg])

theorem neg_work {S : ℕ} {q : ℚ} (h : Fits S q) : (neg q).Bound 2 (scalarWidth S) := by
  have := h.1
  simp [neg,Run.Bound,Work.one,Work.seq,scalarWidth]
  omega

theorem neg_fits {S : ℕ} {q : ℚ} (h : Fits S q) : Fits S (-q) := by simpa [Fits] using h

def gain (a : Input) (j : Fin a.targets) : Run ℚ := do
  let p ← get a.2.1 j
  let n ← neg p.1
  plus p.2 n

@[simp] theorem gain_value (a : Input) (j : Fin a.targets) : (gain a j).value = a.game.gain j := by
  simp only [gain,Run.bind_value,plus_value,neg_value,Input.game,Input.defense,sub_eq_add_neg]
  rw [get_value a.2.1 j]

def fieldSlots (S : ℕ) := 2*S+scalarSlots S+8

theorem gain_work (a : Input) (j : Fin a.targets) : (gain a j).Bound (fieldSlots (lengthInput a)) (scalarWidth (lengthInput a)) := by
  let p := a.2.1.get j
  have h := defense_widths a j
  have left : Fits (lengthInput a) p.1 := ⟨(parts _).1.trans h.1,(parts _).2.trans h.1⟩
  have right : Fits (lengthInput a) p.2 := ⟨(parts _).1.trans h.2,(parts _).2.trans h.2⟩
  have g := get_bound a.2.1 j
  have small := j.isLt.le.trans (dimensions a).1
  have idx := (size_le_self j.val).trans small
  have n := neg_work left
  have sum := plus_work right (neg_fits left)
  simp only [gain,Run.Bound,Run.bind_slots,Run.bind_width,neg_value,fieldSlots,scalarWidth] at *
  rw [get_value a.2.1 j]
  dsimp only [p] at *
  omega

def bid (a : Input) (i : Fin a.types) (j : Fin a.targets) : Run (ℚ × ℚ) := do
  let p ← offer a i j
  let intercept ← neg p.1
  let n ← neg p.2
  let slope ← plus p.1 n
  step 0 (intercept,slope)

@[simp] theorem bid_value (a : Input) (i : Fin a.types) (j : Fin a.targets) :
    (bid a i j).value = (a.game.intercept i j,a.game.slope i j) := by
  simp [bid,Input.game,sub_eq_add_neg]

theorem bid_work (a : Input) (v : a.Valid) (i : Fin a.types) (j : Fin a.targets) :
    (bid a i j).Bound (fieldSlots (lengthInput a)) (scalarWidth (lengthInput a)) := by
  have o := offer_work a i j
  have f := offer_fits a v i j
  have n := neg_work f.1
  have n' := neg_work f.2
  have sum := plus_work f.1 (neg_fits f.2)
  simp only [bid,Run.Bound,Run.bind_slots,Run.bind_width,offer_value,neg_value,
    step_slots,step_width,fieldSlots,scalarWidth,width] at *
  omega

structure Tables (k m : ℕ) where
  resources : ℕ
  priors : Vector ℚ k
  gains : Vector ℚ m
  bids : Vector (Vector (ℚ × ℚ) m) k

def Tables.game {k m : ℕ} (t : Tables k m) : Game (Fin k) (Fin m) where
  resources := t.resources
  prior i := t.priors[i.val]
  gain j := t.gains[j.val]
  intercept i j := t.bids[i.val][j.val].1
  slope i j := t.bids[i.val][j.val].2

def prior (a : Input) (i : Fin a.types) : Run ℚ := do
  let t ← get a.2.2 i
  step 0 t.1

theorem prior_value (a : Input) (i : Fin a.types) : (prior a i).value = a.game.prior i := by
  simp only [prior,Run.bind_value,step_value,Input.game,Input.prior]
  rw [get_value a.2.2 i]

theorem prior_work (a : Input) (i : Fin a.types) : (prior a i).Bound (fieldSlots (lengthInput a)) (scalarWidth (lengthInput a)) := by
  have g := get_bound a.2.2 i
  have small := i.isLt.le.trans (dimensions a).2.1
  have idx := (size_le_self i.val).trans small
  simp only [prior,Run.Bound,Run.bind_slots,Run.bind_width,step_width,step_slots,fieldSlots,scalarWidth] at *
  omega

def run (a : Input) : Run (Tables a.types a.targets) := do
  let p ← countedTab a.2.2 (prior a)
  let g ← countedTab a.2.1 (gain a)
  let b ← countedTab a.2.2 fun i => countedTab a.2.1 (bid a i)
  step 0 ⟨a.1,p,g,b⟩

theorem run_value (a : Input) : (run a).value.game = a.game := by
  have cells (i : Fin a.types) (j : Fin a.targets) :
      (countedTab a.2.2 (fun i => countedTab a.2.1 (bid a i))).value[i.val][j.val] =
        (a.game.intercept i j,a.game.slope i j) := by
    rw [countedTab_get a.2.2 _ i]
    exact (countedTab_get a.2.1 (bid a i) j).trans (bid_value a i j)
  simp only [run,Run.bind_value,step_value,Tables.game]
  congr 1
  · funext i; exact (countedTab_get a.2.2 _ i).trans (prior_value a i)
  · funext i j; exact congrArg Prod.fst (cells i j)
  · funext i j; exact congrArg Prod.snd (cells i j)
  · funext j; exact (countedTab_get a.2.1 _ j).trans (gain_value a j)

def tabSlots (S K : ℕ) := 4*(S+1)+S*K
def tableSlots (S : ℕ) := 2*tabSlots S (fieldSlots S)+tabSlots S (tabSlots S (fieldSlots S))+1

theorem run_work (a : Input) (v : a.Valid) : (run a).Bound (tableSlots (lengthInput a)) (scalarWidth (lengthInput a)) := by
  let S := lengthInput a
  have hw : S ≤ scalarWidth S := by unfold scalarWidth; omega
  have md := (dimensions a).1
  have kd := (dimensions a).2.1
  have ps := countedTab_work a.2.2 (prior a) kd hw (prior_work a)
  have gs := countedTab_work a.2.1 (gain a) md hw (gain_work a)
  have bs := countedTab_work a.2.2 (fun i => countedTab a.2.1 (bid a i)) kd hw
    (fun i => countedTab_work a.2.1 (bid a i) md hw (bid_work a v i))
  simp only [run,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,tableSlots,tabSlots] at *
  dsimp only [S] at *
  omega

theorem run_binary_work (a : Input) (v : a.Valid) :
    LinearProgramming.RecoveryRun.binaryWork (lengthInput a) (run a).work ≤
      CodecWork.binaryLimit (lengthInput a) (tableSlots (lengthInput a)) (scalarWidth (lengthInput a)) :=
  CodecWork.addressed_bound _ (run_work a v)

end Kintali.InputOutput.NormalizedWork
