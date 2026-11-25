module

public import Kintali.InputOutput.LotterySize
public import Kintali.InputOutput.NormalizedWork
public import Kintali.LinearProgramming.RecoveryCost

/-! # Word work of systematic sampling for the sparse defender lottery
The addressed implementation uses reduced rational arithmetic and stable
insertion sort. A defense is stored as a target-order list of membership bits.
-/

@[expose] public section
namespace Kintali.InputOutput.LotteryWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize TrialWork NormalizedWork

variable {m : ℕ}

def input (x : Vector ℚ m) (j : Fin m) := x[j.val]

def pref (x : Vector ℚ m) : (k : ℕ) → k ≤ m → Run ℚ
  | 0, _ => step 0 0
  | k+1, h => do
    let j ← step (k+1).size (⟨k,by omega⟩ : Fin m)
    let q ← step m.size x[j.val]
    let p ← pref x k (by omega)
    plus p q

@[simp] theorem pref_value (x : Vector ℚ m) (k : ℕ) (h : k ≤ m) :
    (pref x k h).value = Fin.partialSum (input x) ⟨k,by omega⟩ := by
  induction k with
  | zero => simp [pref]
  | succ k ih =>
    let j : Fin m := ⟨k,by omega⟩
    change _ = Fin.partialSum (input x) j.succ
    rw [Fin.partialSum_succ]
    simp [pref,ih,input,j]

theorem pref_fits (x : Vector ℚ m) {S : ℕ} (hx : ∀ j, Fits S (input x j))
    (k : ℕ) (h : k ≤ m) : Fits (1+k*(S+1)) (pref x k h).value := by
  induction k with
  | zero => simpa [pref] using Fits.zero
  | succ k ih =>
    let j : Fin m := ⟨k,by omega⟩
    have a := (ih (by omega)).add (hx j)
    simp only [pref,Run.bind_value,step_value,plus_value]
    exact a.mono (by rw [Nat.succ_mul]; omega)

def base (m S : ℕ) := 1+m*(S+1)+S+m

theorem pref_work (x : Vector ℚ m) {S : ℕ} (hx : ∀ j, Fits S (input x j))
    (k : ℕ) (h : k ≤ m) : (pref x k h).Bound
      (1+k*(2+scalarSlots (base m S))) (scalarWidth (base m S)) := by
  induction k with
  | zero => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | succ k ih =>
    let j : Fin m := ⟨k,by omega⟩
    have hp := pref_fits x hx k (by omega)
    have mk := Nat.mul_le_mul_right (S+1) (by omega : k ≤ m)
    have a := plus_work (hp.mono (by unfold base; omega : 1+k*(S+1) ≤ base m S))
      ((hx j).mono (by unfold base; omega))
    have t := ih (by omega)
    have dim := size_le_self m
    have idx := size_le_self (k+1)
    simp only [pref,Run.Bound,Run.bind_slots,Run.bind_width,step_value,step_slots,step_width,
      Nat.succ_mul] at t a ⊢
    dsimp only [j,input] at a
    unfold base scalarWidth at *
    omega

/-- Compute the fractional part by a binary remainder and gcd reduction. -/
def frac (q : ℚ) : Run ℚ := do
  let rem ← step (max q.num.natAbs.size q.den.size+1) (q.num % (q.den : ℤ))
  CodecWork.reduce rem q.den

@[simp] theorem frac_value (q : ℚ) : (frac q).value = Int.fract q := by
  simp only [frac,Run.bind_value,step_value,CodecWork.reduce_value]
  rw [Int.mod_nat_eq_sub_mul_floor_rat_div, Rat.num_div_den]
  unfold Int.fract
  push_cast
  field_simp [Rat.den_ne_zero]
  rw [← Rat.mul_den_eq_num q]
  ring

theorem frac_work {q : ℚ} {w : ℕ} (h : Fits w q) :
    (frac q).Bound (5*w+8) (w+2) := by
  have pos : 0 < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have rem : (q.num % (q.den : ℤ)).natAbs ≤ q.den := by
    have a := Int.emod_nonneg q.num pos.ne'
    have b := Int.emod_lt_of_pos q.num pos
    omega
  have r := CodecWork.reduce_work _ _ ((Nat.size_le_size rem).trans h.2) h.2
  obtain ⟨a,b⟩ := h
  simp only [frac,Run.Bound,Run.bind_width,Run.bind_slots,step_slots,step_width,step_value] at *
  omega

theorem frac_fits {q : ℚ} {w : ℕ} (h : Fits w q) : Fits (w+1) (Int.fract q) := by
  have d := (Rat.sub_den_dvd_lcm q (⌊q⌋ : ℤ)).trans (show (Nat.lcm q.den (⌊q⌋ : ℚ).den) ∣ q.den by simp)
  have pos := Int.fract_nonneg q
  have small := Int.fract_lt_one q
  have a := Fits.of_den_of_abs (q := Int.fract q) (Nat.le_of_dvd q.den_pos d)
    (N := 1) (by simpa [abs_of_nonneg pos] using small.le)
  exact a.mono (by simp; exact h.2)

def insertCut (a : ℚ) : List ℚ → Run (List ℚ)
  | [] => step 0 [a]
  | b::bs => do
    let cmp ← le a b
    if cmp then step 0 (a::b::bs) else do
      let tail ← insertCut a bs
      step 0 (b::tail)

@[simp] theorem insertCut_value (a : ℚ) (xs : List ℚ) :
    (insertCut a xs).value = xs.orderedInsert (· ≤ ·) a := by
  induction xs with
  | nil => simp [insertCut]
  | cons b xs ih => by_cases h : a ≤ b <;> simp [insertCut,h,ih]

theorem insertCut_work {a : ℚ} {w : ℕ} (ha : Fits w a) (xs : List ℚ)
    (h : ∀ q ∈ xs, Fits w q) : (insertCut a xs).Bound (4*xs.length+1) (scalarWidth w) := by
  induction xs with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons b bs ih =>
    have cmp := le_work ha (h b (by simp))
    have tail := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    by_cases e : a ≤ b <;> simp [insertCut, Run.Bound,e] at * <;> omega

def sortCuts : List ℚ → Run (List ℚ)
  | [] => step 0 []
  | a::as => do
    let tail ← sortCuts as
    insertCut a tail

@[simp] theorem sortCuts_value (xs : List ℚ) : (sortCuts xs).value = xs.mergeSort := by
  rw [List.mergeSort_eq_insertionSort (· ≤ ·)]
  induction xs with
  | nil => simp [sortCuts]
  | cons a as ih => simp [sortCuts,ih]

theorem sortCuts_work (xs : List ℚ) {w : ℕ} (h : ∀ q ∈ xs, Fits w q) :
    (sortCuts xs).Bound (4*xs.length^2+1) (scalarWidth w) := by
  induction xs with
  | nil => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | cons a as ih =>
    have ht (q : ℚ) (mem : q ∈ as) := h q (List.mem_cons_of_mem _ mem)
    have ins := insertCut_work (h a (by simp)) as.mergeSort (fun q hq => ht q (List.mem_mergeSort.mp hq))
    have sub := ih ht
    simp only [sortCuts,Run.Bound,Run.bind_slots,Run.bind_width,sortCuts_value,List.length_cons,List.length_mergeSort] at *
    constructor
    · nlinarith [ins.1,sub.1]
    · exact max_le sub.2 ins.2


def diff (a b : ℚ) : Run ℚ := neg b >>= plus a

@[simp] theorem diff_value (a b : ℚ) : (diff a b).value = a-b := by simp [diff,sub_eq_add_neg]

theorem diff_work {w : ℕ} {a b : ℚ} (ha : Fits w a) (hb : Fits w b) :
    (diff a b).Bound (2+scalarSlots w) (scalarWidth w) :=
  bound_bind (neg_work hb) (by rw [neg_value]; exact plus_work ha (neg_fits hb))

theorem diff_fits {w : ℕ} {a b : ℚ} (ha : Fits w a) (hb : Fits w b) :
    Fits (2*w+1) (a-b) := by simpa [two_mul,sub_eq_add_neg] using ha.add (neg_fits hb)

def interval (a b : ℚ) : Run Lottery.Sample := do
  let s ← plus a b
  let mid ← divide s 2
  let gap ← diff b a
  step 0 (mid,gap)

@[simp] theorem interval_value (a b : ℚ) : (interval a b).value = ((a+b)/2,b-a) := by simp [interval]

private theorem two_fit : Fits 2 2 := by unfold Fits; decide

theorem interval_work {w : ℕ} {a b : ℚ} (ha : Fits w a) (hb : Fits w b) :
    (interval a b).Bound (3*scalarSlots (2*w+2)+7) (scalarWidth (2*w+2)) := by
  let u := 2*w+2
  have ab : Fits u (a+b) := (ha.add hb).mono (by dsimp [u]; omega)
  have two : Fits u 2 := two_fit.mono (by dsimp [u]; omega)
  have big : w ≤ u := by dsimp [u]; omega
  have z := divide_work ab two
  have p := plus_work (ha.mono big) (hb.mono big)
  have d := diff_work (hb.mono big) (ha.mono big)
  simp only [interval,Run.Bound,Run.bind_slots,Run.bind_width,plus_value,step_width,step_slots] at *
  dsimp only [u] at *
  omega

def intervals (a : ℚ) : List ℚ → Run (List Lottery.Sample)
  | [] => do
    let p ← interval a 1
    step 0 [p]
  | b::bs => do
    let p ← interval a b
    let rest ← intervals b bs
    step 0 (p::rest)

@[simp] theorem intervals_value (a : ℚ) (xs : List ℚ) :
    (intervals a xs).value = Lottery.samples a xs := by
  induction xs generalizing a with
  | nil => simp [intervals,Lottery.samples]
  | cons _ _ ih => simp [intervals,Lottery.samples,ih]

theorem intervals_work {w : ℕ} {a : ℚ} (xs : List ℚ) (ha : Fits w a) (h : ∀ q ∈ xs, Fits w q) :
    (intervals a xs).Bound ((xs.length+1)*(3*scalarSlots (2*w+2)+8)) (scalarWidth (2*w+2)) := by
  induction xs generalizing a with
  | nil =>
    have cell := interval_work ha (Fits.one.mono ha.pos)
    simp only [intervals,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,List.length_nil,
      Nat.zero_add,one_mul] at *
    omega
  | cons b bs ih =>
    have hb := h b (by simp)
    have cell := interval_work ha hb
    have sub := ih hb (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [intervals,Run.Bound,Run.bind_slots,Run.bind_width,step_slots,step_width,List.length_cons,
      Nat.succ_mul] at *
    omega

/-- Rounding the difference in prefix counts needs only a comparison of signed ceilings. -/
def ceiling (q : ℚ) : Run ℤ := do
  let n ← step (q.num.natAbs.size+1) (-q.num)
  let quot ← step (max n.natAbs.size q.den.size+1) (n / (q.den : ℤ))
  step (quot.natAbs.size+1) (-quot)

@[simp] theorem ceiling_value (q : ℚ) : (ceiling q).value = ⌈q⌉ := by simp [ceiling,Rat.ceil_def']

theorem ceiling_work {w : ℕ} {q : ℚ} (h : Fits w q) :
    (ceiling q).Bound 3 (w+1) ∧ (⌈q⌉ : ℤ).natAbs.size ≤ w := by
  have t := Nat.size_le_size (Int.natAbs_ediv_le_natAbs (-q.num) (q.den : ℤ))
  obtain ⟨hn,hd⟩ := h
  simp [ceiling,Run.Bound,Rat.ceil_def'] at *
  omega

def before (s u : ℚ) : Run ℤ := diff s u >>= ceiling

@[simp] theorem before_value (s u : ℚ) : (before s u).value = Lottery.count s u := by simp [before,Lottery.count]

theorem before_work {s u : ℚ} {w : ℕ} (a : Fits w s) (b : Fits w u) :
    (before s u).Bound (5+scalarSlots w) (scalarWidth w) ∧
    (Lottery.count s u).natAbs.size ≤ 2*w+1 := by
  have d := diff_work a b
  have c := ceiling_work (diff_fits a b)
  simp only [before,Run.Bound,Run.bind_slots,Run.bind_width,diff_value,Lottery.count,scalarWidth] at *
  omega

def bit (x : Vector ℚ m) (u : ℚ) (j : Fin m) : Run Bool := do
  let left ← pref x j.val j.isLt.le
  let k ← step m.size (⟨j.val+1,by omega⟩ : Fin (m+1))
  let right ← pref x k.val (by omega)
  let l ← before left u
  let r ← before right u
  step (max l.natAbs.size r.natAbs.size+1) (decide (l < r))

@[simp] theorem bit_value (x : Vector ℚ m) (u : ℚ) (j : Fin m) :
    (bit x u j).value = decide (j ∈ Lottery.allocation (input x) u) := by
  simp only [bit,Run.bind_value,step_value,pref_value,before_value,Lottery.allocation,
    Finset.mem_filter,Finset.mem_univ,true_and,Lottery.increment,sub_pos]
  rfl

def bitSlots (m S w : ℕ) := 2*(1+m*(2+scalarSlots (base m S)))+2*(5+scalarSlots w)+2

theorem bit_work (x : Vector ℚ m) {S w : ℕ} (hx : ∀ j, Fits S (input x j)) (big : base m S ≤ w)
    {u : ℚ} (hu : Fits w u) (j : Fin m) :
    (bit x u j).Bound (bitSlots m S w) (scalarWidth w) := by
  have p (k : ℕ) (h : k ≤ m) :
      (pref x k h).Bound (1+m*(2+scalarSlots (base m S))) (scalarWidth w) :=
    (pref_work x hx k h).weaken (by gcongr) (by unfold scalarWidth; omega)
  have b (k : ℕ) (h : k ≤ m) :=
    before_work ((pref_fits x hx k h).mono (show 1+k*(S+1) ≤ w by
      have := Nat.mul_le_mul_right (S+1) h; unfold base at big; omega)) hu
  have p₁ := p j.val j.isLt.le
  have p₂ := p (j.val+1) j.isLt
  have b₁ := b j.val j.isLt.le
  have b₂ := b (j.val+1) j.isLt
  have dim := size_le_self m
  simp only [bit,Run.Bound,Run.bind_slots,Run.bind_width,step_value,before_value,
    step_width,step_slots,bitSlots,scalarWidth] at *
  unfold base at big
  omega


def breakpoint {n : ℕ} (x : Vector ℚ (n+1)) (j : Fin n) : Run ℚ := do
  let k ← step (n+1).size (j.succ.castSucc : Fin ((n+1)+1))
  let p ← pref x k.val (by omega)
  frac p

@[simp] theorem breakpoint_value {n : ℕ} (x : Vector ℚ (n+1)) (j : Fin n) :
    (breakpoint x j).value = Int.fract (Fin.partialSum (input x) j.succ.castSucc) := by
  simp only [breakpoint,Run.bind_value,step_value,pref_value,frac_value]

def cutSlots (m S : ℕ) := 2+m*(2+scalarSlots (base m S))+(5*base m S+8)

theorem breakpoint_work {n S : ℕ} (x : Vector ℚ (n+1)) (hx : ∀ j, Fits S (input x j)) (j : Fin n) :
    (breakpoint x j).Bound (cutSlots (n+1) S) (scalarWidth (base (n+1) S)) ∧
    Fits (base (n+1) S+1) (breakpoint x j).value := by
  have h : j.val+1 ≤ n+1 := by have := j.isLt; omega
  have m := Nat.mul_le_mul_right (S+1) h
  have b := (pref_fits x hx (j.val+1) h).mono (show _ ≤ base (n+1) S by unfold base; omega)
  have p := pref_work x hx (j.val+1) h
  have cnt := Nat.mul_le_mul_right (2+scalarSlots (base (n+1) S)) h
  have dim := size_le_self (n+1)
  have F := frac_work b
  have val := frac_fits b
  constructor
  · simp only [breakpoint,Run.Bound,Run.bind_slots,Run.bind_width,step_value,step_width,step_slots,
      Fin.val_castSucc,Fin.val_succ,cutSlots,scalarWidth] at *
    unfold base at *
    omega
  · exact (frac_value _).symm ▸ val

def orderedCuts {n : ℕ} (x : Vector ℚ (n+1)) : Run (List ℚ) := do
  let js ← finRange n
  let qs ← StochasticGames.CompilerRun.mapM (breakpoint x) js
  sortCuts qs

@[simp] theorem orderedCuts_value {n : ℕ} (x : Vector ℚ (n+1)) :
    (orderedCuts x).value = Lottery.cuts (input x) := by simp [orderedCuts,Lottery.cuts,List.ofFn_eq_map]

def orderedSlots (n S : ℕ) := (2*n+1)+(n*(cutSlots (n+1) S+2)+1)+(4*n^2+1)

theorem orderedCuts_work {n S : ℕ} (x : Vector ℚ (n+1)) (hx : ∀ j, Fits S (input x j)) :
    (orderedCuts x).Bound (orderedSlots n S) (scalarWidth (base (n+1) S+1)) ∧
    ∀ q ∈ Lottery.cuts (input x), Fits (base (n+1) S+1) q := by
  let js := List.finRange n
  let qs := js.map fun j => (breakpoint x j).value
  have fit : ∀ q ∈ qs, Fits (base (n+1) S+1) q := by
    intro q h
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    exact (breakpoint_work x hx j).2
  have sort := sortCuts_work qs fit
  have indices := finRange_bound n
  have mp := mapM_bound (breakpoint x) js (cutSlots (n+1) S) _ (fun j _ => (breakpoint_work x hx j).1)
  have dim := size_le_self n
  constructor
  · simp only [orderedCuts,Run.Bound,Run.bind_slots,Run.bind_width,finRange_value,mapM_value,
      orderedSlots,qs,js,List.length_map,List.length_finRange,scalarWidth] at *
    unfold base at *
    omega
  · unfold Lottery.cuts
    intro q h
    obtain ⟨j,e⟩ := List.mem_ofFn.mp (List.mem_mergeSort.mp h)
    exact by simpa only [← e,← breakpoint_value] using (breakpoint_work x hx j).2

/-- Both fields of each generated sample fit, including intervals of width zero. -/
theorem sample_fits {a : ℚ} (xs : List ℚ) {w : ℕ} (ha : Fits w a) (h : ∀ q ∈ xs, Fits w q) :
    ∀ p ∈ Lottery.samples a xs, Fits (2*w+3) p.1 ∧ Fits (2*w+3) p.2 := by
  have pair {a b : ℚ} (a' : Fits w a) (b' : Fits w b) :
      Fits (2*w+3) ((a+b)/2) ∧ Fits (2*w+3) (b-a) :=
    ⟨((a'.add b').div two_fit).mono (by omega),(diff_fits b' a').mono (by omega)⟩
  induction xs generalizing a with
  | nil =>
    intro p hp
    simp only [Lottery.samples,List.mem_singleton] at hp
    subst p
    exact pair ha (Fits.one.mono ha.pos)
  | cons b bs ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | later
    · exact pair ha (h b (by simp))
    · exact ih (h b (by simp)) (fun q hq => h q (List.mem_cons_of_mem _ hq)) _ later

abbrev MaskOutcome := List Bool × ℚ

def writeSample (x : Vector ℚ m) (js : List (Fin m)) (p : Lottery.Sample) : Run (List MaskOutcome) := do
  let positive ← lt 0 p.2
  if positive then do
    let mask ← StochasticGames.CompilerRun.mapM (bit x p.1) js
    step 0 [(mask,p.2)]
  else step 0 []

def mask {m : ℕ} (p : Lottery.Outcome m) : MaskOutcome :=
  (List.ofFn (fun j => decide (j ∈ p.1)), p.2)

theorem writeSample_value (x : Vector ℚ m) (p : Lottery.Sample) :
    (writeSample x (List.finRange m) p).value =
      if 0 < p.2 then [mask (Lottery.allocation (input x) p.1,p.2)] else [] := by
  by_cases h : 0 < p.2 <;> simp [writeSample,h,mask,List.ofFn_eq_map]

def sampleSlots (m S w : ℕ) := 6+m*(bitSlots m S w+2)

theorem writeSample_work (x : Vector ℚ m) {S w : ℕ} (hx : ∀ j, Fits S (input x j)) (big : base m S ≤ w)
    (p : Lottery.Sample) (uf : Fits w p.1) (wf : Fits w p.2) :
    (writeSample x (List.finRange m) p).Bound (sampleSlots m S w) (scalarWidth w) := by
  have cmp := lt_work (Fits.zero.mono wf.pos) wf
  have mp := mapM_bound (bit x p.1) (List.finRange m) _ _ (fun j _ => bit_work x hx big uf j)
  by_cases h : 0 < p.2 <;>
    simp only [writeSample,Run.Bound,Run.bind_slots,Run.bind_width,lt_value,decide_eq_true_eq,
      h,ite_true,ite_false,step_slots,step_width,sampleSlots,List.length_finRange] at * <;> omega

def runPositive {n : ℕ} (x : Vector ℚ (n+1)) : Run (List MaskOutcome) := do
  let cuts ← orderedCuts x
  let offsets ← intervals 0 cuts
  let js ← finRange (n+1)
  StochasticGames.CompilerRun.flatMapM (writeSample x js) offsets

@[simp] theorem runPositive_value {n : ℕ} (x : Vector ℚ (n+1)) :
    (runPositive x).value = (Lottery.recover (input x)).map mask := by
  simp only [runPositive,Run.bind_value,orderedCuts_value,intervals_value,finRange_value,flatMapM_value,
    Lottery.recover,Lottery.outcomes,List.map_map,writeSample_value]
  generalize Lottery.samples 0 (Lottery.cuts (input x)) = ps
  induction ps with
  | nil => rfl
  | cons p ps ih => by_cases h : 0 < p.2 <;> simp [h,ih]


def words (n S : ℕ) := 2*(base (n+1) S+1)+3

def slots (n S : ℕ) :=
  orderedSlots n S + (n+1)*(3*scalarSlots (2*(base (n+1) S+1)+2)+8)
    + (2*(n+1)+1) + ((n+1)*(sampleSlots (n+1) S (words n S)+1+2)+1)

theorem runPositive_work {n S : ℕ} (x : Vector ℚ (n+1)) (hx : ∀ j, Fits S (input x j)) :
    (runPositive x).Bound (slots n S) (scalarWidth (words n S)) := by
  let qs := Lottery.cuts (input x)
  let ps := Lottery.samples 0 qs
  let w := base (n+1) S+1
  have zero : Fits w 0 := Fits.zero.mono (by dsimp [w]; omega)
  have oc := orderedCuts_work x hx
  have fi : ∀ q ∈ qs, Fits w q := oc.2
  have cs := oc.1
  have it := intervals_work qs zero fi
  have cnt : qs.length = n := by simp [qs,Lottery.cuts]
  have pc : ps.length = n+1 := by simp [ps,cnt]
  have sf := sample_fits qs zero fi
  have big : base (n+1) S ≤ words n S := by unfold words; omega
  have each (p : Lottery.Sample) (hp : p ∈ ps) := writeSample_work x hx big p (sf p hp).1 (sf p hp).2
  have len (p : Lottery.Sample) (_ : p ∈ ps) : (writeSample x (List.finRange (n+1)) p).value.length ≤ 1 := by
    rw [writeSample_value]
    split <;> simp
  have emit := flatMapM_bound (writeSample x (List.finRange (n+1))) ps _ 1 _ each len
  have idx := finRange_bound (n+1)
  have dim := size_le_self (n+1)
  have fit : n+1 ≤ base (n+1) S := by unfold base; omega
  simp only [runPositive,Run.Bound,Run.bind_width,Run.bind_slots,orderedCuts_value,intervals_value,
    finRange_value,slots,cnt,pc,scalarWidth,words] at cs it emit idx ⊢
  dsimp only [w,ps,qs] at *
  omega

/-- The zero-target convention agrees with the unique empty pure defense. -/
def run : {m : ℕ} → Vector ℚ m → Run (List MaskOutcome)
  | 0, _ => step 0 [([],1)]
  | _+1, x => runPositive x

theorem run_value (x : Vector ℚ m) : (run x).value = (Lottery.recover (input x)).map mask := by
  cases m with
  | zero => simp [run,Lottery.recover,mask]
  | succ n => exact runPositive_value x

def inputLength (x : Vector ℚ m) := (Binary.many Binary.rational (List.ofFn (input x))).length

theorem run_work (x : Vector ℚ m) :
    (run x).Bound (slots (inputLength x) (inputLength x)) (scalarWidth (words (inputLength x) (inputLength x))) := by
  let S := inputLength x
  have dim : m ≤ S := by simpa [S,inputLength] using Binary.count_le_many Binary.rational (List.ofFn (input x))
  have fits (j : Fin m) : Fits S (input x j) := by
    have bits : (Binary.rational (input x j)).length ≤ S :=
      Binary.entry_le_many _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    exact ⟨(Binary.parts _).1.trans bits,(Binary.parts _).2.trans bits⟩
  cases m with
  | zero =>
    apply (bound_step _ _).weaken _ (Nat.zero_le _)
    unfold slots
    omega
  | succ n =>
    have ns : n ≤ S := by omega
    apply (runPositive_work x fits).weaken
    · unfold slots orderedSlots words sampleSlots bitSlots cutSlots base scalarSlots
      gcongr
    · unfold scalarWidth words base
      gcongr

def binaryLimit (S : ℕ) :=
  slots S S * (64 * (S + slots S S + 3*scalarWidth (words S S) + 16)^3)

/-- In the project's addressed binary-word model, constructing the weighted
membership lists costs polynomial work in the encoded coverage-vector length. -/
theorem run_binary_work (x : Vector ℚ m) :
    LinearProgramming.RecoveryRun.binaryWork (inputLength x) (run x).work ≤ binaryLimit (inputLength x) := by
  let S := inputLength x
  let W := (run x).work
  have b := run_work x
  have count : W.slots ≤ slots S S := b.1
  have operands : W.width ≤ scalarWidth (words S S) := b.2
  have i := size_le_self (S+1)
  have s := size_le_self (W.slots+1)
  have w := size_le_self (W.width+1)
  have width : max W.width (addressWidth S W.slots W.width)+1 ≤ S+slots S S+3*scalarWidth (words S S)+16 := by
    unfold addressWidth
    omega
  exact Nat.mul_le_mul count (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left width 3))


/-- Every stored probability satisfies the sharper common-denominator output
width from the correctness construction, irrespective of arithmetic scratch. -/
theorem output_width {n : ℕ} (x : Vector ℚ (n+1)) (o : MaskOutcome) (h : o ∈ (run x).value) :
    o.1.length = n+1 ∧ Fits (1+inputLength x) o.2 := by
  rw [run_value] at h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h
  exact ⟨by simp [mask],Lottery.probability_parts (input x) p hp⟩

end Kintali.InputOutput.LotteryWork
