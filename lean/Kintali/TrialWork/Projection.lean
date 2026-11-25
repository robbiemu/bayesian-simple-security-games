module

public import Kintali.TrialWork.Scan
public import Kintali.ExactRecovery.SparseView

/-! Compute the projected coverage and attack tables with explicit scans of
the retained real bids and private interval groups. Each field access carries
its own work, so a stored list lookup and an array read can use different costs. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize ExactRecovery QuotaSweep
open LinearProgramming.ArithmeticRun

variable {k m G : ℕ} {A H : Type}

structure Access (k m G : ℕ) (A H : Type) where
  real : A → Run (Fin k × Fin m × Quote G)
  site : H → Run (Fin m)
  holding : Sparse.R (Fin k) (Fin m) A H → Run ℚ
  redirect : Fin k → Run (Fin m)
  active : Fin m → Run Bool

structure Reads (a : Access k m G A H) (g : Game (Fin k) (Fin m))
    (layout : Sparse.Layout (Fin k) (Fin m) G A H)
    (x : Sparse.R (Fin k) (Fin m) A H → ℚ) (toSite : Fin k → Fin m) : Prop where
  real : ∀ i, (a.real i).value = layout.real i
  site : ∀ h, (a.site h).value = (layout.representative h).1
  holding : ∀ r, (a.holding r).value = x r
  redirect : ∀ i, (a.redirect i).value = toSite i
  active : ∀ j, (a.active j).value = decide (0 < g.gain j)

structure AccessBound (a : Access k m G A H) (c w : ℕ) : Prop where
  real : ∀ i, (a.real i).Bound c w
  site : ∀ h, (a.site h).Bound c w
  holding : ∀ r, (a.holding r).Bound c w
  redirect : ∀ i, (a.redirect i).Bound c w
  active : ∀ j, (a.active j).Bound c w
  fits : ∀ r, Fits w (a.holding r).value
  buyers : k.size ≤ w
  sites : m.size ≤ w
  positive : 1 ≤ w

def finEqual {n : ℕ} (i j : Fin n) : Run Bool :=
  step (max i.val.size j.val.size) (decide (i=j))

@[simp] theorem finEqual_value {n : ℕ} (i j : Fin n) : (finEqual i j).value = decide (i=j) := rfl

theorem finEqual_work {n w : ℕ} (i j : Fin n) (h : n.size ≤ w) : (finEqual i j).Bound 1 w :=
  (bound_step _ _).weaken le_rfl (max_le ((Nat.size_le_size i.isLt.le).trans h)
    ((Nat.size_le_size j.isLt.le).trans h))

def masked (test : Run Bool) (read : Unit → Run ℚ) : Run ℚ := do
  let b ← test
  if b then read () else pure 0

@[simp] theorem masked_value (test : Run Bool) (read : Unit → Run ℚ) :
    (masked test read).value = if test.value then (read ()).value else 0 := by
  cases e : test.value <;> simp [masked,e]

theorem masked_work {c d w : ℕ} {test : Run Bool} {read : Unit → Run ℚ}
    (ht : test.Bound c w) (hr : (read ()).Bound d w) : (masked test read).Bound (c+d) w := by
  apply bound_bind ht
  split
  · exact hr
  · exact (bound_pure _ _).weaken (Nat.zero_le _) le_rfl

theorem masked_fits {w : ℕ} {test : Run Bool} {read : Unit → Run ℚ}
    (f : Fits w (read ()).value) : Fits w (masked test read).value := by
  rw [masked_value]
  split
  · exact f
  · exact Fits.zero.mono f.pos

namespace Access

variable (a : Access k m G A H)

def atSite (j : Fin m) (h : H) : Run ℚ :=
  masked (a.site h >>= fun s => finEqual s j) (fun _ => a.holding (outside (.inr h)))

def atPair (i : Fin k) (j : Fin m) (v : A) : Run ℚ :=
  masked (do
    let f ← a.real v
    let h₁ ← finEqual f.1 i
    let h₂ ← finEqual f.2.1 j
    step 1 (h₁ && h₂)) (fun _ => a.holding (bid (.inl v)))

def redirected (i : Fin k) (j : Fin m) : Run ℚ :=
  masked (a.redirect i >>= fun s => finEqual s j) (fun _ => a.holding (outside (.inl i)))

def coverage (groups : List H) (σ : ℚ) (j : Fin m) : Run ℚ := do
  let yes ← a.active j
  if yes then do
    let total ← qsum (a.atSite j) groups
    divide total σ
  else pure 0

def joint (reals : List A) (i : Fin k) (j : Fin m) : Run ℚ := do
  let v ← qsum (a.atPair i j) reals
  let b ← a.redirected i j
  plus v b

def tables (groups : List H) (reals : List A) (σ : ℚ) :
    Run (Vector ℚ m × Vector (Vector ℚ m) k) := do
  let x ← tabulate m (a.coverage groups σ)
  let q ← tabulate k (fun i => tabulate m (a.joint reals i))
  step 0 (x,q)

theorem coverage_value [DecidableEq H] [Fintype H] {g : Game (Fin k) (Fin m)}
    {layout : Sparse.Layout (Fin k) (Fin m) G A H} {x : Sparse.R (Fin k) (Fin m) A H → ℚ}
    {f : Fin k → Fin m} (rd : Reads a g layout x f) (groups : List H)
    (unique : groups.Nodup) (complete : ∀ h, h ∈ groups) (σ : ℚ) (j : Fin m) :
    (a.coverage groups σ j).value = Sparse.siteCoverage g σ layout x j := by
  by_cases active : 0 < g.gain j
  · simp only [coverage,Run.bind_value,rd.active,active,decide_true,ite_true,divide_value,qsum_value,
      Sparse.siteCoverage,Sparse.siteOutside,atSite,masked_value,finEqual_value,rd.site,rd.holding,
      decide_eq_true_eq]
    rw [list_sum_univ _ groups unique complete]
  · simp [coverage,rd.active,active,Sparse.siteCoverage]

theorem joint_value [DecidableEq A] [Fintype A] {g : Game (Fin k) (Fin m)}
    {layout : Sparse.Layout (Fin k) (Fin m) G A H} {x : Sparse.R (Fin k) (Fin m) A H → ℚ}
    {f : Fin k → Fin m} (rd : Reads a g layout x f) (reals : List A)
    (unique : reals.Nodup) (complete : ∀ h, h ∈ reals) (i : Fin k) (j : Fin m) :
    (a.joint reals i j).value = Sparse.attackJoint layout f x i j := by
  simp only [joint,Run.bind_value,plus_value,qsum_value,atPair,redirected,masked_value,rd.real,
    finEqual_value,rd.holding,rd.redirect,step_value,Bool.and_eq_true,decide_eq_true_eq,
    Sparse.attackJoint]
  rw [list_sum_univ _ reals unique complete]

theorem tables_value [DecidableEq H] [Fintype H] [DecidableEq A] [Fintype A]
    {g : Game (Fin k) (Fin m)} {layout : Sparse.Layout (Fin k) (Fin m) G A H}
    {x : Sparse.R (Fin k) (Fin m) A H → ℚ} {f : Fin k → Fin m} (rd : Reads a g layout x f)
    (groups : List H) (reals : List A) (gu : groups.Nodup) (ga : ∀ h, h ∈ groups)
    (ru : reals.Nodup) (ra : ∀ i, i ∈ reals) (σ : ℚ) :
    (a.tables groups reals σ).value = (Vector.ofFn (Sparse.siteCoverage g σ layout x),
      Vector.ofFn (fun i => Vector.ofFn (Sparse.attackJoint layout f x i))) := by
  simp only [tables,Run.bind_value,tabulate_value,step_value,a.coverage_value rd groups gu ga,
    a.joint_value rd reals ru ra]

def entrySlots (c : ℕ) := 2*c+4

theorem atSite_work {c w : ℕ} (bounds : AccessBound a c w) (j : Fin m) (h : H) :
    (a.atSite j h).Bound (entrySlots c) w := by
  unfold atSite
  apply Run.Bound.weaken (k := (c+1)+c) (w := w) ?_ (by unfold entrySlots; omega) le_rfl
  apply masked_work (d := c) ?_ (bounds.holding _)
  apply bound_bind (bounds.site h)
  exact finEqual_work _ _ bounds.sites

theorem atPair_work {c w : ℕ} (bounds : AccessBound a c w) (i : Fin k) (j : Fin m) (v : A) :
    (a.atPair i j v).Bound (entrySlots c) w := by
  unfold atPair
  apply Run.Bound.weaken (k := (c+(1+(1+1)))+c) (w := w) ?_ (by unfold entrySlots; omega) le_rfl
  apply masked_work (d := c) ?_ (bounds.holding _)
  apply bound_bind (bounds.real v)
  apply bound_bind (finEqual_work _ _ bounds.buyers)
  apply bound_bind (finEqual_work _ _ bounds.sites)
  exact (bound_step 1 _).weaken le_rfl bounds.positive

theorem redirected_work {c w : ℕ} (bounds : AccessBound a c w) (i : Fin k) (j : Fin m) :
    (a.redirected i j).Bound (entrySlots c) w := by
  unfold redirected
  apply Run.Bound.weaken (k := (c+1)+c) (w := w) ?_ (by unfold entrySlots; omega) le_rfl
  apply masked_work (d := c) ?_ (bounds.holding _)
  apply bound_bind (bounds.redirect i)
  exact finEqual_work _ _ bounds.sites

def projectionWidth (n w : ℕ) := scalarWidth (addWidth n w)
def cellSlots (n w c : ℕ) := c+sumSlots n w (entrySlots c)+entrySlots c+4+scalarSlots (addWidth n w)
def rowSlots (n w c : ℕ) := 3*(n+1)+n*cellSlots n w c
def projectionSlots (n w c : ℕ) := rowSlots n w c+3*(n+1)+n*rowSlots n w c+1

private theorem narrow (n w : ℕ) : w ≤ projectionWidth n w := by
  unfold projectionWidth scalarWidth addWidth; omega

theorem coverage_work {c w n : ℕ} (bounds : AccessBound a c w) (groups : List H) (len : groups.length ≤ n)
    {σ : ℚ} (fs : Fits w σ) (j : Fin m) :
    (a.coverage groups σ j).Bound (cellSlots n w c) (projectionWidth n w) := by
  let test := a.atSite j
  let b := addWidth n w
  let u := projectionWidth n w
  have item (h) : (test h).Bound (entrySlots c) u := (a.atSite_work bounds j h).weaken le_rfl (narrow n w)
  have fits (h) : Fits w (test h).value := masked_fits (bounds.fits _)
  have total := qsum_work test groups len item fits (show scalarWidth b ≤ u from le_rfl)
  have ht : sumBits groups.length w ≤ b :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ len) 1).trans (Nat.le_add_right ..)
  have normalize := divide_work ((list_sum_fits test groups fits).mono ht)
    (fs.mono (show w ≤ b from Nat.le_add_left ..))
  unfold coverage
  apply (bound_bind ((bounds.active j).weaken le_rfl (narrow n w)) (l := sumSlots n w (entrySlots c)+
    (4+scalarSlots b)) ?_).weaken (by unfold cellSlots; dsimp only [b]; omega) le_rfl
  split
  · exact bound_bind total normalize
  · exact (bound_pure _ _).weaken (Nat.zero_le _) le_rfl

theorem joint_work {c w n : ℕ} (bounds : AccessBound a c w) (reals : List A) (len : reals.length ≤ n)
    (i : Fin k) (j : Fin m) : (a.joint reals i j).Bound (cellSlots n w c) (projectionWidth n w) := by
  let test := a.atPair i j
  let b := addWidth n w
  let u := projectionWidth n w
  have fits (v) : Fits w (test v).value := masked_fits (bounds.fits _)
  have item (v) := (a.atPair_work bounds i j v).weaken le_rfl (narrow n w)
  have total := qsum_work test reals len item fits (show scalarWidth b ≤ u from le_rfl)
  have ht : sumBits reals.length w ≤ b :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ len) 1).trans (Nat.le_add_right ..)
  have rfit : Fits w (a.redirected i j).value := masked_fits (bounds.fits _)
  have addition := plus_work ((list_sum_fits test reals fits).mono ht)
    (rfit.mono (show w ≤ b from Nat.le_add_left ..))
  exact (bound_bind total (bound_bind ((a.redirected_work bounds i j).weaken le_rfl (narrow n w))
    addition)).weaken (by unfold cellSlots; dsimp only [b]; omega) le_rfl

theorem tables_work {c w n : ℕ} (bounds : AccessBound a c w) (groups : List H) (reals : List A)
    (hlen : groups.length ≤ n) (alen : reals.length ≤ n) (buyers : k ≤ n) (sites : m ≤ n)
    {σ : ℚ} (fs : Fits w σ) :
    (a.tables groups reals σ).Bound (projectionSlots n w c) (projectionWidth n w) := by
  let u := projectionWidth n w
  have km : k.size ≤ u := bounds.buyers.trans (narrow n w)
  have mm : m.size ≤ u := bounds.sites.trans (narrow n w)
  have row : 3*(m+1)+m*cellSlots n w c ≤ rowSlots n w c :=
    Nat.add_le_add (Nat.mul_le_mul_left 3 (Nat.succ_le_succ sites)) (Nat.mul_le_mul_right _ sites)
  have cov := (tabulate_bound _ mm (a.coverage_work bounds groups hlen fs)).weaken row le_rfl
  have joint (i) := (tabulate_bound _ mm (a.joint_work bounds reals alen i)).weaken row le_rfl
  have all := (tabulate_bound _ km joint).weaken (Nat.add_le_add
    (Nat.mul_le_mul_left 3 (Nat.succ_le_succ buyers)) (Nat.mul_le_mul_right _ buyers)) le_rfl
  exact (bound_bind cov (bound_bind all ((bound_step 0 _).weaken le_rfl (Nat.zero_le u)))).weaken
    (by unfold projectionSlots; omega) le_rfl

end Access
end Kintali.TrialWork
