module

public import Kintali.TrialWork.Fields

/-! Best responses are computed by a charged scan which retains the first
minimum. The reference, mark and endpoint-status tables are saved for reuse. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun ContactSize ExactRecovery LinearProgramming.ArithmeticRun

variable {k m : ℕ} {α : Type}

def leastAux (score : α → Run ℚ) (best : α) : List α → Run α
  | [] => step 0 best
  | x::xs => do
    let next ← step 0 x
    let b ← score best
    let a ← score next
    let keep ← le b a
    leastAux score (if keep then best else next) xs

theorem leastAux_value (score : α → Run ℚ) (best : α) (xs : List α) :
    (leastAux score best xs).value = (best::xs).minOn (fun i => (score i).value) (by simp) := by
  induction xs generalizing best with
  | nil => simp [leastAux]
  | cons x xs ih =>
    simp only [leastAux,Run.bind_value,step_value,le_value,List.minOn_cons_cons]
    by_cases h : (score best).value ≤ (score x).value <;> simp [h,minOn_eq_ite,ih]

theorem leastAux_work (score : α → Run ℚ) (best : α) (xs : List α) {c v w : ℕ}
    (cost : ∀ i, (score i).Bound c w) (fits : ∀ i, Fits v (score i).value)
    (small : scalarWidth v ≤ w) :
    (leastAux score best xs).Bound (1+xs.length*(2*c+4)) w := by
  induction xs generalizing best with
  | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
  | cons x xs ih =>
    unfold leastAux
    apply Run.Bound.weaken (k := 1+(c+(c+(3+(1+xs.length*(2*c+4)))))) (w := w) ?_
      (by rw [List.length_cons,Nat.add_mul,Nat.one_mul]; omega) le_rfl
    apply bound_bind ((bound_step 0 _).weaken le_rfl (Nat.zero_le w))
    apply bound_bind (cost best)
    apply bound_bind (cost x)
    apply bound_bind ((le_work (fits best) (fits x)).weaken le_rfl small)
    exact ih _

def bestFin (n : ℕ) (hm : 0 < n) (score : Fin n → Run ℚ) : Run (Fin n) := do
  let js ← finRange n
  match js with
  | [] => pure ⟨0,hm⟩
  | x::xs => leastAux score x xs

theorem bestFin_value (n : ℕ) (hm : 0 < n) (score : Fin n → Run ℚ) :
    (bestFin n hm score).value = (List.finRange n).minOn (fun i => (score i).value)
      (List.ne_nil_of_mem (List.mem_finRange ⟨0,hm⟩)) := by
  simp only [bestFin,Run.bind_value,finRange_value]
  have aux (js : List (Fin n)) (hne : js ≠ []) :
      (match js with | [] => (pure ⟨0,hm⟩ : Run (Fin n)) | x::xs => leastAux score x xs).value =
        js.minOn (fun i => (score i).value) hne := by
    cases js with
    | nil => exact (hne rfl).elim
    | cons x xs => exact leastAux_value ..
  exact aux _ _

theorem bestFin_work {n c v w : ℕ} (hm : 0 < n) (score : Fin n → Run ℚ) (idx : n.size ≤ w)
    (cells : ∀ i, (score i).Bound c w) (bits : ∀ i, Fits v (score i).value) (small : scalarWidth v ≤ w) :
    (bestFin n hm score).Bound (2*n+1+(1+n*(2*c+4))) w := by
  apply bound_bind ((finRange_bound n).weaken le_rfl idx)
  rw [finRange_value]
  cases eq : List.finRange n with
  | nil => exact (bound_pure _ _).weaken (Nat.zero_le _) le_rfl
  | cons x xs =>
    have len := congrArg List.length eq
    simp only [List.length_finRange,List.length_cons] at len
    exact (leastAux_work score x xs cells bits small).weaken
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) le_rfl

def mark (d : Fields k m) (v : Point k m) (ref : Vector (Fin m) k) (i : Fin k) (j : Fin m) :
    Run Bool := do
  let b ← step k.size ref[i.val]
  let y ← d.pointCost v i j
  let z ← d.pointCost v i b
  let allowed ← plus z v.tolerance
  le y allowed

@[simp] theorem mark_value (d : Fields k m) (v : Point k m) (ref : Vector (Fin m) k) (i j) :
    (mark d v ref i j).value = decide (d.game.cost i j (v.x j) ≤
      d.game.cost i ref[i.val] (v.x ref[i.val])+v.tolerance) := by simp [mark]

def status (v : Point k m) (j : Fin m) : Run Status := do
  let x ← v.readX j
  let lo ← eqRat x 0
  if lo then pure .lower else do
    let hi ← eqRat x 1
    pure (if hi then .upper else .balanced)

@[simp] theorem status_value (v : Point k m) (j) : (status v j).value = statusAt (v.x j) := by
  by_cases a : v.x j = 0 <;> by_cases b : v.x j = 1 <;> simp [status,statusAt,a,b]

def pattern (d : Fields k m) (v : Point k m) (hm : 0 < m) (tol : 0 ≤ v.tolerance) :
    Run (Pattern (Fin k) (Fin m)) :=
  let refs := tabulate k (fun i => bestFin m hm (d.pointCost v i))
  let marks := tabulate k (fun i => tabulate m (mark d v refs.value i))
  let states := tabulate m (status v)
  let p : Pattern (Fin k) (Fin m) :=
    ⟨fun i => refs.value[i.val],fun i j => marks.value[i.val][j.val],by
      intro i
      simp only [marks,tabulate_value,Vector.getElem_ofFn,mark_value,decide_eq_true_eq]
      exact le_add_of_nonneg_right tol,
      fun j => states.value[j.val]⟩
  ⟨p,refs.work.seq (marks.work.seq (states.work.seq (Work.one 0)))⟩

theorem pattern_value (d : Fields k m) (v : Point k m) (hm : 0 < m) (tol : 0 ≤ v.tolerance) :
    (pattern d v hm tol).value =
      contactPattern d.game v.x (d.game.bestTarget hm v.x) v.tolerance tol := by
  simp only [pattern,tabulate_value,Vector.getElem_ofFn,bestFin_value,Fields.pointCost_value,
    mark_value,status_value,contactPattern,Game.bestTarget]
  rfl

def patternWidth (w : ℕ) := scalarWidth (4*w+2)
def markSlots (c w : ℕ) := 1+2*(1+costSlots c w)+scalarSlots (3*w+1)+3
def referenceSlots (n c w : ℕ) := 2*n+1+(1+n*(2*(1+costSlots c w)+4))
def tableSlots (n c : ℕ) := 3*(n+1)+n*c

def patternSlots (k m c w : ℕ) :=
  tableSlots k (referenceSlots m c w)+tableSlots k (tableSlots m (markSlots c w))+tableSlots m 7+1

theorem mark_work (d : Fields k m) {v : Point k m} {c w : ℕ} (ok : FieldBound d c w) (point : PointBound v w)
    (ref : Vector (Fin m) k) (i j) : (mark d v ref i j).Bound (markSlots c w) (patternWidth w) := by
  let u := patternWidth w
  have cwide : costWidth w ≤ u := by unfold u patternWidth costWidth scalarWidth; omega
  have lew : w ≤ 3*w+1 := by omega
  have mid : scalarWidth (3*w+1) ≤ u := by unfold u patternWidth scalarWidth; omega
  have yw := d.cost_fits ok i j (point.coverage j)
  have zw := d.cost_fits ok i ref[i.val] (point.coverage ref[i.val])
  have sf := zw.add point.tolerance
  unfold mark
  apply Run.Bound.weaken (k := 1+((1+costSlots c w)+((1+costSlots c w)+(scalarSlots (3*w+1)+3))))
    (w := u) ?_ (by unfold markSlots; omega) le_rfl
  apply bound_bind ((bound_step _ _).weaken le_rfl (ok.kSize.trans (by unfold u patternWidth scalarWidth; omega)))
  apply bound_bind ((d.pointCost_work ok point i j).weaken le_rfl cwide)
  apply bound_bind ((d.pointCost_work ok point i ref[i.val]).weaken le_rfl cwide)
  simp only [Fields.pointCost_value]
  apply bound_bind ((plus_work zw (point.tolerance.mono lew)).weaken le_rfl mid)
  rw [plus_value]
  exact le_work (yw.mono (show 3*w+1 ≤ 4*w+2 by omega)) (sf.mono (by omega))

theorem status_work {v : Point k m} {c w : ℕ} {d : Fields k m} (ok : FieldBound d c w)
    (small : PointBound v w) (j) : (status v j).Bound 7 (patternWidth w) := by
  have narrow : scalarWidth w ≤ patternWidth w := by unfold patternWidth scalarWidth; omega
  have hw : w ≤ patternWidth w := by unfold patternWidth scalarWidth; omega
  unfold status
  apply bound_bind (l := 6) ((v.readX_bound j ok.mSize).weaken le_rfl hw)
  apply bound_bind (l := 3) ((eqRat_work (small.coverage j) (Fits.zero.mono ok.positive)).weaken le_rfl narrow)
  split
  · exact (bound_pure _ _).weaken (by decide) le_rfl
  · exact bound_bind ((eqRat_work (small.coverage j) (Fits.one.mono ok.positive)).weaken le_rfl narrow)
      (bound_pure _ _)

theorem pattern_work (d : Fields k m) {v : Point k m} {c w : ℕ} (ok : FieldBound d c w)
    (small : PointBound v w) (hm : 0 < m) (tol : 0 ≤ v.tolerance) :
    (pattern d v hm tol).Bound (patternSlots k m c w) (patternWidth w) := by
  let u := patternWidth w
  have h : w ≤ u := by unfold u patternWidth scalarWidth; omega
  have cost : costWidth w ≤ u := by unfold u patternWidth costWidth scalarWidth; omega
  have mid : scalarWidth (3*w+1) ≤ u := by unfold u patternWidth scalarWidth; omega
  have ref (i) := bestFin_work hm (d.pointCost v i) (ok.mSize.trans h)
    (fun j => (d.pointCost_work ok small i j).weaken le_rfl cost)
    (fun j => by rw [Fields.pointCost_value]; exact d.cost_fits ok i j (small.coverage j)) mid
  have refs := tabulate_bound _ (ok.kSize.trans h) ref
  let R := (tabulate k (fun i => bestFin m hm (d.pointCost v i))).value
  have mark (i) := tabulate_bound _ (ok.mSize.trans h) (mark_work d ok small R i)
  have marks := tabulate_bound _ (ok.kSize.trans h) mark
  have states := tabulate_bound _ (ok.mSize.trans h) (status_work ok small)
  change (_+(_+(_+1)) ≤ _) ∧ max _ (max _ (max _ 0)) ≤ u
  exact ⟨(Nat.add_le_add refs.1 (Nat.add_le_add marks.1 (Nat.add_le_add_right states.1 1))).trans
    (by unfold patternSlots tableSlots referenceSlots; omega), max_le refs.2 (max_le marks.2 (max_le states.2 (Nat.zero_le _)))⟩

end Kintali.TrialWork
