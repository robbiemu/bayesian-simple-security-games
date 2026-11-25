module

public import Kintali.InputOutput.NormalizedWork
public import Kintali.ContactSize.Parameters

/-! # Charging the closed-form eligibility prefix on stored coefficients

The input to a cell consists of the cached grid, outside cost, gain, intercept
and slope. The horizontal branch includes endpoint ties. The positive-slope
branch rounds a normalized rational down and caps the count at the grid.
-/

@[expose] public section
namespace Kintali.InputOutput.EligibilityWork

open Binary ContactSize TrialWork NormalizedWork StochasticGames.CompilerRun StochasticGames.BinarySize
open ExactRecovery MarketTrial LinearProgramming.ArithmeticRun

def floorNat (q : ℚ) : Run ℕ := do
  let n ← step (max q.num.natAbs.size q.den.size+1) (q.num / (q.den : ℤ))
  step (n.natAbs.size+1) n.toNat

@[simp] theorem floor_value (q : ℚ) : (floorNat q).value = ⌊q⌋₊ := by
  simp only [floorNat,Run.bind_value,step_value,← Int.floor_toNat,Rat.floor_def']

theorem floor_work {w : ℕ} {q : ℚ} (h : Fits w q) : (floorNat q).Bound 2 (w+1) := by
  have n := (Nat.size_le_size (Int.natAbs_ediv_le_natAbs q.num (q.den : ℤ))).trans h.1
  obtain ⟨hn,hd⟩ := h
  simp [floorNat,Run.Bound]
  omega

theorem floor_width {w : ℕ} {q : ℚ} (h : Fits w q) : (⌊q⌋₊).size ≤ w := by
  rw [← Int.floor_toNat,Rat.floor_def']
  have abs (n : ℤ) : n.toNat ≤ n.natAbs := by rw [← Int.toNat_add_toNat_neg_eq_natAbs]; omega
  exact (Nat.size_le_size ((abs _).trans (Int.natAbs_ediv_le_natAbs _ _))).trans h.1

def count (G : ℕ) (gain intercept slope outside : ℚ) : Run ℕ := do
  let active ← lt 0 gain
  let allowed ← le intercept outside
  if active && allowed then
    let flat ← eqRat slope 0
    if flat then step 0 G else do
      let n ← neg intercept
      let diff ← plus outside n
      let g ← step (G.size+1) (G : ℚ)
      let product ← times diff g
      let q ← divide product slope
      let f ← floorNat q
      let upper ← natAdd f 1
      step (max G.size upper.size) (min G upper)
  else step 0 0

def countSlots (w : ℕ) := 3*scalarSlots (4*w+3)+32
def countWidth (w : ℕ) := scalarWidth (4*w+3)

theorem count_work {w G : ℕ} {g a b o : ℚ} (grid : G.size+1 ≤ w) (gain : Fits w g)
    (intercept : Fits w a) (slope : Fits w b) (outside : Fits w o) :
    (count G g a b o).Bound (countSlots w) (countWidth w) := by
  let u := 4*w+3
  have small : w ≤ u := by dsimp [u]; omega
  have zero := Fits.zero.mono (by omega : 1 ≤ w)
  have gf := (Fits.natCast G).mono grid
  have nf := neg_fits intercept
  have df := outside.add nf
  have pf := df.mul gf
  have qf := pf.div slope
  have du : Fits u (o + -a) := df.mono (by dsimp [u]; omega)
  have pu : Fits u ((o + -a) * G) := pf.mono (by dsimp [u]; omega)
  have qu : Fits u ((o + -a)*G/b) := qf.mono (by dsimp [u]; omega)
  have active := lt_work (zero.mono small) (gain.mono small)
  have allowed := le_work (intercept.mono small) (outside.mono small)
  have flat := eqRat_work (slope.mono small) (zero.mono small)
  have n := neg_work (intercept.mono small)
  have add := plus_work (outside.mono small) (nf.mono small)
  have prod := times_work du (gf.mono small)
  have div := divide_work pu (slope.mono small)
  have f := floor_work qu
  have fw := floor_width qu
  have up := size_succ_le ⌊(o + -a)*G/b⌋₊
  by_cases A : 0 < g <;> by_cases C : a ≤ o <;> by_cases B : b = 0 <;>
    simp only [count,Run.Bound,Run.bind_slots,Run.bind_width,lt_value,le_value,eqRat_value,
      Bool.and_eq_true,decide_eq_true_eq,A,C,B,true_and,false_and,ite_true,ite_false,step_slots,step_width,step_value,
      neg_value,plus_value,times_value,divide_value,floor_value,natAdd,Nat.size_one,
      countSlots,countWidth,scalarWidth,scalarSlots] at * <;>
    dsimp only [u] at * <;> omega

theorem count_value {k m : ℕ} (g : Game (Fin k) (Fin m)) (redirect : Fin k → Fin m)
    (G : ℕ) (i : Fin k) (j : Fin m) :
    (count G (g.gain j) (g.intercept i j) (g.slope i j) (Holdings.outsideCost g redirect i)).value =
      eligibleCount g redirect G i j := by
  by_cases A : 0 < g.gain j <;> by_cases C : g.intercept i j ≤ Holdings.outsideCost g redirect i <;>
    by_cases B : g.slope i j = 0 <;> simp [count,eligibleCount,sub_eq_add_neg,natAdd,A,C,B]

/-- A row and its two rational fields share one vector cell. -/
def cell {k m : ℕ} (t : Tables k m) (outside : Vector ℚ k) (G : ℕ) (i : Fin k) (j : Fin m) : Run ℕ := do
  let row ← step i.val.size t.bids[i.val]
  let b ← step j.val.size row[j.val]
  let g ← step j.val.size t.gains[j.val]
  let o ← step i.val.size outside[i.val]
  count G g b.1 b.2 o

def fill {k m : ℕ} (t : Tables k m) (outside : Vector ℚ k) (G n : ℕ) (length : n = k*m) : Run (Vector ℕ n) :=
  tabulate n fun ix => do
    let p := Fin.cast length ix
    let i ← step (max p.val.size m.size) (finProdFinEquiv.symm p).1
    let j ← step (max p.val.size m.size) (finProdFinEquiv.symm p).2
    cell t outside G i j

/-- Computing the product dimension supplies the allocation bound. -/
def table {k m : ℕ} (t : Tables k m) (outside : Vector ℚ k) (G : ℕ) : Run (Vector ℕ (k*m)) :=
  let dimension := natMul k m
  let rows := fill t outside G dimension.value rfl
  ⟨rows.value,dimension.work.seq rows.work⟩

private theorem fill_work {k m S w G : ℕ} (t : Tables k m) (outside : Vector ℚ k) (kd : k ≤ S) (md : m ≤ S)
    (wide : S*S+S ≤ w) (grid : G.size+1 ≤ w) (gains : ∀ j : Fin m, Fits w t.gains[j.val])
    (bids : ∀ (i : Fin k) (j : Fin m), Fits w t.bids[i.val][j.val].1 ∧ Fits w t.bids[i.val][j.val].2)
    (out : ∀ i : Fin k, Fits w outside[i.val]) :
    (fill t outside G (k*m) rfl).Bound (3*(S*S+1)+S*S*(6+countSlots w)) (countWidth w) := by
  have dim := Nat.mul_le_mul kd md
  have W : w ≤ countWidth w := by unfold countWidth scalarWidth; omega
  have each (p : Fin (k*m)) :=
    let ij := finProdFinEquiv.symm p
    count_work grid (gains ij.2) (bids ij.1 ij.2).1 (bids ij.1 ij.2).2 (out ij.1)
  apply (tabulate_bound _ (cost := 6+countSlots w)
    ((size_le_self _).trans (dim.trans (by omega))) ?_).weaken ?_ le_rfl
  · intro p
    let ij := finProdFinEquiv.symm p
    have ps := (size_le_self p.val).trans (p.isLt.le.trans dim)
    have ms := (size_le_self m).trans md
    have ii := (size_le_self ij.1.val).trans (ij.1.isLt.le.trans kd)
    have jj := (size_le_self ij.2.val).trans (ij.2.isLt.le.trans md)
    have h := each p
    simp only [cell,Run.Bound,Run.bind_slots,Run.bind_width,step_value,step_slots,step_width] at *
    dsimp only [ij] at *
    simp only [Fin.cast_refl,id_eq] at *
    omega
  · gcongr

theorem table_work {k m S w G : ℕ} (t : Tables k m) (outside : Vector ℚ k) (kd : k ≤ S) (md : m ≤ S)
    (wide : S*S+S ≤ w) (grid : G.size+1 ≤ w) (gains : ∀ j : Fin m, Fits w t.gains[j.val])
    (bids : ∀ (i : Fin k) (j : Fin m), Fits w t.bids[i.val][j.val].1 ∧ Fits w t.bids[i.val][j.val].2)
    (out : ∀ i : Fin k, Fits w outside[i.val]) :
    (table t outside G).Bound (1+(3*(S*S+1)+S*S*(6+countSlots w))) (countWidth w) := by
  have h := fill_work t outside kd md wide grid gains bids out
  have ks := (size_le_self _).trans kd
  have ms := (size_le_self _).trans md
  change 1+(fill t outside G (k*m) rfl).work.slots ≤ _ ∧ max (max k.size m.size) (fill t outside G (k*m) rfl).work.width ≤ _
  exact ⟨Nat.add_le_add_left h.1 1,max_le (by unfold countWidth scalarWidth; omega) h.2⟩

theorem table_value (a : Input) (hm : 0 < a.targets) (t : Tables a.types a.targets) (ht : t.game = a.game)
    (outside : Vector ℚ a.types)
    (ho : ∀ i : Fin a.types, outside[i.val] = Holdings.outsideCost a.game (redirect a.game hm) i) :
    (table t outside (grid a.game)).value = eligible a.game hm := by
  apply Vector.ext
  intro p hp
  simp only [table,fill,natMul,step_value,tabulate_value,Vector.getElem_ofFn,Run.bind_value,cell,eligible]
  let ij := finProdFinEquiv.symm (⟨p,hp⟩ : Fin (a.types*a.targets))
  have hg : t.gains[ij.2.val] = a.game.gain ij.2 := congrArg (fun g => Game.gain g ij.2) ht
  have hi : t.bids[ij.1.val][ij.2.val].1 = a.game.intercept ij.1 ij.2 := congrArg (fun g => Game.intercept g ij.1 ij.2) ht
  have hs : t.bids[ij.1.val][ij.2.val].2 = a.game.slope ij.1 ij.2 := congrArg (fun g => Game.slope g ij.1 ij.2) ht
  change (count _ t.gains[ij.2.val] t.bids[ij.1.val][ij.2.val].1 t.bids[ij.1.val][ij.2.val].2 outside[ij.1.val]).value = _
  rw [hg,hi,hs,ho ij.1]
  exact count_value _ _ _ _ _

end Kintali.InputOutput.EligibilityWork
