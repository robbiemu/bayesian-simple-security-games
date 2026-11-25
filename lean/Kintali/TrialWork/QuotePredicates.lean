module

public import Kintali.TrialWork.Fields
public import Kintali.TrialWork.Projection

/-! A retained real bid is compared using cost, site and quote. The record
code in the expanded book cannot break a tie between identical owned bids. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize ExactRecovery QuotaSweep
variable {k m G : ℕ}

def land (x y : Run Bool) : Run Bool := do
  let a ← x
  let b ← y
  step 1 (a && b)

def lor (x y : Run Bool) : Run Bool := do
  let a ← x
  let b ← y
  step 1 (a || b)

@[simp] theorem land_value (x y : Run Bool) : (land x y).value = (x.value && y.value) := rfl
@[simp] theorem lor_value (x y : Run Bool) : (lor x y).value = (x.value || y.value) := rfl

theorem land_work {x y : Run Bool} {c d w : ℕ} (a : x.Bound c w) (b : y.Bound d w) (one : 1 ≤ w) :
    (land x y).Bound (c+(d+1)) w :=
  bound_bind a (bound_bind b ((bound_step _ _).weaken le_rfl one))

theorem lor_work {x y : Run Bool} {c d w : ℕ} (a : x.Bound c w) (b : y.Bound d w) (one : 1 ≤ w) :
    (lor x y).Bound (c+(d+1)) w :=
  bound_bind a (bound_bind b ((bound_step _ _).weaken le_rfl one))

def finLess {n : ℕ} (i j : Fin n) : Run Bool :=
  step (max i.val.size j.val.size) (decide (i.val < j.val))

@[simp] theorem finLess_value {n : ℕ} (i j : Fin n) : (finLess i j).value = decide (i.val < j.val) := rfl

theorem finLess_work {n w : ℕ} (i j : Fin n) (h : n.size ≤ w) : (finLess i j).Bound 1 w :=
  (bound_step _ _).weaken le_rfl (max_le ((Nat.size_le_size i.isLt.le).trans h)
    ((Nat.size_le_size j.isLt.le).trans h))

def priceOf (z : Quote G) : Run ℚ := do
  let n ← step z.val.size (z.val : ℚ)
  let g ← step G.size (G : ℚ)
  divide n g

@[simp] theorem priceOf_value (z : Quote G) : (priceOf z).value = price z := by simp [priceOf,price]

theorem price_fits {w : ℕ} (grid : 2*(G.size+1) ≤ w) (z : Quote G) : Fits w (price z) := by
  have sz := Nat.size_le_size (Nat.lt_succ_iff.mp z.isLt)
  exact ((Fits.natCast z.val).div (Fits.natCast G)).mono (by omega)

theorem priceOf_work {w : ℕ} (grid : 2*(G.size+1) ≤ w) (z : Quote G) :
    (priceOf z).Bound (6+scalarSlots w) (scalarWidth w) := by
  have sz := Nat.size_le_size (Nat.lt_succ_iff.mp z.isLt)
  apply Run.Bound.weaken (k := 1+(1+(4+scalarSlots w))) (w := scalarWidth w) ?_ (by omega) le_rfl
  apply bound_bind ((bound_step _ _).weaken le_rfl (by unfold scalarWidth; omega))
  apply bound_bind ((bound_step _ _).weaken le_rfl (by unfold scalarWidth; omega))
  exact divide_work ((Fits.natCast _).mono (by omega)) ((Fits.natCast _).mono (by omega))

def Fields.quoteCost (d : Fields k m) (i : Fin k) (j : Fin m) (z : Quote G) : Run ℚ :=
  priceOf z >>= d.costAt i j

@[simp] theorem Fields.quoteCost_value (d : Fields k m) (i : Fin k) (j : Fin m) (z : Quote G) :
    (d.quoteCost i j z).value = d.game.cost i j (price z) := by simp [Fields.quoteCost]

def quoteSlots (c w : ℕ) := 6+scalarSlots w+costSlots c w

theorem Fields.quoteCost_work (d : Fields k m) {c w : ℕ} (f : FieldBound d c w)
    (grid : 2*(G.size+1) ≤ w) (i j) (z : Quote G) : (d.quoteCost i j z).Bound (quoteSlots c w) (costWidth w) := by
  apply bound_bind ((priceOf_work grid z).weaken le_rfl (by unfold costWidth scalarWidth; omega))
  rw [priceOf_value]
  exact d.costAt_work f i j (price_fits grid z)

def better (d : Fields k m) (i : Fin k) (j l : Fin m) (z u : Quote G) : Run Bool := do
  let x ← d.quoteCost i j z
  let y ← d.quoteCost i l u
  lor (lt x y) (land (eqRat x y)
    (lor (finLess j l) (land (finEqual j l) (finLess z u))))

theorem owned_key (g : Game (Fin k) (Fin m)) (i : Fin k) (j l : Fin m) (z u : Quote G) :
    Expanded.key g Fin.val Fin.val (.inl (.inl i)) (bid (Expanded.realBid i j z)) <
      Expanded.key g Fin.val Fin.val (.inl (.inl i)) (bid (Expanded.realBid i l u)) ↔
    g.cost i j (price z) < g.cost i l (price u) ∨
      g.cost i j (price z) = g.cost i l (price u) ∧ (j.val < l.val ∨ j = l ∧ z.val < u.val) := by
  change toLex ((↑(g.cost i j (price z)) : WithTop ℚ),toLex (j.val,toLex (z.val,_))) <
    toLex ((↑(g.cost i l (price u)) : WithTop ℚ),toLex (l.val,toLex (u.val,_))) ↔ _
  by_cases e : j = l
  · subst l
    by_cases f : z = u
    · subst u; simp
    · have ne : z.val ≠ u.val := fun h => f (Fin.ext h)
      simp [Prod.Lex.lt_iff,ne]
  · have ne : j.val ≠ l.val := fun h => e (Fin.ext h)
    simp [Prod.Lex.lt_iff,e,ne]

@[simp] theorem better_value (d : Fields k m) (i : Fin k) (j l : Fin m) (z u : Quote G) :
    (better d i j l z u).value = decide (Expanded.key d.game Fin.val Fin.val (.inl (.inl i))
      (bid (Expanded.realBid i j z)) < Expanded.key d.game Fin.val Fin.val (.inl (.inl i))
      (bid (Expanded.realBid i l u))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [better,Run.bind_value,Fields.quoteCost_value,lor_value,land_value,lt_value,eqRat_value,
    finLess_value,finEqual_value,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,owned_key]

def blockWidth (w : ℕ) := scalarWidth (3*w+1)
def betterSlots (c w : ℕ) := 2*quoteSlots c w+14

theorem better_work (d : Fields k m) {c w : ℕ} (ok : FieldBound d c w) (grid : 2*(G.size+1) ≤ w)
    (i : Fin k) (j l : Fin m) (z u : Quote G) :
    (better d i j l z u).Bound (betterSlots c w) (blockWidth w) := by
  let U := blockWidth w
  have h : w ≤ U := by unfold U blockWidth scalarWidth; omega
  have one := ok.positive.trans h
  have cost : costWidth w ≤ U := by unfold U blockWidth costWidth scalarWidth; omega
  have gs : (G+1).size ≤ U := (size_succ_le _).trans (by omega)
  have ms := ok.mSize.trans h
  have x := d.cost_fits ok i j (price_fits grid z)
  have y := d.cost_fits ok i l (price_fits grid u)
  have keys := lor_work (lt_work x y) (land_work (eqRat_work x y)
    (lor_work (finLess_work j l ms) (land_work (finEqual_work j l ms) (finLess_work z u gs) one) one) one) one
  unfold better
  apply Run.Bound.weaken (k := quoteSlots c w+(quoteSlots c w+14)) (w := U) ?_ (by unfold betterSlots; omega) le_rfl
  apply bound_bind ((d.quoteCost_work ok grid i j z).weaken le_rfl cost)
  apply bound_bind ((d.quoteCost_work ok grid i l u).weaken le_rfl cost)
  rw [Fields.quoteCost_value,Fields.quoteCost_value]
  exact keys

end Kintali.TrialWork
