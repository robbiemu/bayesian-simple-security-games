module

public import Kintali.TrialWork.Scan
public import Kintali.MarketTrial

/-! Stored payoff and projected-point fields for trial comparisons. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize ExactRecovery

variable {k m : ℕ}

structure Fields (k m : ℕ) where
  budget : ℕ
  prior : Fin k → Run ℚ
  gain : Fin m → Run ℚ
  intercept : Fin k → Fin m → Run ℚ
  slope : Fin k → Fin m → Run ℚ

def Fields.game (d : Fields k m) : Game (Fin k) (Fin m) :=
  ⟨d.budget, fun i => (d.prior i).value,fun i j => (d.intercept i j).value,
    fun i j => (d.slope i j).value, fun j => (d.gain j).value⟩

structure FieldBound (d : Fields k m) (c w : ℕ) : Prop where
  prior : ∀ i, (d.prior i).Bound c w ∧ Fits w (d.prior i).value
  gain : ∀ j, (d.gain j).Bound c w ∧ Fits w (d.gain j).value
  intercept : ∀ i j, (d.intercept i j).Bound c w ∧ Fits w (d.intercept i j).value
  slope : ∀ i j, (d.slope i j).Bound c w ∧ Fits w (d.slope i j).value
  budget : Fits w (d.budget : ℚ)
  kSize : k.size ≤ w
  mSize : m.size ≤ w
  positive : 1 ≤ w

structure Point (k m : ℕ) where
  coverage : Vector ℚ m
  joint : Vector (Vector ℚ m) k
  threshold : ℚ
  tolerance : ℚ

namespace Point

def x (v : Point k m) (j : Fin m) := v.coverage[j.val]
def q (v : Point k m) (i : Fin k) (j : Fin m) := v.joint[i.val][j.val]

def readX (v : Point k m) (j : Fin m) := step m.size (v.x j)

def readQ (v : Point k m) (i : Fin k) (j : Fin m) : Run ℚ := do
  let row ← step k.size v.joint[i.val]
  step m.size row[j.val]

@[simp] theorem readX_value (v : Point k m) (j) : (v.readX j).value = v.x j := rfl
@[simp] theorem readQ_value (v : Point k m) (i j) : (v.readQ i j).value = v.q i j := rfl

theorem readX_bound (v : Point k m) (j) {w : ℕ} (h : m.size ≤ w) : (v.readX j).Bound 1 w :=
  (bound_step _ _).weaken le_rfl h

theorem readQ_bound (v : Point k m) (i j) {w : ℕ} (hk : k.size ≤ w) (hm : m.size ≤ w) :
    (v.readQ i j).Bound 2 w := ⟨le_rfl,max_le hk hm⟩

end Point

structure PointBound (v : Point k m) (w : ℕ) : Prop where
  coverage : ∀ j, Fits w (v.x j)
  joint : ∀ i j, Fits w (v.q i j)
  threshold : Fits w v.threshold
  tolerance : Fits w v.tolerance

def Fields.costAt (d : Fields k m) (i : Fin k) (j : Fin m) (x : ℚ) : Run ℚ := do
  let a ← d.intercept i j
  let b ← d.slope i j
  let v ← times b x
  plus a v

@[simp] theorem Fields.costAt_value (d : Fields k m) (i j x) :
    (d.costAt i j x).value = d.game.cost i j x := by simp [Fields.costAt,Fields.game,Game.cost]

theorem Fields.cost_fits (d : Fields k m) {c w : ℕ} (ok : FieldBound d c w) (i j)
    {x : ℚ} (small : Fits w x) : Fits (3*w+1) (d.game.cost i j x) :=
  ((ok.intercept i j).2.add ((ok.slope i j).2.mul small)).mono (by omega)

def costSlots (c w : ℕ) := 2*c+scalarSlots w+scalarSlots (2*w)
def costWidth (w : ℕ) := scalarWidth (2*w)

theorem Fields.costAt_work (d : Fields k m) {c w : ℕ} (ok : FieldBound d c w) (i j)
    {x : ℚ} (small : Fits w x) : (d.costAt i j x).Bound (costSlots c w) (costWidth w) := by
  have narrow : w ≤ costWidth w := by unfold costWidth scalarWidth; omega
  have up : scalarWidth w ≤ costWidth w := by unfold costWidth scalarWidth; omega
  unfold Fields.costAt
  apply Run.Bound.weaken (k := c+(c+(scalarSlots w+scalarSlots (2*w)))) (w := costWidth w) ?_
    (by unfold costSlots; omega) le_rfl
  apply bound_bind ((ok.intercept i j).1.weaken le_rfl narrow)
  apply bound_bind ((ok.slope i j).1.weaken le_rfl narrow)
  apply bound_bind ((times_work (ok.slope i j).2 small).weaken le_rfl up)
  rw [times_value]
  exact plus_work ((ok.intercept i j).2.mono (by omega))
    (((ok.slope i j).2.mul small).mono (by omega))

def Fields.pointCost (d : Fields k m) (v : Point k m) (i : Fin k) (j : Fin m) : Run ℚ :=
  v.readX j >>= d.costAt i j

@[simp] theorem Fields.pointCost_value (d : Fields k m) (v : Point k m) (i j) :
    (d.pointCost v i j).value = d.game.cost i j (v.x j) := by simp [Fields.pointCost]

theorem Fields.pointCost_work (d : Fields k m) {c w : ℕ} (ok : FieldBound d c w)
    {v : Point k m} (small : PointBound v w) (i j) :
    (d.pointCost v i j).Bound (1+costSlots c w) (costWidth w) := by
  apply bound_bind ((v.readX_bound j ok.mSize).weaken le_rfl (by unfold costWidth scalarWidth; omega))
  exact d.costAt_work ok i j (small.coverage j)

theorem FieldBound.mono {d : Fields k m} {c w u : ℕ} (ok : FieldBound d c w) (h : w ≤ u) :
    FieldBound d c u :=
  ⟨fun i => ⟨(ok.prior i).1.weaken le_rfl h,(ok.prior i).2.mono h⟩,
    fun j => ⟨(ok.gain j).1.weaken le_rfl h,(ok.gain j).2.mono h⟩,
    fun i j => ⟨(ok.intercept i j).1.weaken le_rfl h,(ok.intercept i j).2.mono h⟩,
    fun i j => ⟨(ok.slope i j).1.weaken le_rfl h,(ok.slope i j).2.mono h⟩,
    ok.budget.mono h,ok.kSize.trans h,ok.mSize.trans h,ok.positive.trans h⟩

end Kintali.TrialWork
