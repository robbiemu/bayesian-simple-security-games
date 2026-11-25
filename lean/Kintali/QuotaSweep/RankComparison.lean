module

public import Kintali.QuotaSweep.RankRun
public import Kintali.QuotaSweep.SelectedPreparation

/-! # Addressed comparison of the four fields of a stored sparse ordinal key -/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open Kintali.ExactRecovery Kintali.ContactSize Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch
open StochasticGames.CompilerRun

def natLess (x y : ℕ) : Run Bool := step (max x.size y.size) (decide (x<y))
def natEqual (x y : ℕ) : Run Bool := step (max x.size y.size) (decide (x=y))

def nullableLess (x y : WithTop ℚ) : Run Bool := do
  let t ← step 0 (x,y)
  match t.1,t.2 with
  | some q,some r => TrialWork.lt q r
  | none,_ => step 1 false
  | some _,none => step 1 true

def nullableEqual (x y : WithTop ℚ) : Run Bool := do
  let t ← step 0 (x,y)
  match t.1,t.2 with
  | some q,some r => TrialWork.eqRat q r
  | none,none => step 1 true
  | _,_ => step 1 false

private theorem nullableLess_value (x y : WithTop ℚ) : (nullableLess x y).value = decide (x<y) := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe <;> simp [nullableLess]

private theorem nullableEqual_value (x y : WithTop ℚ) : (nullableEqual x y).value = decide (x=y) := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe <;> simp [nullableEqual]

def PrimaryFits (w : ℕ) (x : WithTop ℚ) := ∀ q : ℚ, x = (q : WithTop ℚ) → Fits w q

private theorem nullableLess_work (x y : WithTop ℚ) {w : ℕ} (hx : PrimaryFits w x) (hy : PrimaryFits w y) :
    (nullableLess x y).Bound 5 (TrialWork.scalarWidth w) := by
  have h : 1 ≤ TrialWork.scalarWidth w := by unfold TrialWork.scalarWidth; omega
  unfold nullableLess
  apply bound_bind (l := 4) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe
  all_goals first | exact (bound_step 1 _).weaken (by decide) h | exact TrialWork.lt_work (hx _ rfl) (hy _ rfl)

private theorem nullableEqual_work (x y : WithTop ℚ) {w : ℕ} (hx : PrimaryFits w x) (hy : PrimaryFits w y) :
    (nullableEqual x y).Bound 4 (TrialWork.scalarWidth w) := by
  have h : 1 ≤ TrialWork.scalarWidth w := by unfold TrialWork.scalarWidth; omega
  unfold nullableEqual
  apply bound_bind (l := 3) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe
  all_goals first | exact (bound_step 1 _).weaken (by decide) h | exact TrialWork.eqRat_work (hx _ rfl) (hy _ rfl)

def lex (l eq tail : Run Bool) : Run Bool := do
  let a ← l
  let b ← eq
  let c ← tail
  step 1 (a || (b && c))

private theorem lex_work {l eq tail : Run Bool} {k j n w : ℕ} (h : 1 ≤ w)
    (hl : l.Bound k w) (he : eq.Bound j w) (ht : tail.Bound n w) :
    (lex l eq tail).Bound (k+(j+(n+1))) w :=
  bound_bind hl (bound_bind he (bound_bind ht ((bound_step _ _).weaken le_rfl h)))

private theorem lex_correct {A B : Type} [LinearOrder A] [LinearOrder B]
    (x y : A ×ₗ B) (l eq tail : Run Bool) (hl : l.value = decide ((ofLex x).1 < (ofLex y).1))
    (he : eq.value = decide ((ofLex x).1 = (ofLex y).1))
    (ht : tail.value = decide ((ofLex x).2 < (ofLex y).2)) :
    (lex l eq tail).value = decide (x<y) := by
  apply Bool.eq_iff_iff.mpr
  simp [lex,hl,he,ht,Prod.Lex.lt_iff]

def keyLess (x y : Expanded.Key) : Run Bool :=
  let a := ofLex x
  let b := ofLex y
  let c := ofLex a.2
  let d := ofLex b.2
  let e := ofLex c.2
  let f := ofLex d.2
  lex (nullableLess a.1 b.1) (nullableEqual a.1 b.1)
    (lex (natLess c.1 d.1) (natEqual c.1 d.1)
      (lex (natLess e.1 f.1) (natEqual e.1 f.1) (natLess e.2 f.2)))

theorem keyLess_value (x y : Expanded.Key) : (keyLess x y).value = decide (x<y) :=
  lex_correct x y _ _ _ (nullableLess_value ..) (nullableEqual_value ..)
    (lex_correct _ _ _ _ _ rfl rfl (lex_correct _ _ _ _ _ rfl rfl rfl))

structure KeyFits (w : ℕ) (x : Expanded.Key) : Prop where
  primary : PrimaryFits w (ofLex x).1
  first : (ofLex (ofLex x).2).1.size ≤ w
  second : (ofLex (ofLex (ofLex x).2).2).1.size ≤ w
  record : (ofLex (ofLex (ofLex x).2).2).2.size ≤ w

theorem keyLess_work (x y : Expanded.Key) {w : ℕ} (hx : KeyFits w x) (hy : KeyFits w y) :
    (keyLess x y).Bound 17 (TrialWork.scalarWidth w) := by
  let W := TrialWork.scalarWidth w
  have one : 1 ≤ W := by unfold W TrialWork.scalarWidth; omega
  have more : w ≤ W := by unfold W TrialWork.scalarWidth; omega
  have l (x y : ℕ) (hx : x.size ≤ w) (hy : y.size ≤ w) : (natLess x y).Bound 1 W :=
    (bound_step _ _).weaken le_rfl ((max_le hx hy).trans more)
  have eq (x y : ℕ) (hx : x.size ≤ w) (hy : y.size ≤ w) : (natEqual x y).Bound 1 W :=
    (bound_step _ _).weaken le_rfl ((max_le hx hy).trans more)
  exact lex_work one (nullableLess_work _ _ hx.primary hy.primary) (nullableEqual_work _ _ hx.primary hy.primary)
    (lex_work one (l _ _ hx.first hy.first) (eq _ _ hx.first hy.first)
      (lex_work one (l _ _ hx.second hy.second) (eq _ _ hx.second hy.second) (l _ _ hx.record hy.record)))

theorem inputKey_fits (a : Input) (valid : a.Valid)
    (v : Expanded.V (Fin a.types) (Fin a.targets) (grid a.game))
    (e : Expanded.R (Fin a.types) (Fin a.targets) (grid a.game)) :
    KeyFits (ContactCharge.operandWidth (Binary.lengthInput a)) (Expanded.key a.game Fin.val Fin.val v e) := by
  obtain ⟨p,f,s,r⟩ := ContactCharge.preference_words a valid v e
  exact ⟨p,f,s,r⟩

end Kintali.QuotaSweep.RankRun
