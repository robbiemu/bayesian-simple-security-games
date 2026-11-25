module

public import Kintali.QuotaSweep.ExpandedIdentifier
public import Kintali.QuotaSweep.RankedContact
public import Kintali.InputOutput.NormalizedFields

/-! # Computing sparse ordinal fields from stored coordinates and normalized game data -/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open Kintali.ExactRecovery Kintali.ContactSize Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch
open StochasticGames.CompilerRun StochasticGames.BinarySize

def scaleIndex (n : ℕ) : Run ℚ := step n.size (n : ℚ)

def quote {k m G : ℕ} (d : TrialWork.Fields k m) (i : Fin k) (j : Fin m) (z : Quote G) : Run (WithTop ℚ) := do
  let num ← scaleIndex z.val
  let den ← scaleIndex G
  let x ← TrialWork.divide num den
  let result ← d.costAt i j x
  step 0 (result : WithTop ℚ)

@[simp] theorem quote_value {k m G : ℕ} (d : TrialWork.Fields k m) (i j) (z : Quote G) :
    (quote d i j z).value = (Holdings.quoteCost d.game i j z : WithTop ℚ) := by
  simp [quote,scaleIndex,Holdings.quoteCost,price]

def quoteSlots (c w : ℕ) := 2+(4+TrialWork.scalarSlots w)+(TrialWork.costSlots c (2*w)+1)

theorem quote_work {k m G : ℕ} (d : TrialWork.Fields k m) {c w : ℕ} (fields : TrialWork.FieldBound d c (2*w))
    (grid : G.size+1 ≤ w) (i j) (z : Quote G) :
    (quote d i j z).Bound (quoteSlots c w) (TrialWork.costWidth (2*w)) := by
  let W := TrialWork.costWidth (2*w)
  have w₁ : w ≤ W := by unfold W TrialWork.costWidth TrialWork.scalarWidth; omega
  have w₂ : TrialWork.scalarWidth w ≤ W := by unfold W TrialWork.costWidth TrialWork.scalarWidth; omega
  have nz := (Nat.size_le_size (Nat.le_of_lt_succ z.isLt)).trans (show G.size ≤ w by omega)
  have iz : Fits w (z.val : ℚ) := (Fits.natCast _).mono
    ((Nat.succ_le_succ (Nat.size_le_size (Nat.le_of_lt_succ z.isLt))).trans grid)
  have ig : Fits w (G : ℚ) := (Fits.natCast _).mono grid
  have t := TrialWork.divide_work iz ig
  have p := (iz.div ig).mono (show w+w ≤ 2*w by omega)
  have cost := d.costAt_work fields i j p
  unfold quote
  exact (bound_bind ((bound_step _ _).weaken le_rfl (nz.trans w₁))
    (bound_bind ((bound_step _ _).weaken le_rfl ((show G.size ≤ w by omega).trans w₁))
      (bound_bind (t.weaken le_rfl w₂) (by
        rw [TrialWork.divide_value]
        exact bound_bind cost ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))))).weaken
    (by unfold quoteSlots; omega) le_rfl

def level (n offset : ℕ) : Run (WithTop ℚ) := do
  let a ← natMul 2 n
  let b ← natAdd a offset
  step (b.size+1) ((-(b : ℚ) : ℚ) : WithTop ℚ)

@[simp] theorem level_value (n k : ℕ) :
    (level n k).value = ((-((2*n+k : ℕ) : ℚ) : ℚ) : WithTop ℚ) := rfl

theorem level_work (n offset : ℕ) {w : ℕ} (hn : n.size ≤ w) (ho : offset ≤ 1) :
    (level n offset).Bound 3 (TrialWork.costWidth (2*w)) := by
  have one : (1:ℕ).size = 1 := by decide
  have two : (2:ℕ).size = 2 := by decide
  have b : (2*n+offset).size ≤ w+1 := by
    apply Nat.size_le.mpr
    have := Nat.size_le.mp hn; rw [pow_succ]; omega
  have a := (Nat.size_le_size (Nat.le_add_right (2*n) offset)).trans b
  have o := (Nat.size_le_size ho).trans_eq one
  simp only [level,Run.Bound,Run.bind_slots,Run.bind_width,natMul,natAdd,step_slots,step_width,
    step_value,TrialWork.costWidth,TrialWork.scalarWidth]
  omega

def primary {k m G : ℕ} (d : TrialWork.Fields k m) (v : Expanded.V (Fin k) (Fin m) G) :
    Expanded.R (Fin k) (Fin m) G → Run (WithTop ℚ)
  | .inr _ => step 0 ⊤
  | .inl (.inl (i,j,z)) =>
    match v with
    | .inl _ => quote d i j z
    | .inr _ => level z.val 0
  | .inl (.inr (_,z)) =>
    match v with
    | .inl _ => step 0 (0 : ℚ)
    | .inr _ => level z.val 1

@[simp] theorem primary_value {k m G : ℕ} (d : TrialWork.Fields k m)
    (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) :
    (primary d v e).value = Expanded.primary d.game v e := by
  rcases e with (⟨i,j,z⟩|⟨j,z⟩)|s <;> cases v <;> simp [primary,Expanded.primary]

theorem primary_work {k m G : ℕ} (d : TrialWork.Fields k m) {c w : ℕ} (fields : TrialWork.FieldBound d c (2*w))
    (grid : G.size+1 ≤ w) (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) :
    (primary d v e).Bound (quoteSlots c w) (TrialWork.costWidth (2*w)) := by
  have three : 3 ≤ quoteSlots c w := by unfold quoteSlots; omega
  rcases e with (⟨i,j,z⟩|⟨j,z⟩)|s <;> cases v
  · exact quote_work d fields grid ..
  · exact (level_work _ 0 ((Nat.size_le_size (Nat.le_of_lt_succ z.isLt)).trans (by omega)) (by decide)).weaken three le_rfl
  · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
  · exact (level_work _ 1 ((Nat.size_le_size z.isLt.le).trans (by omega)) (by decide)).weaken three le_rfl
  · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
  · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)

def keyAt {k m G : ℕ} (d : TrialWork.Fields k m)
    (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) : Run Expanded.Key := do
  let input ← step 0 (v,e)
  let p ← primary d input.1 input.2
  let t ← step 0 (Expanded.tie Fin.val Fin.val input.1 input.2)
  let code ← StoredLookup.expandedKey input.2
  step 0 (toLex (p,toLex (t.1,toLex (t.2,code))))

@[simp] theorem keyAt_value {k m G : ℕ} (d : TrialWork.Fields k m)
    (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) :
    (keyAt d v e).value = Expanded.key d.game Fin.val Fin.val v e := by
  simp [keyAt,Expanded.key,StoredLookup.expandedKey_value]

theorem keyAt_work {k m G w c : ℕ} (d : TrialWork.Fields k m) (fields : TrialWork.FieldBound d c (2*w))
    (hk : k.size ≤ w) (hm : m.size ≤ w) (grid : G.size+1 ≤ w) (gridSucc : (G+1).size ≤ w)
    (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) :
    (keyAt d v e).Bound (quoteSlots c w+18) (TrialWork.costWidth (2*w)+10) := by
  let W := TrialWork.costWidth (2*w)+10
  have wid : 4*w+10 ≤ W := by unfold W TrialWork.costWidth TrialWork.scalarWidth; omega
  have baseCost := (primary_work d fields grid v e).weaken le_rfl (Nat.le_add_right (TrialWork.costWidth (2*w)) 10)
  have code := ((StoredLookup.expandedKey_bound hk hm (show G.size ≤ w by omega) gridSucc).work e).weaken le_rfl wid
  have h : (keyAt d v e).Bound (1+(quoteSlots c w+(1+(15+1)))) W :=
    bound_bind ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)) (bound_bind baseCost
      (bound_bind ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))
        (bound_bind code ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))))
  exact h.weaken (by omega) le_rfl

end Kintali.QuotaSweep.RankRun
