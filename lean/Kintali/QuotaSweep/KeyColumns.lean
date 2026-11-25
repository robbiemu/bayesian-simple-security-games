module

public import Kintali.QuotaSweep.KeyEvaluation

/-! # Sparse ordinal construction from the two materialized coordinate columns -/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open Kintali.ExactRecovery Kintali.ContactSize Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch
open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

/-- The real column is indexed by the retained-bid order. The private column
has one row per site and one representative gap per consecutive interval. -/
structure Columns (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) where
  reals : Vector (Sparse.ListedBid a.types a.targets (grid a.game))
    (Sparse.realOrder (G := grid a.game) a.game toSite s).length
  groups : Vector (Array (Fin (grid a.game))) a.targets
  rowLength : ∀ j : Fin a.targets, groups[j.val].size =
    (Sparse.partition (G := grid a.game) a.game toSite s j).groups

namespace Columns

variable (c : Columns a toSite s)

def gap (h : StoredLookup.SelectedGroups a toSite s) : Fin (grid a.game) :=
  c.groups[h.1.val][h.2.val]'(by rw [c.rowLength]; exact h.2.isLt)

def vertex : SelectedVertex a toSite s → Run (Expanded.V (Fin a.types) (Fin a.targets) (grid a.game))
  | .inl (.inl i) => step 0 (.inl (.inl i))
  | .inr j => step 0 (.inr j)
  | .inl (.inr h) =>
    let row := step h.1.val.size c.groups[h.1.val]
    let z := step h.2.val.size (row.value[h.2.val]'((c.rowLength h.1).symm ▸ h.2.isLt))
    ⟨.inl (.inr (h.1,z.value)),row.work.seq (z.work.seq (StochasticGames.CompilerRun.Work.one 0))⟩

def record : StoredLookup.SelectedRecord a toSite s → Run (Expanded.R (Fin a.types) (Fin a.targets) (grid a.game))
  | .inl (.inl i) => do
    let b ← step i.val.size c.reals[i.val]
    step 0 (.inl (.inl b))
  | .inl (.inr h) =>
    let row := step h.1.val.size c.groups[h.1.val]
    let z := step h.2.val.size (row.value[h.2.val]'((c.rowLength h.1).symm ▸ h.2.isLt))
    ⟨.inl (.inr (h.1,z.value)),row.work.seq (z.work.seq (StochasticGames.CompilerRun.Work.one 0))⟩
  | .inr v => do
    let u ← c.vertex v
    step 0 (.inr u)

def Correct :=
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  (∀ i : StoredLookup.SelectedReals a toSite s, c.reals[i.val] = l.real i) ∧
    ∀ h : StoredLookup.SelectedGroups a toSite s, (h.1,c.gap h) = l.representative h

theorem vertex_value (correct : c.Correct) (v : SelectedVertex a toSite s) :
    (c.vertex v).value =
      (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored.embedVertex v := by
  rcases v with (i|h)|j
  · rfl
  · exact congrArg (fun p => Sum.inl (Sum.inr p)) (correct.2 h)
  · rfl

theorem record_value (correct : c.Correct) (e : StoredLookup.SelectedRecord a toSite s) :
    (c.record e).value =
      (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored.embedRecord e := by
  rcases e with (i|h)|v
  · exact congrArg (fun p => Sum.inl (Sum.inl p)) (correct.1 i)
  · exact congrArg (fun p => Sum.inl (Sum.inr p)) (correct.2 h)
  · exact congrArg Sum.inr (c.vertex_value correct v)

end Columns

/-- Exact mathematical columns corresponding to the selected-layout builder. -/
def canonicalColumns (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :
    Columns a toSite s :=
  let l := Sparse.selectedLayout (G := grid a.game) a.game toSite s
  let D := Sparse.partition (G := grid a.game) a.game toSite s
  { reals := Vector.ofFn l.real
    groups := Vector.ofFn (fun j => Array.ofFn (fun h : Fin (D j).groups => (l.representative ⟨j,h⟩).2))
    rowLength := by simp [D] }

theorem canonicalColumns_correct (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :
    (canonicalColumns a toSite s).Correct := by
  constructor
  · intro i; simp [canonicalColumns]
  · rintro ⟨j,h⟩; simp [canonicalColumns,Columns.gap]; rfl

theorem public_keyBits (a : Input) (valid : a.Valid) :
    let L := Binary.lengthInput a
    let b := Binary.gridBitBound L+L+2
    a.types.size ≤ b ∧ a.targets.size ≤ b ∧ (grid a.game).size+1 ≤ b ∧ ((grid a.game)+1).size ≤ b := by
  let g := grid a.game
  let L := Binary.lengthInput a
  have grid := Binary.grid_size a valid
  have h₁ := (size_le_self _).trans (Binary.dimensions a).2.1
  have h₂ := (size_le_self _).trans (Binary.dimensions a).1
  have succ : (g+1).size ≤ g.size+1 := by
    apply Nat.size_le.mpr; rw [pow_succ]
    have := Nat.lt_size_self g
    omega
  dsimp only
  dsimp [g] at succ
  omega

theorem column_indices (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (hs : SelectionBound a s) :
    let L := Binary.lengthInput a
    let W := ContactCharge.width L
    (∀ i : StoredLookup.SelectedReals a toSite s, i.val.size ≤ W) ∧
    (∀ h : StoredLookup.SelectedGroups a toSite s, h.1.val.size ≤ W ∧ h.2.val.size ≤ W) := by
  let L := Binary.lengthInput a
  let D := Sparse.partition (G := grid a.game) a.game toSite s
  obtain ⟨reals,groups,_,_⟩ := selected_inventory a toSite s hs
  have fit : recordLimit L+L ≤ ContactCharge.width L := by
    unfold ContactCharge.width ContactCharge.operandWidth TrialWork.scalarWidth; omega
  have rc : (Sparse.realOrder (G := grid a.game) a.game toSite s).length ≤ recordLimit L := by
    simpa only [Fintype.card_fin] using reals
  refine ⟨fun i => (size_le_self _).trans (i.isLt.le.trans (rc.trans ((Nat.le_add_right ..).trans fit))),?_⟩
  intro h
  have inj : Function.Injective (fun t : Fin (D h.1).groups =>
      (⟨h.1,t⟩ : StoredLookup.SelectedGroups a toSite s)) := by
    intro b c same; exact eq_of_heq (Sigma.mk.inj same).2
  have gc := Fintype.card_le_of_injective _ inj
  simp only [Fintype.card_fin] at gc
  exact ⟨(size_le_self _).trans (h.1.isLt.le.trans ((Binary.dimensions a).1.trans ((Nat.le_add_left ..).trans fit))),
    (size_le_self _).trans (h.2.isLt.le.trans (gc.trans (groups.trans ((Nat.le_add_right ..).trans fit))))⟩

theorem Columns.access_work (c : Columns a toSite s) (hs : SelectionBound a s) :
    let W := ContactCharge.width (Binary.lengthInput a)
    (∀ v, (c.vertex v).Bound 3 W) ∧ (∀ e, (c.record e).Bound 4 W) := by
  obtain ⟨real,group⟩ := column_indices a toSite s hs
  have weak : 0 ≤ ContactCharge.width (Binary.lengthInput a) := Nat.zero_le _
  have vertices (v) : (c.vertex v).Bound 3 (ContactCharge.width (Binary.lengthInput a)) := by
    rcases v with (i|h)|j
    · exact (bound_step 0 _).weaken (by decide) weak
    · exact ⟨le_rfl,max_le (group h).1 (max_le (group h).2 weak)⟩
    · exact (bound_step 0 _).weaken (by decide) weak
  refine ⟨vertices,?_⟩
  rintro ((i|h)|v)
  · exact (bound_bind ((bound_step _ _).weaken le_rfl (real i))
      ((bound_step 0 _).weaken le_rfl weak)).weaken (by decide) le_rfl
  · exact ⟨by change 3 ≤ 4; decide,max_le (group h).1 (max_le (group h).2 weak)⟩
  · exact bound_bind (vertices v) ((bound_step 0 _).weaken le_rfl weak)

def Columns.make (c : Columns a toSite s) (fields : TrialWork.Fields a.types a.targets)
    (v : SelectedVertex a toSite s) (e : StoredLookup.SelectedRecord a toSite s) : Run Expanded.Key := do
  let i ← c.vertex v
  let j ← c.record e
  keyAt fields i j

theorem Columns.make_correct (c : Columns a toSite s) (ok : c.Correct) (t : NormalizedWork.Tables a.types a.targets)
    (actual : t.game = a.game) : KeysCorrect a toSite s (c.make t.fields) := by
  intro v e
  simp only [Columns.make,Run.bind_value,keyAt_value,NormalizedWork.Tables.fields_game,actual,
    c.vertex_value ok,c.record_value ok]

def keySlots (L : ℕ) := quoteSlots 2 (Binary.gridBitBound L+L+2)+25

theorem Columns.make_work (c : Columns a toSite s) (valid : a.Valid) (hs : SelectionBound a s)
    (t : NormalizedWork.Tables a.types a.targets) (actual : t.game = a.game)
    (v : SelectedVertex a toSite s) (e : StoredLookup.SelectedRecord a toSite s) :
    (c.make t.fields v e).Bound (keySlots (Binary.lengthInput a)) (ContactCharge.width (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  let b := Binary.gridBitBound L+L+2
  obtain ⟨ht,hm,hg,hg'⟩ := public_keyBits a valid
  have fit : 2*L+1 ≤ 2*b := by unfold b; omega
  have data := (NormalizedWork.fields_bound a valid t actual).mono fit
  have cost := keyAt_work t.fields data ht hm hg hg' (c.vertex v).value (c.record e).value
  have bigger : TrialWork.costWidth (2*b)+10 ≤ ContactCharge.width L := by
    unfold TrialWork.costWidth TrialWork.scalarWidth ContactCharge.width ContactCharge.operandWidth b
    dsimp only [TrialWork.scalarWidth]; omega
  obtain ⟨vs,es⟩ := c.access_work hs
  exact (bound_bind (vs v) (bound_bind (es e) (cost.weaken le_rfl bigger))).weaken
    (by unfold keySlots; change 3+(4+(quoteSlots 2 b+18)) ≤ quoteSlots 2 b+25; omega) le_rfl

/-- Invoke the arithmetic on the grid number stored by initialization.
The dependent types are reindexed by a proof that erases from execution. -/
@[noinline] def keyAtGrid {k m G : ℕ} (N : ℕ) (same : N = G) (d : TrialWork.Fields k m)
    (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) : Run Expanded.Key :=
  @keyAt k m N d (same.symm ▸ v) (same.symm ▸ e)

@[simp] theorem keyAtGrid_eq {k m G : ℕ} (N : ℕ) (same : N=G) (d : TrialWork.Fields k m)
    (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) :
    keyAtGrid N same d v e = keyAt d v e := by subst G; rfl

def Columns.makeAt (c : Columns a toSite s) (N : ℕ) (same : N = grid a.game)
    (d : TrialWork.Fields a.types a.targets) (v : SelectedVertex a toSite s) (e : StoredLookup.SelectedRecord a toSite s) :
    Run Expanded.Key := do
  let i ← c.vertex v
  let j ← c.record e
  keyAtGrid N same d i j

@[simp] theorem Columns.makeAt_eq (c : Columns a toSite s) (N : ℕ) (same : N = grid a.game)
    (d : TrialWork.Fields a.types a.targets) : c.makeAt N same d = c.make d := by
  funext v e
  simp [makeAt,make]

end Kintali.QuotaSweep.RankRun
