module

public import Kintali.InputOutput.PlanWork
public import Kintali.InputOutput.StrategyWork
public import Kintali.TrialWork.SelectedExecute
public import Kintali.TrialWork.BuiltInventory

/-! # Connect the selected inventory and trial to the outer search

The remaining contact parameter reads the prepared sparse market and returns
the stored quota-sweep allocation. Its contract states the actual value
and addressed work at this interface.
-/

@[expose] public section

namespace Kintali.InputOutput.InventorySearch

open StochasticGames.CompilerRun
open LinearProgramming.ArithmeticRun
open ExactRecovery QuotaSweep QuoteSearch TrialWork MarketTrial ContactSize

abbrev Contact (a : Input) (st : InitializationWork.State a.types a.targets) :=
  (s : Selection (a.types*a.targets)) → Selected.Lists a (Selected.route st) s →
    Run (StoredLookup.SelectedStored a (Selected.route st) s)

def Contact.Value (a : Input) (st : InitializationWork.State a.types a.targets) (contact : Contact a st) : Prop :=
  ∀ s l, (contact s l).value = (Sparse.selectedRun (G := grid a.game) a.game
    (Selected.route st) s (privateScale a.game)).1

def trial (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (contact : Contact a st)
    (s : Selection (a.types*a.targets)) : Run (Reply (a.types*a.targets) (Strategy a.types a.targets)) := do
  let inventory ← Inventory.build a hm st correct s
  Selected.trialWith a hm st correct s inventory (contact s inventory)

theorem trial_value (a : Input) (hm : 0 < a.targets) (st : InitializationWork.State a.types a.targets)
    (correct : InitializationWork.Correct a hm st) (contact : Contact a st)
    (eq : Contact.Value a st contact) (s : Selection (a.types*a.targets)) :
    (trial a hm st correct contact s).value = MarketTrial.run a.game hm (sparseView a.game hm) s := by
  unfold trial
  rw [Run.bind_value]
  exact Selected.trialWith_value a hm st correct s _ _ (eq s _)

def trialSlots (L C : ℕ) := Inventory.slots L + C + Selected.afterSlots L
def trialWidth (L W : ℕ) := Inventory.width L + W + Selected.afterWidth L

theorem trial_work (a : Input) (v : a.Valid) (normal : ¬a.game.DirectCase)
    (st : InitializationWork.State a.types a.targets) (correct : InitializationWork.Correct a v.1 st)
    (contact : Contact a st) (eq : Contact.Value a st contact) (s : Selection (a.types*a.targets))
    (hs : ValidSelection (4*witnessBound a.game) (eligible a.game v.1) s)
    {C W : ℕ} (cw : ∀ l, (contact s l).Bound C W) :
    (trial a v.1 st correct contact s).Bound (trialSlots (Binary.lengthInput a) C)
      (trialWidth (Binary.lengthInput a) W) := by
  let L := Binary.lengthInput a
  let inv := Inventory.build a v.1 st correct s
  have ib := Inventory.build_work a v st correct s hs
  have hSample : SelectionBound a s := by
    intro j
    have h := (hs.count j).trans (Nat.sub_le _ _)
    have hh := Nat.mul_le_mul_left 4 (Binary.witness_bound a)
    unfold sampleLimit Binary.witnesses at *
    omega
  have bw := Selected.trialWith_work a v normal st correct s hSample inv.value
    (contact s inv.value) (eq s inv.value) (cw inv.value)
  have sa : Inventory.width L ≤ trialWidth L W := by unfold trialWidth; omega
  have sb : max W (Selected.afterWidth L) ≤ trialWidth L W := by
    rw [max_le_iff]
    unfold trialWidth
    omega
  constructor
  · change inv.work.slots + (Selected.trialWith a v.1 st correct s inv.value
      (contact s inv.value)).work.slots ≤ trialSlots L C
    change _ ≤ (Inventory.slots L+C)+Selected.afterSlots L
    rw [Nat.add_assoc]
    exact Nat.add_le_add ib.1 bw.1
  · exact max_le (ib.2.trans sa) (bw.2.trans sb)

/-- Strategies returned by the successful trial use vector-backed accessors. -/
def emit {k m : ℕ} (s : Strategy k m) : Run Output := do
  let x ← tabulate m fun j => step m.size (s.coverage j)
  let q ← tabulate k fun i => tabulate m fun j => ⟨s.attacks i j, ⟨2,k.size+m.size⟩⟩
  StrategyWork.run x q

@[simp] theorem emit_value {k m : ℕ} (s : Strategy k m) : (emit s).value = writeStrategy s := by
  simp only [emit, Run.bind_value, tabulate_value, StrategyWork.run_value, step_value, Vector.getElem_ofFn]

def emitSlots (L : ℕ) := 3*(L+1)+L + (3*(L+1)+L*(3*(L+1)+2*L)) + StrategyWork.slots L

theorem emit_work {k m L : ℕ} (s : Strategy k m) (kl : k ≤ L) (ml : m ≤ L) :
    (emit s).Bound (emitSlots L) (2*L) := by
  have kb := (StochasticGames.BinarySize.size_le_self _).trans kl
  have mb := (StochasticGames.BinarySize.size_le_self _).trans ml
  let x := tabulate m fun j => step m.size (s.coverage j)
  let q := tabulate k fun i => tabulate m fun j => (⟨s.attacks i j, ⟨2,k.size+m.size⟩⟩ : Run ℚ)
  have bits : k.size+m.size ≤ 2*L := by omega
  have mfit : m.size ≤ 2*L := by omega
  have kfit : k.size ≤ 2*L := by omega
  have cov := tabulate_bound (fun j : Fin m => step m.size (s.coverage j)) mfit
    (fun _ => ⟨le_rfl,mfit⟩)
  have each (i : Fin k) := tabulate_bound
    (fun j : Fin m => (⟨s.attacks i j,⟨2,k.size+m.size⟩⟩ : Run ℚ)) mfit (fun _ => ⟨le_rfl,bits⟩)
  have attacks := tabulate_bound _ kfit each
  have write := StrategyWork.run_work x.value q.value kl ml
  have c := cov.1.trans (show 3*(m+1)+m*1 ≤ 3*(L+1)+L by simp; omega)
  have d := attacks.1.trans (show 3*(k+1)+k*(3*(m+1)+m*2) ≤ 3*(L+1)+L*(3*(L+1)+2*L) by
    rw [Nat.mul_comm m 2]
    gcongr)
  constructor
  · change x.work.slots + (q.work.slots + (StrategyWork.run x.value q.value).work.slots) ≤ _
    change x.work.slots ≤ _ at c
    change q.work.slots ≤ _ at d
    unfold emitSlots
    rw [Nat.add_assoc]
    exact Nat.add_le_add c (Nat.add_le_add d write.1)
  · exact max_le cov.2 (max_le attacks.2 (write.2.trans (by omega)))

end Kintali.InputOutput.InventorySearch
