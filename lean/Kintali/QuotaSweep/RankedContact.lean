module

public import Kintali.QuotaSweep.RankConstruction

/-! # Composing the addressed ordinal constructor and the stored quota sweep -/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open StochasticGames.CompilerRun

variable {B S E : Type} [DecidableEq B] [DecidableEq S] [DecidableEq E]

def attach (K : Book B S E) (t : Run (Book.RankTable B S E)) (ok : t.value = K.rankTable) : Run (Book B S E) :=
  let b := K.withRanks t.value (by rw [ok]; exact K.readRanks_eq)
  ⟨b,t.work.seq (StochasticGames.CompilerRun.Work.one 0)⟩

theorem attach_value (K : Book B S E) (t : Run (Book.RankTable B S E)) (ok : t.value = K.rankTable) :
    (attach K t ok).value = K := by
  obtain ⟨table,cost⟩ := t
  change table = K.rankTable at ok
  subst table
  exact K.cacheRanks_eq

theorem attach_work (K : Book B S E) (t : Run (Book.RankTable B S E)) (ok : t.value = K.rankTable)
    {c w : ℕ} (h : t.Bound c w) : (attach K t ok).Bound (c+1) w := by
  exact ⟨Nat.add_le_add_right h.1 1,max_le h.2 (Nat.zero_le _)⟩

def selectedBook (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (make) (correct : KeysCorrect a toSite s make) :=
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  let K := Sparse.book a.game Fin.val Fin.val l
  let t := selectedTable a toSite s make
  attach K t ((selectedTable_value a toSite s make correct).trans (Sparse.keyedTable_eq ..))

theorem selectedBook_value (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (make) (correct : KeysCorrect a toSite s make) :
    (selectedBook a toSite s make correct).value =
      Sparse.book a.game Fin.val Fin.val ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored) :=
  attach_value _ _ ((selectedTable_value a toSite s make correct).trans (Sparse.keyedTable_eq ..))

def selectedContact (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (make) (correct : KeysCorrect a toSite s make) : Run (StoredLookup.SelectedStored a toSite s) := do
  let K ← selectedBook a toSite s make correct
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  let P := BudgetContact.parameters a.game (privateScale a.game) (fun h => (l.representative h).1)
      (fun h => Sparse.mass a.game (privateScale a.game) l (.inr h))
  ContactCharge.prepared K P (ContactCharge.operandWidth (Binary.lengthInput a))

theorem selectedContact_value (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (make) (correct : KeysCorrect a toSite s make) :
    (selectedContact a toSite s make correct).value =
      (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).1 := by
  simp [selectedContact,selectedBook_value,ContactCharge.prepared_value,Sparse.selectedRun,Book.indexedContact_eq]

def contactSlots (L k : ℕ) := inputSlots L k+1+ContactCharge.slots L

theorem selectedContact_work (a : Input) (valid : a.Valid) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) (make) (correct : KeysCorrect a toSite s make)
    {k : ℕ} (charged : ∀ v e, (make v e).Bound k (ContactCharge.width (Binary.lengthInput a))) :
    (selectedContact a toSite s make correct).Bound (contactSlots (Binary.lengthInput a) k)
      (ContactCharge.width (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  let K := Sparse.book a.game Fin.val Fin.val l
  let P := BudgetContact.parameters a.game (privateScale a.game) (fun h => (l.representative h).1)
      (fun h => Sparse.mass a.game (privateScale a.game) l (.inr h))
  have table := selectedTable_work a valid toSite s hs make correct charged
  have attach : (selectedBook a toSite s make correct).Bound (inputSlots L k+1) (ContactCharge.width L) :=
    attach_work _ _ ((selectedTable_value a toSite s make correct).trans (Sparse.keyedTable_eq ..)) table
  have size : K.records.length ≤ recordLimit L := by
    simp only [K,l,Sparse.Layout.stored_eq]
    exact (selected_inventory a toSite s hs).2.2.2
  have contact : (ContactCharge.prepared K P (ContactCharge.operandWidth L)).Bound
      (ContactCharge.slots L) (ContactCharge.width L) :=
    (ContactCharge.prepared_work K P _).weaken
      (by unfold ContactCharge.slots OperandBounds.inputSlots; gcongr) le_rfl
  apply bound_bind attach
  rw [selectedBook_value]
  exact contact

theorem selectedContact_binary (a : Input) (valid : a.Valid) (toSite : Fin a.types → Fin a.targets)
    (s : Selection (a.types*a.targets)) (hs : SelectionBound a s) (make) (correct : KeysCorrect a toSite s make)
    {k : ℕ} (charged : ∀ v e, (make v e).Bound k (ContactCharge.width (Binary.lengthInput a))) :
    let L := Binary.lengthInput a
    LinearProgramming.RecoveryRun.binaryWork L (selectedContact a toSite s make correct).work ≤
      CodecWork.binaryLimit L (contactSlots L k) (ContactCharge.width L) :=
  CodecWork.addressed_bound _ (selectedContact_work a valid toSite s hs make correct charged)

end Kintali.QuotaSweep.RankRun
