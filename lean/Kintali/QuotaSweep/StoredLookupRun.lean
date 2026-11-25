module

public import Kintali.QuotaSweep.EncodedKeyRun
public import Kintali.ContactSize.Prefix

/-! # Addressed lookups in the stored contact used by projection and tests -/

@[expose] public section
namespace Kintali.QuotaSweep.StoredLookup

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {T U : Type}

def scan (key : T → Run ℕ) (code : ℕ) (fallback : U) : List (T × U) → Run U
  | [] => step 0 fallback
  | item :: rest => do
    let cell ← step 0 item
    let id ← key cell.1
    let yes ← step (max code.size id.size) (decide (code=id))
    if yes then step 0 cell.2 else scan key code fallback rest

def read (key : T → Run ℕ) (needle : T) (fallback : U) (table : List (T × U)) : Run U := do
  let code ← key needle
  scan key code fallback table

theorem scan_value [Encodable T] (key : T → Run ℕ) (correct : ∀ i, (key i).value = Encodable.encode i)
    (needle : T) (fallback : U) (xs : List (T × U)) :
    (scan key (Encodable.encode needle) fallback xs).value =
      (@Kintali.QuotaSweep.Work.search T U Book.encodedEq needle fallback xs).1 := by
  induction xs with
  | nil => rfl
  | cons item rest ih =>
    obtain ⟨i,v⟩ := item
    by_cases hv : needle = i
    · subst i; simp [scan,correct,Kintali.QuotaSweep.Work.search]
    · have hc : Encodable.encode needle ≠ Encodable.encode i := fun e => hv (Encodable.encode_injective e)
      simp [scan,correct,Kintali.QuotaSweep.Work.search,hc,hv,ih]

theorem read_value [Encodable T] (key : T → Run ℕ) (correct : ∀ i, (key i).value = Encodable.encode i)
    (needle : T) (fallback : U) (xs : List (T × U)) :
    (read key needle fallback xs).value =
      (@Kintali.QuotaSweep.Work.search T U Book.encodedEq needle fallback xs).1 := by
  simpa only [read,Run.bind_value,correct] using scan_value key correct needle fallback xs

theorem scan_bound (key : T → Run ℕ) {c w : ℕ} (bounds : KeyBound key c w)
    (code : ℕ) (fits : code.size ≤ w) (fallback : U) (xs : List (T × U)) :
    (scan key code fallback xs).Bound (1+xs.length*(c+3)) w := by
  induction xs with
  | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
  | cons cell rest ih =>
    have slot := bounds.work cell.1
    have size := bounds.size cell.1
    have tail : (if code = (key cell.1).value then step 0 cell.2 else scan key code fallback rest).Bound
        (1+rest.length*(c+3)) w := by
      split
      · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
      · exact ih
    simp only [scan,Run.Bound,Run.bind_slots,Run.bind_width,step_value,step_slots,step_width,
      decide_eq_true_eq,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    omega

theorem read_bound (key : T → Run ℕ) {c w : ℕ} (bounds : KeyBound key c w)
    (needle : T) (fallback : U) (table : List (T × U)) :
    (read key needle fallback table).Bound (c+(1+table.length*(c+3))) w :=
  bound_bind (bounds.work needle) (scan_bound key bounds _ (bounds.size needle) fallback table)

abbrev SelectedGroups (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :=
  Sparse.IntervalGroup (Sparse.partition (G := grid a.game) a.game toSite s)

abbrev SelectedReals (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :=
  Fin (Sparse.realOrder (G := grid a.game) a.game toSite s).length

abbrev SelectedStored (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :=
  Book.Stored (Sparse.B (Fin a.types) (SelectedGroups a toSite s)) (Fin a.targets)
    (Sparse.E (SelectedReals a toSite s) (SelectedGroups a toSite s))

abbrev SelectedRecord (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) :=
  Sparse.R (Fin a.types) (Fin a.targets) (SelectedReals a toSite s) (SelectedGroups a toSite s)

def selected (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (z : SelectedStored a toSite s) (e : SelectedRecord a toSite s) : Run ℚ :=
  read (recordKey (Sparse.partition (G := grid a.game) a.game toSite s)) e 0 z.entries

theorem selected_value (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (z : SelectedStored a toSite s) (e : SelectedRecord a toSite s) :
    (selected a toSite s z e).value = (z.encodedRead e).1 :=
  read_value _ (recordKey_value _) e 0 z.entries

def slots (r : ℕ) := 13+r*15
def width (L : ℕ) := 2*(recordLimit L+L)+8

theorem selected_key_bound (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (hs : SelectionBound a s) :
    let D := Sparse.partition (G := grid a.game) a.game toSite s
    KeyBound (recordKey (k := a.types) (a := (Sparse.realOrder (G := grid a.game) a.game toSite s).length) D)
      12 (width (Binary.lengthInput a)) := by
  let L := Binary.lengthInput a
  let D := Sparse.partition (G := grid a.game) a.game toSite s
  let H := SelectedGroups a toSite s
  obtain ⟨real,groups,_,_⟩ := selected_inventory a toSite s hs
  have dims := Binary.dimensions a
  have hsizes (j : Fin a.targets) : (D j).groups ≤ recordLimit L := by
    have inj : Function.Injective (fun h : Fin (D j).groups => (⟨j,h⟩ : H)) := by
      intro x y same
      exact eq_of_heq (Sigma.mk.inj same).2
    have count := Fintype.card_le_of_injective _ inj
    exact (by simpa only [Fintype.card_fin] using count : (D j).groups ≤ Fintype.card H).trans groups
  have nr : (Sparse.realOrder (G := grid a.game) a.game toSite s).length ≤ recordLimit L := by
    simpa only [Fintype.card_fin] using real
  apply recordKey_bound
  · exact (size_le_self _).trans (dims.2.1.trans (Nat.le_add_left ..))
  · exact (size_le_self _).trans (dims.1.trans (Nat.le_add_left ..))
  · exact (size_le_self _).trans (nr.trans (Nat.le_add_right ..))
  · exact fun j => (size_le_self _).trans ((hsizes j).trans (Nat.le_add_right ..))

theorem selected_work (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (hs : SelectionBound a s) (z : SelectedStored a toSite s) {r : ℕ} (len : z.entries.length ≤ r)
    (e : SelectedRecord a toSite s) : (selected a toSite s z e).Bound (slots r) (width (Binary.lengthInput a)) := by
  have h := read_bound _ (selected_key_bound a toSite s hs) e (0 : ℚ) z.entries
  exact h.weaken (by unfold slots; omega) le_rfl

theorem contact_read_work (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (hs : SelectionBound a s) (e : SelectedRecord a toSite s) :
    let z := (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).1
    (selected a toSite s z e).Bound (slots (recordLimit (Binary.lengthInput a))) (width (Binary.lengthInput a)) :=
  selected_work a toSite s hs _ ((Sparse.selectedRun_length ..).le.trans (selected_inventory a toSite s hs).2.2.2) e

end Kintali.QuotaSweep.StoredLookup
