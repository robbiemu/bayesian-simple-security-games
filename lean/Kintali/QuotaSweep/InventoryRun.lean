module

public import Kintali.QuotaSweep.KeyColumns
public import Kintali.QuotaSweep.RuntimeRanks

/-!
# Restricted contact from a supplied sparse inventory

The stored input comprises normalized payoff vectors, retained-real and
private interval coordinates, the ordinal book's records and endpoints,
its vertex order, and the quota parameters. The rank constructor reads
those columns directly. It computes every affine cost and four-field key,
compares the stored keys, and writes the rank rows before the measured sweep.

`fromBuilder` accepts a separately charged constructor for this inventory.
The raw selected-quote and cap filtering, site-cut sorting, group and
sparse-index enumeration, and production of the supplied columns belong to
that constructor. The finite contact sweep uses the scalar-charge adapter
described in `ContactCharge`.
-/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open StochasticGames.CompilerRun

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

structure Inventory (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets)) where
  columns : Columns a toSite s
  columns_correct : columns.Correct
  payoffs : NormalizedWork.Tables a.types a.targets
  payoffs_correct : payoffs.game = a.game
  gridValue : ℕ
  grid_correct : gridValue = grid a.game
  book : Book (Sparse.B (Fin a.types) (StoredLookup.SelectedGroups a toSite s)) (Fin a.targets)
    (Sparse.E (StoredLookup.SelectedReals a toSite s) (StoredLookup.SelectedGroups a toSite s))
  book_correct : book = Sparse.book a.game Fin.val Fin.val
    ((Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored)
  vertices : List (SelectedVertex a toSite s)
  vertices_correct : vertices = book.rankVertices
  parameters : Parameters (Sparse.B (Fin a.types) (StoredLookup.SelectedGroups a toSite s)) (Fin a.targets)
  parameters_correct : parameters = Sparse.selectedParameters (G := grid a.game) a.game toSite s (privateScale a.game)
  finiteBuyers : Fintype (Sparse.B (Fin a.types) (StoredLookup.SelectedGroups a toSite s))
  finiteSites : Fintype (Fin a.targets)
  finiteBids : Fintype (Sparse.E (StoredLookup.SelectedReals a toSite s) (StoredLookup.SelectedGroups a toSite s))

namespace Inventory

variable (x : Inventory a toSite s)

def ranks :=
  table x.vertices x.book.records (x.columns.makeAt x.gridValue x.grid_correct x.payoffs.fields) keyLess

theorem ranks_eq :
    x.ranks = selectedTable a toSite s (x.columns.make x.payoffs.fields) := by
  simp only [ranks,selectedTable,x.vertices_correct,x.book_correct,Columns.makeAt_eq]

theorem ranks_value : x.ranks.value = x.book.rankTable := by
  rw [x.ranks_eq, x.book_correct]
  exact (selectedTable_value a toSite s _ (x.columns.make_correct x.columns_correct x.payoffs x.payoffs_correct)).trans
    (Sparse.keyedTable_eq ..)

def contact : Run (StoredLookup.SelectedStored a toSite s) := do
  let bid := (⟨labelEq⟩ : Equality (Sparse.E (StoredLookup.SelectedReals a toSite s) (StoredLookup.SelectedGroups a toSite s)))
  let buyer := (⟨labelEq⟩ : Equality (Sparse.B (Fin a.types) (StoredLookup.SelectedGroups a toSite s)))
  let site := (⟨coordinateEq⟩ : Equality (Fin a.targets))
  let k ← attachIndexed x.book x.ranks x.ranks_value buyer site bid
  preparedBy x.finiteBuyers x.finiteSites x.finiteBids buyer site bid k x.parameters
    (ContactCharge.operandWidth (Binary.lengthInput a))

theorem contact_eq : x.contact = (attach x.book x.ranks x.ranks_value >>= fun k =>
    ContactCharge.prepared k x.parameters (ContactCharge.operandWidth (Binary.lengthInput a))) := by
  simp only [contact,attachIndexed_eq]
  apply congrArg (fun f => attach x.book x.ranks x.ranks_value >>= f)
  funext k
  exact preparedBy_eq x.finiteBuyers x.finiteSites x.finiteBids _ _ _ k x.parameters _

theorem contact_value :
    x.contact.value = (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).1 := by
  rw [x.contact_eq]
  simp [attach_value,ContactCharge.prepared_value,x.book_correct,x.parameters_correct,
    Sparse.selectedRun,Sparse.selectedParameters,Book.indexedContact_eq]

theorem contact_work (valid : a.Valid) (hs : SelectionBound a s) :
    let L := Binary.lengthInput a
    x.contact.Bound (contactSlots L (keySlots L)) (ContactCharge.width L) := by
  let L := Binary.lengthInput a
  have table := selectedTable_work a valid toSite s hs (x.columns.make x.payoffs.fields)
    (x.columns.make_correct x.columns_correct x.payoffs x.payoffs_correct)
    (x.columns.make_work valid hs x.payoffs x.payoffs_correct)
  rw [← x.ranks_eq] at table
  have attached := attach_work x.book x.ranks x.ranks_value table
  have r : x.book.records.length ≤ recordLimit L := by
    rw [x.book_correct,Sparse.Layout.stored_eq]
    exact (selected_inventory a toSite s hs).2.2.2
  rw [x.contact_eq]
  apply bound_bind attached
  rw [attach_value]
  exact (ContactCharge.prepared_work x.book x.parameters _).weaken
    (by unfold ContactCharge.slots OperandBounds.inputSlots; gcongr) le_rfl

end Inventory

def fromBuilder (build : Run (Inventory a toSite s)) : Run (StoredLookup.SelectedStored a toSite s) :=
  build >>= Inventory.contact

theorem fromBuilder_value (build : Run (Inventory a toSite s)) :
    (fromBuilder build).value = (Sparse.selectedRun (G := grid a.game) a.game toSite s (privateScale a.game)).1 :=
  build.value.contact_value

theorem fromBuilder_work (valid : a.Valid) (hs : SelectionBound a s) (build : Run (Inventory a toSite s))
    {k w : ℕ} (cost : build.Bound k w) :
    let L := Binary.lengthInput a
    (fromBuilder build).Bound (k+contactSlots L (keySlots L)) (max w (ContactCharge.width L)) := by
  have run := build.value.contact_work valid hs
  exact ⟨Nat.add_le_add cost.1 run.1,max_le_max cost.2 run.2⟩

/-- The actual input lists and quota book provide an inhabitant for the
constructor interface. Its generation cost is parameterized in `fromBuilder_work`. -/
def canonicalInventory (a : Input) (toSite : Fin a.types → Fin a.targets) (s : Selection (a.types*a.targets))
    (t : NormalizedWork.Tables a.types a.targets) (actual : t.game = a.game) : Inventory a toSite s :=
  let l := (Sparse.selectedLayout (G := grid a.game) a.game toSite s).stored
  let K := Sparse.book a.game Fin.val Fin.val l
  { columns := canonicalColumns a toSite s, columns_correct := canonicalColumns_correct a toSite s
    payoffs := t, payoffs_correct := actual, book := K, book_correct := rfl
    gridValue := grid a.game,grid_correct := rfl
    finiteBuyers := inferInstance,finiteSites := inferInstance,finiteBids := inferInstance
    vertices := K.rankVertices, vertices_correct := rfl
    parameters := Sparse.selectedParameters (G := grid a.game) a.game toSite s (privateScale a.game)
    parameters_correct := rfl }

end Kintali.QuotaSweep.RankRun
