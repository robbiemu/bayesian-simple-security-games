module

public import Kintali.QuotaSweep.FastChoices
public import Kintali.QuotaSweep.Events
public import Kintali.QuotaSweep.RoutingWork
import Mathlib.Tactic.Linarith

/-! # Materialized choices, successor graph and through-rates for a stage -/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep

namespace Work

theorem read_tabulate {α β : Type*} [DecidableEq α] (f : α → β × ℕ) (l : List α) (b : β)
    {a : α} (h : a ∈ l) : (search a b (tabulate f l).1).1 = (f a).1 := by
  rw [search_value, tabulate_value, List.lookup_graph (fun x => (f x).1) h]
  rfl

@[simp] theorem tabulate_length {α β : Type*} (f : α → β × ℕ) (l : List α) :
    (tabulate f l).1.length = l.length := by simp [tabulate_value]

end Work

namespace Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E] (K : Book B S E)

def vertexOrder : List (Vertex B S) := K.records.filterMap Sum.getRight?

theorem mem_vertexOrder (v : Vertex B S) : v ∈ K.vertexOrder :=
  List.mem_filterMap.mpr ⟨.inr v,K.complete _,rfl⟩

theorem vertexOrder_length : K.vertexOrder.length ≤ K.records.length := List.length_filterMap_le ..

theorem buyerOrder_length : K.buyerOrder.length ≤ K.records.length := List.length_filterMap_le ..

def marker (x : Record B S E → ℚ) : Vertex B S → Record B S E :=
  Sum.elim (K.worst x) (K.proposal x)

def measuredMarker (unit : ℕ) (x : Record B S E → ℚ × ℕ) : Vertex B S → Record B S E × ℕ :=
  Sum.elim (K.measuredWorst unit x) (K.measuredProposal unit x)

theorem measuredMarker_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (v : Vertex B S) :
    (K.measuredMarker unit x v).1 = K.marker (fun r => (x r).1) v := by
  cases v with
  | inl b => exact K.measuredWorst_value ..
  | inr s => exact K.measuredProposal_value ..

theorem measuredMarker_work (unit : ℕ) (x : Record B S E → ℚ × ℕ) (hx : ∀ r, (x r).2 ≤ unit)
    (v : Vertex B S) : (K.measuredMarker unit x v).2 ≤ choiceLimit K.records.length unit := by
  cases v with
  | inl b => exact K.measuredWorst_work unit x hx b
  | inr s => exact K.measuredProposal_work unit x hx s

def successor : Vertex B S → Record B S E → Option (Vertex B S)
  | .inl _, .inl e => some (.inr (K.site e))
  | .inr _, .inl e => some (.inl (K.buyer e))
  | _, .inr _ => none

theorem successor_marker (x : Record B S E → ℚ) (v : Vertex B S) :
    K.successor v (K.marker x v) = K.next x v := by
  cases v with
  | inl b => cases hb : K.worst x b <;> simp [successor,marker,next,hb]
  | inr s => cases hs : K.proposal x s <;> simp [successor,marker,next,hs]

def cachedMarker (unit : ℕ) (buyers : List (B × Release B S E)) :
    Vertex B S → Record B S E × ℕ
  | .inl b =>
    let rel := readRelease buyers b
    (rel.1.1,rel.2+1)
  | .inr s => K.fastProposal unit buyers s

def marksLimit (r u : ℕ) := buyerTableLimit r u + r*(proposalLimit r u+r+2)

def marks (unit : ℕ) (x : Record B S E → ℚ × ℕ) :=
  let buyers := K.releaseTable unit x
  let chosen := Work.tabulate (K.cachedMarker unit buyers.1) K.vertexOrder
  (chosen.1,buyers.2+chosen.2)

theorem marks_work (unit : ℕ) (x : Record B S E → ℚ × ℕ) (hx : ∀ r, (x r).2 ≤ unit) :
    (K.marks unit x).2 ≤ marksLimit K.records.length unit := by
  let buyers := (K.releaseTable unit x).1
  let r := K.records.length
  have hlen : buyers.length ≤ r := by simpa [buyers,releaseTable,r] using K.buyerOrder_length
  have hw (v) : (K.cachedMarker unit buyers v).2 ≤ proposalLimit r unit+r+1 := by
    cases v with
    | inl b =>
      have h := (Work.search_work b (outside b,none) buyers).trans hlen
      change (Work.search b (outside b,none) buyers).2+1 ≤ _
      omega
    | inr s => exact (K.fastProposal_work unit buyers hlen s).trans (by change proposalLimit r unit ≤ _; omega)
  exact Nat.add_le_add (K.releaseTable_work unit x hx K.buyerOrder_length)
    ((Work.tabulate_work _ _ hw _).trans (Nat.mul_le_mul_right _ K.vertexOrder_length))

def edges (unit : ℕ) (table : List (Vertex B S × Record B S E)) :=
  Work.tabulate (fun v =>
    let m := Work.search v (Sum.inr v) table
    (K.successor v m.1,m.2+unit+2)) K.vertexOrder

def readMark (table : List (Vertex B S × Record B S E)) (v : Vertex B S) :=
  Work.search v (Sum.inr v) table

def readEdge (table : List (Vertex B S × Option (Vertex B S))) (v : Vertex B S) :=
  (Work.search v none table).1

theorem readMark_marks (unit : ℕ) (x : Record B S E → ℚ × ℕ) (v : Vertex B S) :
    (readMark (K.marks unit x).1 v).1 = K.marker (fun r => (x r).1) v := by
  unfold readMark marks
  rw [Work.read_tabulate _ _ _ (K.mem_vertexOrder v)]
  cases v with
  | inl b =>
    change (readRelease (K.releaseTable unit x).1 b).1.1 = _
    rw [K.readRelease_table]
    exact K.measuredWorst_value ..
  | inr s => exact K.fastProposal_value ..

theorem readEdge_edges (unit : ℕ) (x : Record B S E → ℚ × ℕ) :
    readEdge (K.edges unit (K.marks unit x).1).1 = K.next (fun r => (x r).1) := by
  funext v
  rw [readEdge,edges,Work.read_tabulate _ _ _ (K.mem_vertexOrder _)]
  change K.successor v (readMark (K.marks unit x).1 v).1 = _
  rw [K.readMark_marks, K.successor_marker]

variable [Fintype B] [Fintype S]

def seed (table : List (Vertex B S × Option (Vertex B S))) : Option B × ℕ :=
  Work.find (fun b =>
    let t := Routing.cycleProbe (readEdge table) (.inl b)
    (t.1,t.2*(table.length+6)+2)) K.buyerOrder

def rateAt (unit : ℕ) (rate : S → ℚ) (table : List (Vertex B S × Option (Vertex B S)))
    (source : Option B) (v : Vertex B S) : ℚ × ℕ :=
  match source with
  | some b =>
    let t := Routing.orbitProbe (readEdge table) (.inl b) v
    (if t.1 then 1 else 0, t.2*(table.length+6)+2)
  | none =>
    let t := Routing.measuredPath (readEdge table) (injection rate) v
    (t.1,t.2*(table.length+6)+Fintype.card (Vertex B S)*(unit+8)+2)

theorem seed_value (x : Record B S E → ℚ) (t : List (Vertex B S × Option (Vertex B S)))
    (h : readEdge t = K.next x) : (K.seed t).1 = K.cycleBuyer x := by
  simp [seed, Work.find_value, h, Routing.cycleProbe_value, cycleBuyer]

theorem rateAt_value (x : Record B S E → ℚ) (unit : ℕ) (rate : S → ℚ)
    (t : List (Vertex B S × Option (Vertex B S))) (h : readEdge t = K.next x) (v : Vertex B S) :
    (rateAt unit rate t (K.cycleBuyer x) v).1 = K.through x rate v := by
  cases hb : K.cycleBuyer x with
  | none => simp [rateAt, h, Routing.measuredPath_value, through, hasCycle, hb]
  | some b => simp [rateAt, h, Routing.orbitProbe_value, through, hasCycle, aroundCycle, Routing.around, hb]

def graphLimit (n r u : ℕ) :=
  marksLimit r u + r*(r+u+3) + r*((n+2)*(r+6)+3) +
    r*((n+1)*(n+1)*(r+6)+n*(u+8)+3)

structure Graph (B S E : Type*) where
  markers : List (Vertex B S × Record B S E)
  source : Option B
  rates : List (Vertex B S × ℚ)

/-- Evaluate all choices once, build the successor table, select the first
cycle buyer, then evaluate all through-rates against this table. -/
def graph (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) : Graph B S E × ℕ :=
  let m := K.marks unit x
  let t := K.edges unit m.1
  let b := K.seed t.1
  let q := Work.tabulate (rateAt unit rate t.1 b.1) K.vertexOrder
  (⟨m.1,b.1,q.1⟩, m.2+t.2+b.2+q.2)

theorem graph_marks (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) (v : Vertex B S) :
    (readMark (K.graph unit x rate).1.markers v).1 = K.marker (fun r => (x r).1) v :=
  K.readMark_marks ..

theorem graph_source (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) :
    (K.graph unit x rate).1.source = K.cycleBuyer (fun r => (x r).1) :=
  K.seed_value _ _ (K.readEdge_edges unit x)

theorem graph_rates (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) (v : Vertex B S) :
    (Work.search v 0 (K.graph unit x rate).1.rates).1 = K.through (fun r => (x r).1) rate v := by
  unfold graph
  rw [Work.read_tabulate _ _ _ (K.mem_vertexOrder _)]
  rw [K.seed_value _ _ (K.readEdge_edges unit x)]
  exact K.rateAt_value _ _ _ _ (K.readEdge_edges unit x) _


theorem graph_table_lengths (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) :
    (K.graph unit x rate).1.markers.length = K.vertexOrder.length ∧
      (K.graph unit x rate).1.rates.length = K.vertexOrder.length := by
  simp [graph, marks]

omit [DecidableEq E] in
theorem rateAt_work (unit : ℕ) (rate : S → ℚ) (t : List (Vertex B S × Option (Vertex B S)))
    (b : Option B) (v : Vertex B S) :
    let n := Fintype.card (Vertex B S)
    (rateAt unit rate t b v).2 ≤ (n+1)*(n+1)*(t.length+6)+n*(unit+8)+2 := by
  let n := Fintype.card (Vertex B S)
  have hone : Fintype.card (Option (Vertex B S)) = n+1 := Fintype.card_option
  have h1 : n+1 ≤ (n+1)*(n+1) := by nlinarith
  cases b with
  | none =>
    have hw := Routing.measuredPath_work (readEdge t) (injection rate) v
    rw [hone] at hw
    have h2 : Fintype.card (Vertex B S)*(n+1) ≤ (n+1)*(n+1) := Nat.mul_le_mul_right _ (Nat.le_succ _)
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hw.trans h2)) _) _
  | some b =>
    have hw := Routing.orbitProbe_work (readEdge t) (Sum.inl b) v
    rw [hone] at hw
    have ha := Nat.mul_le_mul_right (t.length+6) (hw.trans h1)
    exact Nat.add_le_add_right (ha.trans (Nat.le_add_right _ _)) 2

/-- All three stage tables have at most one entry per record of the input
list. The charge includes graph-table lookup, every walked successor,
choice predicates, rate sums, and the comparison of positive return times. -/
theorem graph_work (unit : ℕ) (x : Record B S E → ℚ × ℕ) (hx : ∀ r, (x r).2 ≤ unit)
    (rate : S → ℚ) :
    (K.graph unit x rate).2 ≤ graphLimit (Fintype.card (Vertex B S)) K.records.length unit := by
  let n := Fintype.card (Vertex B S)
  let r := K.records.length
  let m := K.marks unit x
  let t := K.edges unit m.1
  let source := K.seed t.1
  have hm : m.1.length ≤ r := by simpa [m,marks,r] using K.vertexOrder_length
  have ht : t.1.length ≤ r := by simpa [t,edges,r] using K.vertexOrder_length
  have hc : m.2 ≤ marksLimit r unit := K.marks_work unit x hx
  have hs : t.2 ≤ r*(r+unit+3) := by
    unfold t edges
    apply (Work.tabulate_work _ (r+unit+2) _ _).trans (Nat.mul_le_mul_right _ K.vertexOrder_length)
    intro v
    exact Nat.add_le_add_right (Nat.add_le_add_right ((Work.search_work v (Sum.inr v) m.1).trans hm) _) _
  have hb : source.2 ≤ r*((n+2)*(r+6)+3) := by
    unfold source seed
    apply (Work.find_work _ ((n+2)*(r+6)+2) _ _).trans (Nat.mul_le_mul_right _ K.buyerOrder_length)
    intro b
    have hw := Routing.cycleProbe_work (readEdge t.1) (Sum.inl b)
    rw [Fintype.card_option] at hw
    exact Nat.add_le_add_right (Nat.mul_le_mul hw (Nat.add_le_add_right ht 6)) 2
  have hq : (Work.tabulate (rateAt unit rate t.1 source.1) K.vertexOrder).2 ≤
      r*((n+1)*(n+1)*(r+6)+n*(unit+8)+3) := by
    apply (Work.tabulate_work _ ((n+1)*(n+1)*(r+6)+n*(unit+8)+2) _ _).trans
      (Nat.mul_le_mul_right _ K.vertexOrder_length)
    intro v
    apply (rateAt_work unit rate t.1 source.1 v).trans
    gcongr
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc hs) hb) hq

end Book
end Kintali.QuotaSweep
