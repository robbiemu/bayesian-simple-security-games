module

public import Kintali.QuotaSweep.WorkGraph
public import Kintali.QuotaSweep.Run
import Mathlib.Tactic.Linarith

/-! # Counted exact event time and allocation direction on a prepared graph -/

open scoped BigOperators

@[expose] public section
namespace Kintali.QuotaSweep

namespace Work

theorem fst_branch {α β : Type*} (p : Prop) [Decidable p] (x y : α × β) :
    (if p then x else y).1 = if p then x.1 else y.1 := by split <;> rfl

def sum {α : Type*} (s : Finset α) (f : α → ℚ × ℕ) : ℚ × ℕ :=
  ∑ a ∈ s, let z := f a; (z.1,z.2+2)

theorem sum_value {α : Type*} (s : Finset α) (f : α → ℚ × ℕ) :
    (sum s f).1 = ∑ a ∈ s, (f a).1 := by simp [sum, Prod.fst_sum]

theorem sum_work {α : Type*} (s : Finset α) (f : α → ℚ × ℕ) (u : ℕ) (h : ∀ a, (f a).2 ≤ u) :
    (sum s f).2 ≤ s.card*(u+2) := by
  rw [sum,Prod.snd_sum]
  exact (Finset.sum_le_sum fun a _ => Nat.add_le_add_right (h a) 2).trans (by simp)

end Work

namespace Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E)

def contribution (g : Graph B S E) (v : Vertex B S) (r : Record B S E) : ℚ × ℕ :=
  let m := readMark g.markers v
  if m.1 = r then
    let q := Work.search v 0 g.rates
    (q.1,m.2+q.2+2)
  else (0,m.2+1)

theorem contribution_work (g : Graph B S E) (v : Vertex B S) (r : Record B S E) :
    (contribution g v r).2 ≤ g.markers.length+g.rates.length+2 := by
  have hm := Work.search_work v (Sum.inr v) g.markers
  have hq := Work.search_work v 0 g.rates
  by_cases he : (Work.search v (Sum.inr v) g.markers).1 = r <;> simp [contribution,readMark,he] <;> omega

variable [Fintype B] [Fintype S]

def derivative (g : Graph B S E) (r : Record B S E) : ℚ × ℕ :=
  let positive := Work.sum Finset.univ fun s : S => contribution g (.inr s) r
  let negative := Work.sum Finset.univ fun b : B => contribution g (.inl b) r
  (positive.1-negative.1,positive.2+negative.2+1)

theorem derivative_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) (r : Record B S E) :
    (derivative (K.graph unit x rate).1 r).1 =
      K.direction (fun e => (x e).1) (K.through (fun e => (x e).1) rate) r := by
  simp [derivative, Work.sum_value, contribution, K.graph_marks, K.graph_rates,
    direction, received, released, marker, Work.fst_branch]

theorem derivative_work (g : Graph B S E) (r : Record B S E) :
    (derivative g r).2 ≤ Fintype.card (Vertex B S)*(g.markers.length+g.rates.length+4)+1 := by
  have ha := Work.sum_work Finset.univ (fun s : S => contribution g (.inr s) r) _
    (fun s => contribution_work g (.inr s) r)
  have hb := Work.sum_work Finset.univ (fun b : B => contribution g (.inl b) r) _
    (fun b => contribution_work g (.inl b) r)
  simp only [Finset.card_univ] at ha hb
  rw [show Fintype.card (Vertex B S) = Fintype.card S + Fintype.card B by
    simp [Vertex,Nat.add_comm], Nat.add_mul]
  exact Nat.add_le_add_right (Nat.add_le_add ha hb) 1

def candidate (g : Graph B S E) (x : Record B S E → ℚ × ℕ) (b : B) : Option ℚ × ℕ :=
  let q := Work.search (Sum.inl b) 0 g.rates
  if 0 < q.1 then
    let m := readMark g.markers (.inl b)
    let old := x m.1
    (some (old.1/q.1),q.2+m.2+old.2+3)
  else (none,q.2+1)

theorem candidate_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) (b : B) :
    (candidate (K.graph unit x rate).1 x b).1 =
      if 0 < K.through (fun e => (x e).1) rate (.inl b) then
        some ((x (K.worst (fun e => (x e).1) b)).1/K.through (fun e => (x e).1) rate (.inl b))
      else none := by
  simp [candidate, Work.fst_branch, K.graph_rates, K.graph_marks, marker]

omit [Fintype B] [Fintype S] [DecidableEq E] in
theorem candidate_work (g : Graph B S E) (x : Record B S E → ℚ × ℕ) (unit : ℕ)
    (hx : ∀ r, (x r).2 ≤ unit) (b : B) :
    (candidate g x b).2 ≤ g.markers.length+g.rates.length+unit+3 := by
  have hq := Work.search_work (Sum.inl b) 0 g.rates
  have hm := Work.search_work (Sum.inl b) (Sum.inr (Sum.inl b)) g.markers
  dsimp [candidate,readMark]
  split <;> grind

def eventList (g : Graph B S E) (t upper : ℚ) (c : List (B × Option ℚ)) : List ℚ :=
  let a := c.filterMap Prod.snd
  if g.source.isSome then a else (upper-t)::a

def measuredDuration (g : Graph B S E) (x : Record B S E → ℚ × ℕ) (t upper : ℚ) : ℚ × ℕ :=
  let c := Work.tabulate (candidate g x) K.buyerOrder
  let l := eventList g t upper c.1
  let best := Work.extremum ((· < ·) : ℚ → ℚ → Prop) 1 l none
  (best.1.getD 0,c.2+c.1.length+best.2+3)

omit [Fintype B] [Fintype S] in
private theorem mem_candidates (g : Graph B S E) (x : Record B S E → ℚ × ℕ) (q : ℚ) :
    q ∈ (Work.tabulate (candidate g x) K.buyerOrder).1.filterMap Prod.snd ↔
      ∃ b, (candidate g x b).1 = some q := by
  simp [Work.tabulate_value, List.filterMap_map, List.mem_filterMap, K.mem_buyerOrder]

private theorem eventList_mem (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) (t upper q : ℚ) :
    let g := (K.graph unit x rate).1
    q ∈ eventList g t upper (Work.tabulate (candidate g x) K.buyerOrder).1 ↔
      q ∈ K.times (fun e => (x e).1) rate t upper := by
  let g := (K.graph unit x rate).1
  have he : q ∈ (Work.tabulate (candidate g x) K.buyerOrder).1.filterMap Prod.snd ↔
      q ∈ K.exhaustions (fun e => (x e).1) rate := by
    rw [K.mem_candidates,K.mem_exhaustions]
    apply exists_congr
    intro b
    rw [show g = _ from rfl, K.candidate_value]
    split <;> simp_all
  change q ∈ eventList g t upper _ ↔ _
  unfold eventList times hasCycle
  rw [← K.graph_source unit x rate]
  change q ∈ (if g.source.isSome then _ else _) ↔ q ∈ (if g.source.isSome then _ else _)
  split
  · exact he
  · simpa only [List.mem_cons,Finset.mem_insert] using (or_congr Iff.rfl he : ((q=upper-t) ∨ _) ↔ _)

theorem measuredDuration_value (unit : ℕ) (x : Record B S E → ℚ × ℕ) (rate : S → ℚ) (t upper : ℚ) :
    (K.measuredDuration (K.graph unit x rate).1 x t upper).1 =
      K.duration (fun e => (x e).1) rate t upper := by
  let g := (K.graph unit x rate).1
  let l := eventList g t upper (Work.tabulate (candidate g x) K.buyerOrder).1
  have hm : ∀ q, q ∈ l ↔ q ∈ K.times (fun e => (x e).1) rate t upper :=
    K.eventList_mem unit x rate t upper
  have ha : K.duration (fun e => (x e).1) rate t upper ∈ l :=
    (hm _).mpr (K.duration_mem ..)
  change (Work.extremum _ 1 l none).1.getD 0 = _
  rw [Work.extremum_value]
  change (l.argmin id).getD 0 = _
  cases hr : l.argmin id with
  | none => simp [List.argmin_eq_none.mp hr] at ha
  | some a =>
    apply le_antisymm (List.le_of_mem_argmin ha (Option.mem_def.mpr hr))
    exact Finset.min'_le _ _ ((hm _).mp (List.argmin_mem (Option.mem_def.mpr hr)))

omit [Fintype B] [Fintype S] in
theorem measuredDuration_work (g : Graph B S E) (x : Record B S E → ℚ × ℕ) (unit : ℕ)
    (hx : ∀ r, (x r).2 ≤ unit) (t upper : ℚ) :
    (K.measuredDuration g x t upper).2 ≤
      K.records.length*(g.markers.length+g.rates.length+unit+4) + 3*K.records.length+5 := by
  let c := Work.tabulate (candidate g x) K.buyerOrder
  let l := eventList g t upper c.1
  have hc := (Work.tabulate_work _ _ (candidate_work g x unit hx) K.buyerOrder).trans
    (Nat.mul_le_mul_right _ K.buyerOrder_length)
  have hsize : c.1.length ≤ K.records.length := by simpa [c] using K.buyerOrder_length
  have hlen : l.length ≤ K.records.length+1 := by
    have hfilter := (List.length_filterMap_le Prod.snd c.1).trans hsize
    dsimp [l,eventList]; split <;> simp_all; omega
  have hb := (Work.extremum_work ((· < ·) : ℚ → ℚ → Prop) 1 l none).trans
    (Nat.mul_le_mul_right _ hlen)
  change c.2+c.1.length+(Work.extremum _ 1 l none).2+3 ≤ _
  change c.2 ≤ K.records.length*(g.markers.length+g.rates.length+unit+4) at hc
  omega

end Book
end Kintali.QuotaSweep
