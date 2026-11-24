module

public import StochasticGames.AtomArena
public import StochasticGames.MeanPayoffSemantics
import Mathlib.Data.List.FinRange
public import Mathlib.Data.FinEnum
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

/-! # Executable indexed edge and ownership tables

Lists, with proofs of coverage and uniqueness, give contiguous identifiers to
every vertex and every distinct edge occurrence. A row with repeated terms
therefore emits parallel arcs with different positions in the table.
-/

@[expose] public section
namespace StochasticGames.ArenaEncoding

open IntegerAtoms AtomArena AtomEncoding

structure Listing (α : Type*) where
  items : List α
  complete : ∀ x, x ∈ items
  nodup : items.Nodup

namespace Listing

variable {α β : Type*}

def index [DecidableEq α] (l : Listing α) : α ≃ Fin l.items.length :=
  (FinEnum.ofNodupList l.items l.complete l.nodup).equiv

theorem length_eq_card [Fintype α] (l : Listing α) : l.items.length = Fintype.card α := by
  classical
  simpa using (Fintype.card_congr l.index).symm

def fin (n : ℕ) : Listing (Fin n) :=
  ⟨List.finRange n, List.mem_finRange, List.nodup_finRange n⟩

def sum (a : Listing α) (b : Listing β) : Listing (α ⊕ β) where
  items := a.items.map Sum.inl ++ b.items.map Sum.inr
  complete := by rintro (x | x) <;> simp [a.complete, b.complete]
  nodup := (a.nodup.map Sum.inl_injective).append (b.nodup.map Sum.inr_injective) (by
    rintro x hx hy
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    simp at hy)

def option (a : Listing α) : Listing (Option α) where
  items := none :: a.items.map some
  complete := by rintro (_ | x) <;> simp [a.complete]
  nodup := List.nodup_cons.mpr ⟨by simp, a.nodup.map (Option.some_injective _)⟩

def sigma {β : α → Type*} (a : Listing α) (b : ∀ x, Listing (β x)) : Listing (Σ x, β x) where
  items := a.items.sigma fun x => (b x).items
  complete := by rintro ⟨x, y⟩; simp [List.mem_sigma, a.complete, (b x).complete]
  nodup := a.nodup.sigma fun x => (b x).nodup

def product (a : Listing α) (b : Listing β) : Listing (α × β) where
  items := a.items ×ˢ b.items
  complete := by rintro ⟨x, y⟩; simp [a.complete, b.complete]
  nodup := a.nodup.product b.nodup

def subtype (a : Listing α) (P : α → Prop) [DecidablePred P] : Listing {x // P x} where
  items := a.items.filterMap fun x => if hx : P x then some ⟨x, hx⟩ else none
  complete := by rintro ⟨x, hx⟩; exact List.mem_filterMap.mpr ⟨x, a.complete _, by simp [hx]⟩
  nodup := List.Nodup.filterMap (fun x y ⟨z, hz⟩ hx hy => by
    split at hx <;> simp_all) a.nodup

def map (a : Listing α) (e : α ≃ β) : Listing β where
  items := a.items.map e
  complete := fun x => List.mem_map.mpr ⟨e.symm x, a.complete _, e.apply_symm_apply _⟩
  nodup := a.nodup.map e.injective

end Listing

def compilerVariables (n a r : ℕ) : Listing (Var (Fin n) a r) :=
  let wires := (Listing.fin a).product (Listing.fin (r+1))
  let args := ((Listing.fin n).sum (wires.sum wires)).option
  args.map {
    toFun := fun
      | none => .reference
      | some (.inl i) => .source i
      | some (.inr (.inl (i, j))) => .high i j
      | some (.inr (.inr (i, j))) => .low i j
    invFun := fun
      | .reference => none
      | .source i => some (.inl i)
      | .high i j => some (.inr (.inl (i, j)))
      | .low i j => some (.inr (.inr (i, j)))
    left_inv := by rintro (_ | i | ⟨i,j⟩ | ⟨i,j⟩) <;> rfl
    right_inv := by intro v; cases v <;> rfl }

variable {ν : Type*}

def vertices (vars : Listing ν) (rows : List (IntAtom ν)) : Listing (Vertex rows) :=
  (vars.sum (Listing.fin rows.length)).option

def edges [DecidableEq ν] (vars : Listing ν) (rows : List (IntAtom ν)) : Listing (Edge rows) :=
  let rs := Listing.fin rows.length
  let replies := rs.sigma (fun r => Listing.fin (rows.get r).terms.length)
  let isolated := vars.subtype fun v => ∀ r : Row rows, (rows.get r).lhs ≠ v
  vars.sum (rs.sum (replies.sum isolated))

structure ArcRecord where
  src : ℕ
  dst : ℕ
  weight : ℤ
  deriving Repr, DecidableEq

structure Table where
  start : ℕ
  owners : List Bool
  arcs : List ArcRecord
  deriving Repr, DecidableEq

def table [DecidableEq ν] (vars : Listing ν) (rows : List (IntAtom ν)) (swap : Bool) : Table :=
  let vs := vertices vars rows
  let id (v : Vertex rows) := (vs.index v).val
  { start := id none
    owners := vs.items.map fun v => if swap then !(isMax v) else isMax v
    arcs := (edges vars rows).items.map fun e =>
      ⟨id (src e), id (dst e), if swap then -(vs.items.length : ℤ) * weight e - 1 else weight e⟩ }

theorem compilerVariables_length (n a r : ℕ) :
    (compilerVariables n a r).items.length = 1 + n + 2 * a * (r+1) := by
  simp [compilerVariables, Listing.map, Listing.option, Listing.sum, Listing.product,
    Listing.fin, List.length_product]
  ring

theorem vertices_length (vars : Listing ν) (rows : List (IntAtom ν)) :
    (vertices vars rows).items.length = 1 + vars.items.length + rows.length := by
  simp [vertices, Listing.option, Listing.sum, Listing.fin]
  omega

theorem edges_length_le [DecidableEq ν] (vars : Listing ν) (rows : List (IntAtom ν)) :
    (edges vars rows).items.length ≤ 2 * vars.items.length + rows.length +
      (rows.map fun r => r.terms.length).sum := by
  have replies : ((List.finRange rows.length).sigma
      (fun r => List.finRange (rows.get r).terms.length)).length =
      (rows.map fun r => r.terms.length).sum := by
    simp [List.sigma, List.length_flatMap]
    congr 1
    apply List.ext_getElem <;> simp
  simp only [edges, Listing.sum, Listing.fin, Listing.sigma, Listing.subtype,
    List.length_append, List.length_map, List.length_finRange, replies]
  have hh := List.length_filterMap_le (l := vars.items)
    (f := fun x => if h : ∀ r : Row rows, (rows.get r).lhs ≠ x then
      some (⟨x, h⟩ : Isolated rows) else none)
  omega

/-- Numeric vertex and edge IDs are bijective. An edge's list position is
its identifier even when another arc has the same endpoints and weight. -/
def Table.Represents {V E : Type*} (t : Table) (G : MeanPayoff.Game V E) (s : V) : Prop :=
  ∃ (vi : V ≃ Fin t.owners.length) (ei : E ≃ Fin t.arcs.length),
    t.start = (vi s).val ∧ (∀ v, t.owners.get (vi v) = G.isMax v) ∧
      ∀ e, t.arcs.get (ei e) = ⟨(vi (G.src e)).val, (vi (G.dst e)).val, G.weight e⟩

theorem table_represents [Fintype ν] [DecidableEq ν] [Nonempty ν] (vars : Listing ν)
    (rows : List (IntAtom ν)) (ok : ∀ r : Row rows, 0 < (rows.get r).terms.length) (swap : Bool) :
    (table vars rows swap).Represents (if swap then (game rows ok).Swap else game rows ok) none := by
  let vs := vertices vars rows
  let es := edges vars rows
  let t := table vars rows swap
  have vl : vs.items.length = t.owners.length := by simp [t, table, vs]
  have el : es.items.length = t.arcs.length := by simp [t, table, es]
  let vi := vs.index.trans (finCongr vl)
  let ei := es.index.trans (finCongr el)
  refine ⟨vi, ei, rfl, fun v => ?_, fun e => ?_⟩
  · have get : vs.items.get (vs.index v) = v := vs.index.symm_apply_apply v
    simp only [table, List.get_eq_getElem, List.getElem_map]
    change (if swap then !(isMax (vs.items.get (vs.index v))) else
      isMax (vs.items.get (vs.index v))) = _
    rw [get]
    cases swap <;> rfl
  · have get : es.items.get (es.index e) = e := es.index.symm_apply_apply e
    have card := vs.length_eq_card
    simp only [table, List.get_eq_getElem, List.getElem_map]
    rw [List.get_eq_getElem] at get
    change (⟨(vs.index (src es.items[(es.index e).val])).val,
      (vs.index (dst es.items[(es.index e).val])).val,
      if swap then -(vs.items.length : ℤ) * weight es.items[(es.index e).val] - 1
      else weight es.items[(es.index e).val]⟩ : ArcRecord) = _
    rw [get]
    cases swap
    · rfl
    · congr 1
      change -(vs.items.length : ℤ) * weight e - 1 = -(Fintype.card (Vertex rows) : ℤ) * weight e - 1
      rw [card]

namespace Table

structure Valid (t : Table) : Prop where
  start_lt : t.start < t.owners.length
  src_lt : ∀ i : Fin t.arcs.length, (t.arcs.get i).src < t.owners.length
  dst_lt : ∀ i : Fin t.arcs.length, (t.arcs.get i).dst < t.owners.length
  total : ∀ v : Fin t.owners.length, ∃ i : Fin t.arcs.length, (t.arcs.get i).src = v.val

def game (t : Table) (h : t.Valid) :
    MeanPayoff.Game (Fin t.owners.length) (Fin t.arcs.length) where
  src e := ⟨(t.arcs.get e).src, h.src_lt e⟩
  dst e := ⟨(t.arcs.get e).dst, h.dst_lt e⟩
  weight e := (t.arcs.get e).weight
  isMax v := t.owners.get v
  outgoing v := (h.total v).imp fun _ eq => Fin.ext eq

def Nonnegative (t : Table) : Prop := ∃ h : t.Valid, (t.game h).Nonnegative ⟨t.start, h.start_lt⟩

variable {V E W F : Type*} {t : Table} {G : MeanPayoff.Game V E} {s : V}

theorem Represents.valid (rep : t.Represents G s) : t.Valid := by
  obtain ⟨vi, ei, hs, _, ha⟩ := rep
  refine ⟨hs ▸ (vi s).isLt, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨e, rfl⟩ := ei.surjective i
    rw [ha]; exact (vi _).isLt
  · intro i
    obtain ⟨e, rfl⟩ := ei.surjective i
    rw [ha]; exact (vi _).isLt
  · intro i
    obtain ⟨v, rfl⟩ := vi.surjective i
    obtain ⟨e, hv⟩ := G.outgoing v
    exact ⟨ei e, by rw [ha, hv]⟩

private theorem pull_certificate {H : MeanPayoff.Game W F} (vi : V ≃ W) (ei : E ≃ F)
    (hs : ∀ e, H.src (ei e) = vi (G.src e))
    (hd : ∀ e, H.dst (ei e) = vi (G.dst e))
    (hw : ∀ e, H.weight (ei e) = G.weight e)
    (ho : ∀ v, H.isMax (vi v) = G.isMax v)
    (h : H.Certificate (vi s)) : G.Certificate s := by
  obtain ⟨p, R, x, hr, step⟩ := h
  let q : G.Policy := fun v =>
    ⟨ei.symm (p (vi v)).val, vi.injective (by
      rw [← hs, ei.apply_symm_apply, (p (vi v)).property])⟩
  refine ⟨q, R ∘ vi, x ∘ vi, hr, fun e he hv => ?_⟩
  have ha : H.Allowed p (ei e) := by
    intro hm
    rw [hs, ho] at hm
    rw [hs]
    exact ei.symm.injective (by simpa [q] using he hm)
  have h' := step (ei e) ha (by rw [hs]; exact hv)
  simpa only [hs, hd, hw, Function.comp_apply] using h'

theorem Represents.nonnegative_iff [Fintype V] [Fintype E] (rep : t.Represents G s) :
    t.Nonnegative ↔ G.Nonnegative s := by
  let valid := rep.valid
  let H := t.game valid
  obtain ⟨vi, ei, hs, ho, ha⟩ := rep
  have source (e : E) : H.src (ei e) = vi (G.src e) := Fin.ext (congrArg ArcRecord.src (ha e))
  have dest (e : E) : H.dst (ei e) = vi (G.dst e) := Fin.ext (congrArg ArcRecord.dst (ha e))
  have weight (e : E) : H.weight (ei e) = G.weight e := congrArg ArcRecord.weight (ha e)
  have owner (v : V) : H.isMax (vi v) = G.isMax v := ho v
  have start : (⟨t.start, valid.start_lt⟩ : Fin t.owners.length) = vi s := Fin.ext hs
  rw [G.nonnegative_iff_certificate]
  constructor
  · rintro ⟨h, hn⟩
    change H.Nonnegative _ at hn
    rw [start, H.nonnegative_iff_certificate] at hn
    exact pull_certificate vi ei source dest weight owner hn
  · intro cert
    refine ⟨valid, ?_⟩
    change H.Nonnegative _
    rw [start, H.nonnegative_iff_certificate]
    apply pull_certificate vi.symm ei.symm (G := H) (H := G)
    · intro i; obtain ⟨e, rfl⟩ := ei.surjective i
      simp [source]
    · intro i; obtain ⟨e, rfl⟩ := ei.surjective i
      simp [dest]
    · intro i; obtain ⟨e, rfl⟩ := ei.surjective i
      simp [weight]
    · intro i; obtain ⟨v, rfl⟩ := vi.surjective i
      simp [owner]
    · simpa using cert

end Table

theorem table_nonnegative_iff [Fintype ν] [DecidableEq ν] [Nonempty ν] (vars : Listing ν)
    (rows : List (IntAtom ν)) (ok : ∀ r : Row rows, 0 < (rows.get r).terms.length) (swap : Bool) :
    (table vars rows swap).Nonnegative ↔
      (if swap then (game rows ok).Swap else game rows ok).Nonnegative none :=
  (table_represents vars rows ok swap).nonnegative_iff

end StochasticGames.ArenaEncoding
