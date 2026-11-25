module

public import Kintali.ExactRecovery.Sparse

/-! # Materialized bids and group coordinates

The proofs may index a sparse layout by a dependent type. The executable
columns below save its values before they are used to construct ranks and
quotas.
-/

@[expose] public section

namespace Kintali.ExactRecovery.Sparse.Layout

variable {I J A H : Type*} {G : ℕ} (L : Layout I J G A H)

section Column

variable {T X : Type*} [DecidableEq T]

@[noinline] def tabulate (keys : List T) (f : T → X) : List (T × X) :=
  keys.map fun t => (t, f t)

@[noinline] def read (column : List (T × X)) (fallback : T → X) (t : T) : X :=
  match column.lookup t with
  | some x => x
  | none => fallback t

theorem read_tabulate (keys : List T) (f : T → X) (t : T) (h : t ∈ keys) :
    read (tabulate keys f) f t = f t := by
  simp [read, tabulate, List.lookup_graph f h]

end Column

variable [Fintype A] [Fintype H] [DecidableEq A] [DecidableEq H] [Encodable A] [Encodable H]

def keys (T : Type*) [Fintype T] [DecidableEq T] [Encodable T] : List T :=
  letI : LinearOrder T := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  Finset.univ.sort

@[simp] theorem mem_keys (T : Type*) [Fintype T] [DecidableEq T] [Encodable T] (t : T) :
    t ∈ keys T := by simp [keys]

def stored : Layout I J G A H :=
  let bids := tabulate (keys A) L.real
  let groups := tabulate (keys H) (fun h => (L.representative h, L.size h))
  let atGroup := read groups (fun h => (L.representative h, L.size h))
  { real := ⟨read bids L.real, by
      intro a b h
      simp only [bids, read_tabulate, mem_keys] at h
      exact L.real.injective h⟩
    representative := ⟨fun h => (atGroup h).1, by
      intro a b h
      simp only [atGroup, groups, read_tabulate, mem_keys] at h
      exact L.representative.injective h⟩
    size := fun h => (atGroup h).2 }

@[simp] theorem stored_eq : L.stored = L := by
  rw [Layout.mk.injEq]
  exact ⟨Function.Embedding.ext (fun a => read_tabulate _ _ _ (mem_keys _ a)),
    Function.Embedding.ext (fun h => congrArg Prod.fst (read_tabulate _ _ _ (mem_keys _ h))),
    funext (fun h => congrArg Prod.snd (read_tabulate _ _ _ (mem_keys _ h)))⟩

end Kintali.ExactRecovery.Sparse.Layout
