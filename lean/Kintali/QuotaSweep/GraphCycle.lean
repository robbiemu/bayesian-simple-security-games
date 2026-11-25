module

public import Kintali.QuotaSweep.Rates
public import Kintali.QuotaSweep.Cycle

/-! # Deterministically select a single directed cycle, in book order -/

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] (K : Book B S E)

/-- Each buyer is listed by the position of its outside record. -/
def buyerOrder : List B :=
  K.records.filterMap fun r => match r with
    | .inr (.inl b) => some b
    | _ => none

omit [Fintype B] [Fintype S] in
theorem mem_buyerOrder (b : B) : b ∈ K.buyerOrder := by
  exact List.mem_filterMap.mpr ⟨outside b, K.complete _, rfl⟩

def cycleBuyer (x : Record B S E → ℚ) : Option B :=
  K.buyerOrder.find? fun b => Routing.cyclic (K.next x) (.inl b)

def hasCycle (x : Record B S E → ℚ) : Bool := (K.cycleBuyer x).isSome

def aroundCycle (x : Record B S E → ℚ) (v : Vertex B S) : ℚ :=
  match K.cycleBuyer x with
  | some b => Routing.around (K.next x) (.inl b) v
  | none => 0

private theorem cyclic_buyer_of_vertex {x : Record B S E → ℚ} {v : Vertex B S}
    (hv : Routing.cyclic (K.next x) v = true) :
    ∃ b, Routing.cyclic (K.next x) (.inl b) = true := by
  rcases v with b | s
  · exact ⟨b, hv⟩
  · let f := Routing.advance (K.next x)
    have hb := Function.bijOn_periodicPts f
    have hp := Routing.cyclic_iff.mp hv
    have hnone : (none : Option (Vertex B S)) ∈ Function.periodicPts f :=
      Function.mk_mem_periodicPts (by decide : 0 < 1) (by rfl)
    cases hn : K.next x (.inr s) with
    | none =>
      have he : f (some (.inr s)) = f none := hn
      cases hb.injOn hp hnone he
    | some v =>
      rcases v with b | t
      · exact ⟨b, Routing.cyclic_iff.mpr (hn ▸ hb.mapsTo hp)⟩
      · exact False.elim (K.no_site_to_site x s t hn)

theorem no_cyclic_vertex {x : Record B S E → ℚ} (h : K.hasCycle x ≠ true)
    (v : Vertex B S) : Routing.cyclic (K.next x) v ≠ true := by
  intro hv
  obtain ⟨b, hb⟩ := K.cyclic_buyer_of_vertex hv
  cases hseed : K.cycleBuyer x with
  | none => exact (List.find?_eq_none.mp hseed b (K.mem_buyerOrder b)) hb
  | some c => simp [hasCycle, hseed] at h

theorem aroundCycle_conservation (x : Record B S E → ℚ) (v : Vertex B S) :
    Routing.incoming (K.next x) (K.aroundCycle x) v = K.aroundCycle x v := by
  cases hseed : K.cycleBuyer x with
  | none => simp [aroundCycle, Routing.incoming, hseed]
  | some b =>
    have hs : Routing.cyclic (K.next x) (.inl b) = true := List.find?_some (p := fun c => Routing.cyclic (K.next x) (.inl c)) hseed
    have he : K.aroundCycle x = Routing.around (K.next x) (.inl b) := by funext u; simp [aroundCycle, hseed]
    rw [he]
    exact Routing.around_conservation hs v

theorem aroundCycle_seed {x : Record B S E → ℚ} (hc : K.hasCycle x = true) :
    ∃ b, K.aroundCycle x (.inl b) = 1 := by
  cases hseed : K.cycleBuyer x with
  | none => simp [hasCycle, hseed] at hc
  | some b =>
    have hs : Routing.cyclic (K.next x) (.inl b) = true := List.find?_some (p := fun c => Routing.cyclic (K.next x) (.inl c)) hseed
    exact ⟨b, by simp [aroundCycle, hseed, Routing.around_seed hs]⟩

theorem aroundCycle_zero_or_one (x : Record B S E → ℚ) (v : Vertex B S) :
    K.aroundCycle x v = 0 ∨ K.aroundCycle x v = 1 := by
  cases h : K.cycleBuyer x with
  | none => simp [aroundCycle, h]
  | some b => by_cases hu : Routing.onCycle (K.next x) (.inl b) v <;> simp [aroundCycle, h, Routing.around, hu]

end Kintali.QuotaSweep.Book
