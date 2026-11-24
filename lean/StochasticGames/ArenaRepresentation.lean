module

public import StochasticGames.ArenaEncoding
import all StochasticGames.AtomEncoding
import all StochasticGames.IntegerAtoms
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # The named terminals and idle rows of the manuscript

Two fresh terminal variables have four difference rows. Eliminating the pinned
variables substitutes the origin and the origin plus one, then subtracts a
left-side offset from every term. Scaling changes the gap between the pinned
terminals from one to Q. Adding a tautological row at a missing left side
changes the arena's vertex count. Its weak threshold before and after owner
reversal is still determined by the same row-feasibility predicate.
-/

@[expose] public section
namespace StochasticGames.ArenaRepresentation
open AtomEncoding IntegerAtoms ArenaEncoding

variable {ν : Type*}

abbrev Named (ν : Type*) := ν ⊕ Bool

def extend {K : Type*} [Add K] (o : ν) (unit : K) (x : ν → K) : Named ν → K
  | .inl v => x v
  | .inr true => x o
  | .inr false => x o + unit

def Pinned {K : Type*} [Add K] (o : ν) (unit : K) (y : Named ν → K) : Prop :=
  y (.inr true) = y (.inl o) ∧ y (.inr false) = y (.inl o) + unit

theorem extend_pinned {K : Type*} [Add K] (o : ν) (c : K) (x : ν → K) :
    Pinned o c (extend o c x) := ⟨rfl, rfl⟩

theorem extend_restrict {K : Type*} [Add K] (o : ν) (c : K) (y : Named ν → K)
    (h : Pinned o c y) : extend o c (fun v => y (.inl v)) = y := by
  funext v
  rcases v with v | (_ | _)
  · rfl
  · exact h.2.symm
  · exact h.1.symm

def collapse (o : ν) : Named ν → ν × ℚ
  | .inl v => (v,0)
  | .inr true => (o,0)
  | .inr false => (o,1)

def collapseSignal (o : ν) (s : Signal (Named ν)) : Signal ν :=
  ((collapse o s.1).1, (collapse o s.1).2 + s.2)

def eliminate (o : ν) (a : Atom (Named ν)) : Atom ν :=
  fromSignals (collapse o a.lhs) (a.terms.map (collapseSignal o))

theorem eliminate_fromSignals (o : ν) (lhs : Signal (Named ν)) (rhs : List (Signal (Named ν))) :
    eliminate o (fromSignals lhs rhs) =
      fromSignals (collapseSignal o lhs) (rhs.map (collapseSignal o)) := by
  simp only [eliminate, fromSignals, collapseSignal, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t _
  congr 1
  ring

private theorem eval_collapse (o : ν) (x : ν → ℝ) (i : Named ν) :
    Signal.value (collapse o i) x = extend o 1 x i := by
  rcases i with i | (_ | _) <;> simp [Signal.value, collapse, extend]

theorem eliminate_holds (o : ν) (x : ν → ℝ) (a : Atom (Named ν)) :
    (eliminate o a).Holds x ↔ a.Holds (extend o 1 x) := by
  rw [eliminate, AtomEncoding.fromSignals_holds]
  simp only [List.mem_map, exists_exists_and_eq_and, eval_collapse, Atom.Holds]
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  change (_ ≤ x (collapse o t.1).1 + (((collapse o t.1).2 + t.2 : ℚ) : ℝ)) ↔ _
  rw [Rat.cast_add, ← add_assoc]
  change (_ ≤ Signal.value (collapse o t.1) x + _) ↔ _
  rw [eval_collapse]
  rfl

def atomPins (o : ν) : List (Atom (Named ν)) :=
  [⟨.inr true, [(.inl o,0)]⟩, ⟨.inl o, [(.inr true,0)]⟩,
   ⟨.inr false, [(.inl o,1)]⟩, ⟨.inl o, [(.inr false,-1)]⟩]

theorem atomPins_iff (o : ν) (y : Named ν → ℝ) :
    AtomEncoding.RowsHold (atomPins o) y ↔ Pinned o 1 y := by
  simp [AtomEncoding.RowsHold, atomPins, Atom.Holds, Signal.value, Pinned]
  constructor
  · rintro ⟨hw,hw',hl,hl'⟩; constructor <;> linarith
  · rintro ⟨hw,hl⟩; refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem eliminate_rows_iff (o : ν) (xs : List (Atom (Named ν))) (x : ν → ℝ) :
    AtomEncoding.RowsHold (xs.map (eliminate o)) x ↔
      ∃ y : Named ν → ℝ, (∀ i, y (.inl i) = x i) ∧
        AtomEncoding.RowsHold (atomPins o ++ xs) y := by
  constructor
  · intro h
    refine ⟨extend o 1 x, fun _ => rfl, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with pin | body
    · exact (atomPins_iff o _).mpr (extend_pinned o 1 x) a pin
    · exact (eliminate_holds o x a).mp (h _ (List.mem_map.mpr ⟨a, body, rfl⟩))
  · rintro ⟨y, old, h⟩ a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    have pin := (atomPins_iff o y).mp (fun k hk => h k (List.mem_append_left _ hk))
    have eq := extend_restrict o 1 y pin
    rw [funext old] at eq
    apply (eliminate_holds o x r).mpr
    rw [eq]
    exact h r (List.mem_append_right _ hr)

def intPins (o : ν) (Q : ℕ) : List (IntAtom (Named ν)) :=
  [⟨.inr true, [(.inl o,0)]⟩, ⟨.inl o, [(.inr true,0)]⟩,
   ⟨.inr false, [(.inl o,Q)]⟩, ⟨.inl o, [(.inr false,-(Q : ℤ))]⟩]

theorem encode_pinned_body (o : ν) (Q : ℕ) (body : List (Atom (Named ν))) :
    encodeAt Q (atomPins o ++ body) = intPins o Q ++ encodeAt Q body := by
  change (atomPins o ++ body).map (integerAtom Q) = _
  rw [List.map_append]
  have pins : (atomPins o).map (integerAtom Q) = intPins o Q := by
    simp [atomPins, intPins, integerAtom]
    exact_mod_cast (Int.floor_intCast (R := ℚ) (-(Q : ℤ)))
  rw [pins]
  rfl

theorem intPins_iff (o : ν) (Q : ℕ) (y : Named ν → ℤ) :
    IntegerAtoms.RowsHold (intPins o Q) y ↔ Pinned o (Q : ℤ) y := by
  simp [IntegerAtoms.RowsHold, intPins, IntAtom.Holds, Pinned]
  omega

def tautology (v : ν) : IntAtom ν := ⟨v, [(v,0)]⟩

def withIdleRows [DecidableEq ν] (vs : Listing ν) (rs : List (IntAtom ν)) :=
  rs ++ ((vs.subtype fun v => ∀ i : AtomArena.Row rs, (rs.get i).lhs ≠ v).items.map
    fun v => tautology v.val)

theorem withIdleRows_holds [DecidableEq ν] (vs : Listing ν) (rs : List (IntAtom ν)) (x : ν → ℤ) :
    IntegerAtoms.RowsHold (withIdleRows vs rs) x ↔ IntegerAtoms.RowsHold rs x := by
  simp only [withIdleRows, IntegerAtoms.RowsHold, List.forall_mem_append, List.forall_mem_map]
  apply and_iff_left
  intro v _
  exact ⟨(v.val,0), by simp [tautology], by simp [tautology]⟩

theorem withIdleRows_has_left [DecidableEq ν] (vs : Listing ν) (rs : List (IntAtom ν)) (v : ν) :
    ∃ row ∈ withIdleRows vs rs, row.lhs = v := by
  by_cases used : ∃ i : AtomArena.Row rs, (rs.get i).lhs = v
  · obtain ⟨i,hi⟩ := used
    exact ⟨rs.get i, List.mem_append_left _ (List.get_mem _ i), hi⟩
  · let idle := vs.subtype fun v => ∀ i : AtomArena.Row rs, (rs.get i).lhs ≠ v
    let t : AtomArena.Isolated rs := ⟨v, fun i hi => used ⟨i,hi⟩⟩
    exact ⟨tautology v, List.mem_append_right _ (List.mem_map.mpr ⟨t, idle.complete t,rfl⟩), rfl⟩

def namedListing (vs : Listing ν) : Listing (Named ν) :=
  vs.sum ⟨[true,false], by rintro (_ | _) <;> simp, by simp⟩

def HasTerms (rs : List (IntAtom ν)) : Prop := ∀ row ∈ rs, 0 < row.terms.length

private theorem total_explicit [DecidableEq ν] (o : ν) (Q : ℕ) (vs : Listing ν)
    (body : List (IntAtom (Named ν))) (h : HasTerms body) :
    HasTerms (withIdleRows (namedListing vs) (intPins o Q ++ body)) := by
  intro row mem
  rcases List.mem_append.mp mem with named | taut
  · rcases List.mem_append.mp named with pin | old
    · simp only [intPins, List.mem_cons, List.not_mem_nil, or_false] at pin
      rcases pin with rfl | rfl | rfl | rfl <;> simp
    · exact h row old
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp taut
    simp [tautology]

def arena [Nonempty ν] (rs : List (IntAtom ν)) (h : HasTerms rs) :=
  AtomArena.game rs (fun i => h _ (List.get_mem _ i))

theorem arena_iff_feasible [Fintype ν] [Nonempty ν] (rs : List (IntAtom ν)) (h : HasTerms rs) :
    (arena rs h).Nonnegative none ↔ ∃ x, IntegerAtoms.RowsHold rs x :=
  ((arena rs h).nonnegative_iff_certificate none).trans (AtomArena.rows_iff_certificate _).symm

/-- Substitution on integer rows permits mixed spellings, for example
retaining the literal upper box while naming Lose in a successor list. -/
def intCollapse (o : ν) (Q : ℕ) : Named ν → ν × ℤ
  | .inl v => (v,0)
  | .inr true => (o,0)
  | .inr false => (o,Q)

def eliminateInt (o : ν) (Q : ℕ) (r : IntAtom (Named ν)) : IntAtom ν :=
  let l := intCollapse o Q r.lhs
  ⟨l.1, r.terms.map (fun t =>
    let z := intCollapse o Q t.1
    (z.1, z.2 + t.2 - l.2))⟩

private theorem collapse_scaled (o : ν) (Q : ℕ) (v : Named ν) :
    (collapse o v).1 = (intCollapse o Q v).1 ∧
      ((intCollapse o Q v).2 : ℚ) = (Q : ℚ) * (collapse o v).2 := by
  rcases v with i | (_ | _) <;> simp [collapse, intCollapse]

/-- Substituting the pinned terminals commutes with scaling: the
substituted offsets change by integral multiples of the scale. -/
theorem encode_eliminate (o : ν) (Q : ℕ) (body : List (Atom (Named ν))) :
    encodeAt Q (body.map (eliminate o)) = (encodeAt Q body).map (eliminateInt o Q) := by
  simp only [encodeAt, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro a _
  have hl := collapse_scaled o Q a.lhs
  simp only [integerAtom, eliminate, fromSignals, collapseSignal, eliminateInt, List.map_map,
    Function.comp_def]
  rw [hl.1]
  congr 1
  apply List.map_congr_left
  intro t _
  have hr := collapse_scaled o Q t.1
  rw [hr.1]
  congr 1
  have offsets :
      (Q : ℚ) * ((collapse o t.1).2 + t.2 - (collapse o a.lhs).2) =
        (Q : ℚ) * t.2 + (((intCollapse o Q t.1).2 - (intCollapse o Q a.lhs).2 : ℤ) : ℚ) := by
    rw [Int.cast_sub, hr.2, hl.2]
    ring
  rw [offsets, Int.floor_add_intCast]
  omega

private theorem int_eval (o : ν) (Q : ℕ) (x : ν → ℤ) (i : Named ν) :
    x (intCollapse o Q i).1 + (intCollapse o Q i).2 = extend o (Q : ℤ) x i := by
  rcases i with i | (_ | _) <;> simp [intCollapse,extend]

theorem eliminateInt_hold (o : ν) (Q : ℕ) (x : ν → ℤ) (r : IntAtom (Named ν)) :
    (eliminateInt o Q r).Holds x ↔ r.Holds (extend o (Q : ℤ) x) := by
  simp only [eliminateInt, IntAtom.Holds, List.mem_map, exists_exists_and_eq_and]
  apply exists_congr; intro t
  apply and_congr_right; intro _
  rw [← int_eval o Q x r.lhs, ← int_eval o Q x t.1]
  omega

theorem explicit_integer_iff (o : ν) (Q : ℕ) (body : List (IntAtom (Named ν))) :
    (∃ y, IntegerAtoms.RowsHold (intPins o Q ++ body) y) ↔
      ∃ x, IntegerAtoms.RowsHold (body.map (eliminateInt o Q)) x := by
  constructor
  · rintro ⟨y, h⟩
    have pin := (intPins_iff o Q y).mp (fun a ha => h a (List.mem_append_left _ ha))
    refine ⟨fun i => y (.inl i), fun a ha => ?_⟩
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
    rw [eliminateInt_hold, extend_restrict o _ y pin]
    exact h _ (List.mem_append_right _ hr)
  · rintro ⟨x,h⟩
    refine ⟨extend o (Q : ℤ) x, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with pin | inner
    · exact (intPins_iff o Q _).mpr (extend_pinned o _ x) a pin
    · exact (eliminateInt_hold o Q x a).mp (h _ (List.mem_map.mpr ⟨a,inner,rfl⟩))

/-- A named body whose substitution gives the compiled integer rows yields
a valid table with the same threshold answer, for either owner setting. -/
theorem explicit_table_checked [DecidableEq ν] [Fintype ν] [Nonempty ν]
    (o : ν) (Q : ℕ) (vs : Listing ν) (body : List (IntAtom (Named ν)))
    (rs : List (IntAtom ν)) (substitution : body.map (eliminateInt o Q) = rs)
    (hr : HasTerms rs) (swap : Bool) :
    let paper := table (namedListing vs) (withIdleRows (namedListing vs) (intPins o Q ++ body)) swap
    paper.Valid ∧ (paper.Nonnegative ↔ (table vs rs swap).Nonnegative) := by
  have hp := total_explicit o Q vs body (fun r hr' => by
    have mem : eliminateInt o Q r ∈ rs := substitution ▸ List.mem_map.mpr ⟨r,hr',rfl⟩
    simpa [eliminateInt] using hr _ mem)
  let explicit := arena _ hp
  let compact := arena _ hr
  have same : explicit.Nonnegative none ↔ compact.Nonnegative none := by
    rw [show explicit = arena _ hp from rfl, show compact = arena _ hr from rfl,
      arena_iff_feasible, arena_iff_feasible]
    simp only [withIdleRows_holds, explicit_integer_iff, substitution]
  refine ⟨(table_represents _ _ (fun i => hp _ (List.get_mem _ i)) swap).valid, ?_⟩
  rw [table_nonnegative_iff _ _ (fun i => hp _ (List.get_mem _ i)),
    table_nonnegative_iff _ _ (fun i => hr _ (List.get_mem _ i))]
  cases swap
  · exact same
  · exact (explicit.swap_nonnegative_iff none).trans
      ((not_congr same).trans (compact.swap_nonnegative_iff none).symm)

end StochasticGames.ArenaRepresentation
