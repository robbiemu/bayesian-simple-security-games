module

public import Kintali.InputOutput.CodecWork
import Kintali.LinearProgramming.Bounds

/-! # Input size after decoding a possibly noncanonical bitstream

Reading unsigned digits can increase a field's digit length by one. Rational
normalization reduces both parts when the denominator is nonzero. Delimited
products and lists preserve the resulting common multiplicative bound.
-/

@[expose] public section

namespace Kintali.InputOutput.CodecWork

open Binary

private def Reencode {α : Type} (c : Codec α) : Prop :=
  ∀ bits x, c.decode bits = some x → (c.encode x).length ≤ 13*bits.length

private theorem nat_reencode : Reencode natCodec := by
  intro bits n h
  change (Computability.encodeNat n).length ≤ _
  rw [length_nat]
  cases bits with
  | nil => change some 0 = some n at h; cases h; decide
  | cons b bs =>
    have w := number_width h
    simp only [List.length_cons] at *
    omega

private theorem fields {α β : Type} {a : Codec α} {b : Codec β} {xs : Stream} {x : α} {y : β}
    (h : (pairCodec a b).decode xs = some (x,y)) :
    ∃ f t : Stream, splitBlock xs = some (f,t) ∧ a.decode f = some x ∧ b.decode t = some y := by
  change (Option.bind (splitBlock xs) _) = _ at h
  obtain ⟨⟨f,t⟩,hs,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨x',hx,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y',hy,h⟩ := Option.bind_eq_some_iff.mp h
  cases h
  exact ⟨f,t,hs,hx,hy⟩

private theorem pair_reencode {α β : Type} {a : Codec α} {b : Codec β}
    (A : Reencode a) (B : Reencode b) : Reencode (pairCodec a b) := by
  rintro xs ⟨x,y⟩ h
  obtain ⟨f,t,hs,hx,hy⟩ := fields h
  have len := split_lengths hs
  have left := A _ _ hx
  have right := B _ _ hy
  change (pair a.encode b.encode (x,y)).length ≤ _
  rw [length_pair]
  dsimp only
  omega

private theorem many_reencode {α : Type} {a : Codec α} (A : Reencode a) (fuel : ℕ)
    (bits : Stream) (xs : List α) (ok : readMany a fuel bits = some xs) :
    (many a.encode xs).length ≤ 13*bits.length := by
  induction fuel generalizing bits xs with
  | zero => cases bits <;> cases ok; rfl
  | succ k ih =>
    cases bits with
    | nil => cases ok; rfl
    | cons b bs =>
      change Option.bind (splitBlock (b::bs)) _ = _ at ok
      obtain ⟨⟨f,t⟩,hs,ok⟩ := Option.bind_eq_some_iff.mp ok
      obtain ⟨x,hx,ok⟩ := Option.bind_eq_some_iff.mp ok
      obtain ⟨rest,hr,ok⟩ := Option.bind_eq_some_iff.mp ok
      cases ok
      have len := split_lengths hs
      have first := A _ _ hx
      have tail := ih t rest hr
      change (block (a.encode x) ++ many a.encode rest).length ≤ _
      rw [List.length_append,length_block]
      omega

private theorem list_reencode {α : Type} {a : Codec α} (A : Reencode a) :
    Reencode (listCodec a) := fun bits xs ok => many_reencode A bits.length bits xs ok

private theorem rat_reencode : Reencode ratCodec := by
  intro bits q h
  change Option.map _ ((pairCodec intCodec natCodec).decode bits) = some q at h
  obtain ⟨⟨z,d⟩,ok,rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨f,t,hs,hz,hd⟩ := fields ok
  have len := split_lengths hs
  have zw := integer_width hz
  have dw := number_width hd
  change (rational ((z : ℚ)/d)).length ≤ _
  by_cases zero : d = 0
  · subst d
    simp only [Nat.cast_zero,div_zero]
    have one : (rational 0).length = 4 := by decide
    omega
  · have reduced := LinearProgramming.divInt_parts_le z (d : ℤ) (by exact_mod_cast zero)
    rw [Rat.divInt_eq_div] at reduced
    simp only [Int.natAbs_natCast,Int.cast_natCast] at reduced
    have num := Nat.size_le_size reduced.1
    have den := Nat.size_le_size reduced.2
    exact (rational_width (hn := num.trans (by omega : z.natAbs.size ≤ bits.length+1))
      (hd := den.trans (by omega : d.size ≤ bits.length+1))).trans (by omega)

/-- Canonical encoding of a successful parse uses at most thirteen times the
supplied stream length. The decoder accepts noncanonical digits and ratios. -/
theorem reencode_length {bits : Stream} {a : Input} (h : inputCodec.decode bits = some a) :
    lengthInput a ≤ 13*bits.length :=
  pair_reencode nat_reencode (pair_reencode (list_reencode (pair_reencode rat_reencode rat_reencode))
    (list_reencode (pair_reencode rat_reencode (list_reencode (pair_reencode rat_reencode rat_reencode))))) bits a h

end Kintali.InputOutput.CodecWork
