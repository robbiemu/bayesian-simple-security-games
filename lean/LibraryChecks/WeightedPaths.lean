module

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-! Directed paths sum rational affine costs. Parallel edges can carry different costs. -/

open Quiver

variable {V : Type*} [Quiver V] {a b c : V}

example (e : a ⟶ b) (f : b ⟶ c) : (e.toPath.comp f.toPath).length = 2 := rfl

example (cost : ∀ {u v : V}, (u ⟶ v) → (ℚ →ᵃ[ℚ] ℚ)) (p : Path a b) (q : Path b c) :
    (p.comp q).addWeight cost = p.addWeight cost + q.addWeight cost :=
  Path.addWeight_comp cost p q
