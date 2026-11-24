module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Ring.Int

/-! # Integer-weighted turn-based arenas and positional certificates -/

@[expose] public section

namespace StochasticGames.MeanPayoff

structure Game (V E : Type*) where
  src : E → V
  dst : E → V
  weight : E → ℤ
  isMax : V → Bool
  outgoing : ∀ v, ∃ e, src e = v

namespace Game

variable {V E : Type*} (G : Game V E)

abbrev Move (v : V) := {e : E // G.src e = v}

abbrev Policy := (v : V) → G.Move v

def Allowed (p : G.Policy) (e : E) : Prop :=
  G.isMax (G.src e) = true → e = (p (G.src e)).val

def Swap [Fintype V] : Game V E where
  src := G.src
  dst := G.dst
  weight e := -(Fintype.card V : ℤ) * G.weight e - 1
  isMax v := !(G.isMax v)
  outgoing := G.outgoing

/-- A positional strategy keeps play in a region and bounds from below the
total weight of every finite prefix there by a difference of potentials. -/
def Certificate (s : V) : Prop :=
  ∃ (p : G.Policy) (R : V → Prop) (x : V → ℤ), R s ∧
    ∀ e, G.Allowed p e → R (G.src e) →
      R (G.dst e) ∧ x (G.src e) ≤ G.weight e + x (G.dst e)

end Game
end StochasticGames.MeanPayoff
