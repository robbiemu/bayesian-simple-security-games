module

public import StochasticGames.ArenaEncoding
import all StochasticGames.ArenaEncoding
import all StochasticGames.MeanPayoffGame
import Mathlib.Data.Fintype.Basic

/-! The terminal and out-of-range cases emit a single weighted loop. -/

@[expose] public section
namespace StochasticGames.TrivialThreshold

open ArenaEncoding MeanPayoff

def loop (accept : Bool) : Table :=
  ⟨0, [false], [⟨0, 0, if accept then 0 else -1⟩]⟩

private def arena (accept : Bool) : Game Unit Unit where
  src _ := ()
  dst _ := ()
  weight _ := if accept then 0 else -1
  isMax _ := false
  outgoing _ := ⟨(), rfl⟩

private def unitIndex : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by
    apply Fin.ext
    have h := i.isLt
    change 0 = i.val
    omega

private theorem loop_represents (accept : Bool) : (loop accept).Represents (arena accept) () :=
  ⟨unitIndex, unitIndex, rfl, fun _ => rfl, fun _ => rfl⟩

theorem loop_valid (accept : Bool) : (loop accept).Valid :=
  (loop_represents accept).valid

theorem loop_nonnegative_iff (accept : Bool) :
    (loop accept).Nonnegative ↔ accept = true := by
  rw [(loop_represents accept).nonnegative_iff, Game.nonnegative_iff_certificate]
  cases accept
  · simp only [Bool.false_eq_true, iff_false]
    rintro ⟨policy, region, h, start, stable⟩
    have allowed : (arena false).Allowed policy () := by simp [Game.Allowed, arena]
    have le := (stable () allowed start).2
    change h () ≤ -1 + h () at le
    omega
  · simp only [iff_true]
    refine ⟨fun _ => ⟨(), rfl⟩, fun _ => True, fun _ => 0, trivial, ?_⟩
    simp [arena]

end StochasticGames.TrivialThreshold
