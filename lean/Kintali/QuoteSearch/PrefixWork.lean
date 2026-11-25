module

public import Kintali.QuoteSearch.BlockingInterval
public import StochasticGames.CompilerRun

/-! # The work of a compressed interval query

The comparison oracle is charged at the midpoint requested by the
search. This separates the binary search from the arithmetic and
rank comparisons used by a particular market.
-/

@[expose] public section

namespace Kintali.QuoteSearch.PrefixWork

open StochasticGames.CompilerRun

variable (accepts : ℕ → Run Bool)

def search : ℕ → ℕ → ℕ → Run ℕ
  | 0, lo, _ => step 0 lo
  | fuel + 1, lo, hi => do
    let done ← step (max lo.size hi.size) (hi ≤ lo : Bool)
    if done then Run.ret lo else
      let delta ← natSub hi lo
      let half ← step (max delta.size 2) (delta / 2)
      let mid ← natAdd lo half
      let accepted ← accepts mid
      let right ← step 0 accepted
      if right then
        let start ← natAdd mid 1
        search fuel start hi
      else
        search fuel lo mid

theorem search_value (fuel lo hi : ℕ) :
    (search accepts fuel lo hi).value = locate (fun q => (accepts q).value) fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    by_cases h : hi ≤ lo
    · simp [search, locate, h, Run.ret]
    · cases ha : (accepts (lo + (hi - lo) / 2)).value <;>
        simp [search, locate, h, ha, ih, natAdd, natSub]

theorem search_bound {limit calls width : ℕ} (fuel lo hi : ℕ)
    (hlo : lo ≤ limit) (hhi : hi ≤ limit)
    (indexWidth : limit.size ≤ width) (smallWidth : 2 ≤ width)
    (hAccept : ∀ q < limit, (accepts q).Bound calls width) :
    (search accepts fuel lo hi).Bound (1 + fuel * (calls + 6)) width := by
  induction fuel generalizing lo hi with
  | zero => simp [search, Run.Bound]
  | succ fuel ih =>
    have wlo := (Nat.size_le_size hlo).trans indexWidth
    have whi := (Nat.size_le_size hhi).trans indexWidth
    by_cases h : hi ≤ lo
    · constructor
      · simp [search, h, Run.ret, Work.empty]
      · simpa [search, h, Run.ret, Work.empty, max_le_iff] using And.intro wlo whi
    · let mid := lo + (hi - lo) / 2
      have mid_lt : mid < hi := by dsimp [mid]; omega
      have delta := (Nat.size_le_size (show hi - lo ≤ limit by omega)).trans indexWidth
      have half := (Nat.size_le_size (show (hi - lo) / 2 ≤ limit by omega)).trans indexWidth
      have wmid := (Nat.size_le_size (mid_lt.le.trans hhi)).trans indexWidth
      have wone : (1 : ℕ).size ≤ width := by change 1 ≤ width; omega
      have ha := hAccept mid (mid_lt.trans_le hhi)
      cases hr : (accepts (lo + (hi - lo) / 2)).value with
      | false =>
        have previous := ih lo mid hlo (mid_lt.le.trans hhi)
        obtain ⟨hslots, hwidth⟩ := previous
        obtain ⟨aslots, awidth⟩ := ha
        dsimp only [mid] at hslots hwidth aslots awidth wmid
        constructor
        · simp only [search, step_value, decide_eq_false h, Bool.false_eq_true, ite_false,
            Run.bind_slots, step_slots, natSub, natAdd, hr]
          rw [Nat.succ_mul]
          omega
        · simp only [search, step_value, decide_eq_false h, Bool.false_eq_true, ite_false,
            Run.bind_width, step_width, natSub, natAdd, hr, max_le_iff]
          aesop
      | true =>
        have previous := ih (mid+1) hi (Nat.succ_le_of_lt mid_lt |>.trans hhi) hhi
        obtain ⟨hslots, hwidth⟩ := previous
        obtain ⟨aslots, awidth⟩ := ha
        dsimp only [mid] at hslots hwidth aslots awidth wmid
        constructor
        · simp only [search, step_value, decide_eq_false h, Bool.false_eq_true, ite_false,
            Run.bind_slots, step_slots, natSub, natAdd, hr, ite_true]
          rw [Nat.succ_mul]
          omega
        · simp only [search, step_value, decide_eq_false h, Bool.false_eq_true, ite_false,
            Run.bind_width, step_width, natSub, natAdd, hr, ite_true, max_le_iff]
          aesop

def findPrefix (quotes : ℕ) : Run ℕ :=
  search accepts (quotes.log2 + 1) 0 quotes

@[simp] theorem prefix_value (quotes : ℕ) :
    (findPrefix accepts quotes).value = prefixLength (fun q => (accepts q).value) quotes :=
  search_value ..

theorem prefix_bound (quotes calls width : ℕ) (w : quotes.size ≤ width) (small : 2 ≤ width)
    (each : ∀ q < quotes, (accepts q).Bound calls width) :
    (findPrefix accepts quotes).Bound (1 + (quotes.log2+1) * (calls+6)) width :=
  search_bound accepts _ _ _ (Nat.zero_le _) le_rfl w small each

end Kintali.QuoteSearch.PrefixWork
