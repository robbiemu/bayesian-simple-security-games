module

public import Kintali.QuoteSearch.RunBounds
public import StochasticGames.CompilerRun

/-! # Updating a blocking interval in the compressed table -/

@[expose] public section

namespace Kintali.QuoteSearch.Runs

open StochasticGames StochasticGames.CompilerRun

def splitWork (cut : ℕ) : List WeightRun → Run (List WeightRun × List WeightRun)
  | [] => step 0 ([], [])
  | r :: rs => do
    let zero ← step cut.size (cut == 0)
    if zero then
      step 0 ([], r :: rs)
    else
      let width := max cut.size r.length.size
      let internal ← step width (cut < r.length : Bool)
      if internal then
        let rest ← natSub r.length cut
        step 0 ([⟨cut, r.doublings⟩], ⟨rest, r.doublings⟩ :: rs)
      else
        let next ← natSub cut r.length
        let (before, after) ← splitWork next rs
        step 0 (r :: before, after)

@[simp] theorem splitWork_value (cut : ℕ) (rs : List WeightRun) :
    (splitWork cut rs).value = splitAt cut rs := by
  induction rs generalizing cut with
  | nil => rfl
  | cons r rs ih =>
    by_cases zero : cut = 0
    · simp [splitWork, splitAt, zero]
    · by_cases internal : cut < r.length <;>
        simp [splitWork, splitAt, zero, internal, natSub, ih]

theorem splitWork_bound (cut : ℕ) (rs : List WeightRun) {W : ℕ}
    (hcut : cut.size ≤ W) (count : (quoteCount rs).size ≤ W) :
    (splitWork cut rs).Bound (1 + 4 * rs.length) W := by
  induction rs generalizing cut with
  | nil => simp [splitWork, Run.Bound]
  | cons r rs ih =>
    have hlen := (Nat.size_le_size (length_le_count (r := r) (by simp : r ∈ r :: rs))).trans count
    have htail := (Nat.size_le_size (Nat.le_add_left (quoteCount rs) r.length)).trans count
    by_cases zero : cut = 0
    · simp [splitWork, zero, Run.Bound]
      omega
    · by_cases internal : cut < r.length
      · constructor
        · simp [splitWork, zero, internal, natSub]
          omega
        · simp [splitWork, zero, internal, natSub, max_le_iff, hcut, hlen]
      · have next := (Nat.size_le_size (Nat.sub_le cut r.length)).trans hcut
        obtain ⟨slots,width⟩ := ih (cut-r.length) next htail
        constructor
        · simp [splitWork, zero, internal, natSub]
          omega
        · simp [splitWork, zero, internal, natSub, max_le_iff, hcut, hlen, width]

private theorem split_counts (cut : ℕ) (rs : List WeightRun) :
    quoteCount (splitAt cut rs).1 ≤ quoteCount rs ∧ quoteCount (splitAt cut rs).2 ≤ quoteCount rs := by
  obtain ⟨am, bm⟩ := Prod.mk.inj (expand_splitAt cut rs)
  constructor
  · rw [← expand_length (splitAt cut rs).1, am, List.length_take, expand_length]
    exact Nat.min_le_right _ _
  · rw [← expand_length (splitAt cut rs).2, bm, List.length_drop, expand_length]
    exact Nat.sub_le _ _

def raiseWork (rs : List WeightRun) : Run (List WeightRun) :=
  CompilerRun.mapM (fun r => do
    let exponent ← natAdd r.doublings 1
    step 0 {r with doublings := exponent}) rs

@[simp] theorem raiseWork_value (rs : List WeightRun) : (raiseWork rs).value = raise rs := by
  simp [raiseWork, raise, natAdd]

theorem raiseWork_bound (rs : List WeightRun) {W : ℕ}
    (h : ∀ r ∈ rs, r.doublings.size ≤ W) (w : 1 ≤ W) :
    (raiseWork rs).Bound (1 + 4 * rs.length) W := by
  have each (r : WeightRun) (hr : r ∈ rs) :
      (natAdd r.doublings 1 >>= fun e => step 0 {r with doublings := e}).Bound 2 W :=
    ⟨le_rfl, max_le (max_le (h r hr) w) (Nat.zero_le _)⟩
  exact (mapM_bound _ _ _ _ each).weaken (by omega) le_rfl

def updateWork (lo hi : ℕ) (rs : List WeightRun) : Run (List WeightRun) := do
  let empty ← step (max lo.size hi.size) (hi ≤ lo : Bool)
  if empty then
    step 0 rs
  else
    let (pre, rest) ← splitWork lo rs
    let span ← natSub hi lo
    let (inside, post) ← splitWork span rest
    let raised ← raiseWork inside
    let tail ← CompilerRun.append raised post
    CompilerRun.append pre tail

@[simp] theorem updateWork_value (lo hi : ℕ) (rs : List WeightRun) :
    (updateWork lo hi rs).value = doubleInterval lo hi rs := by
  by_cases h : hi ≤ lo
  · simp [updateWork, doubleInterval, h]
  · cases ha : splitAt lo rs with
    | mk pre rest =>
      cases hb : splitAt (hi-lo) rest with
      | mk inside post => simp [updateWork, doubleInterval, h, natSub, ha, hb]

theorem updateWork_bound (lo hi : ℕ) (rs : List WeightRun) {t W : ℕ}
    (hlo : lo.size ≤ W) (hhi : hi.size ≤ W) (count : (quoteCount rs).size ≤ W)
    (exponents : ∀ r ∈ rs, r.doublings ≤ t) (hW : t + 1 ≤ W) :
    (updateWork lo hi rs).Bound (32 * (rs.length + 1)) W := by
  by_cases empty : hi ≤ lo
  · constructor
    · simp [updateWork, empty]
      omega
    · simp [updateWork, empty, max_le_iff, hlo, hhi]
  let pre := (splitAt lo rs).1
  let rest := (splitAt lo rs).2
  let inside := (splitAt (hi-lo) rest).1
  let post := (splitAt (hi-lo) rest).2
  have hloCut := splitWork_bound lo rs hlo count
  have hsize := (Nat.size_le_size (Nat.sub_le hi lo)).trans hhi
  have restCnt := (Nat.size_le_size (split_counts lo rs).2).trans count
  have hhiCut := splitWork_bound (hi-lo) rest hsize restCnt
  have expo := (splitAt_exponents rest (hi-lo) t (splitAt_exponents rs lo t exponents).2).1
  have incr := raiseWork_bound inside
    (fun r hr => (StochasticGames.BinarySize.size_le_self r.doublings).trans
      ((expo r hr).trans (show t ≤ W by omega))) (by omega)
  have hpLen : pre.length + rest.length ≤ rs.length + 1 := splitAt_count lo rs
  have hiLen : inside.length + post.length ≤ rest.length + 1 := splitAt_count (hi-lo) rest
  have raisedLen : (raiseWork inside).value.length = inside.length := by simp [raise]
  have ctail := append_bound (raiseWork inside).value post W
  have cfull := append_bound pre (CompilerRun.append (raiseWork inside).value post).value W
  have eq₁ : (splitWork lo rs).value = (pre,rest) := by simp [pre, rest]
  have eq₂ : (splitWork (hi-lo) rest).value = (inside,post) := by simp [inside, post]
  constructor
  · simp only [updateWork, Run.bind_slots, step_value, step_slots, empty,
      decide_false, Bool.false_eq_true, ite_false, eq₁, eq₂, natSub]
    have s₁ := hloCut.1
    have s₂ := hhiCut.1
    have s₃ := incr.1
    have s₄ := ctail.1
    have s₅ := cfull.1
    rw [raisedLen] at s₄
    omega
  · simp only [updateWork, Run.bind_width, step_value, step_width, empty,
      decide_false, Bool.false_eq_true, ite_false, eq₁, eq₂, natSub, max_le_iff]
    exact ⟨⟨hlo,hhi⟩, hloCut.2, ⟨hhi,hlo⟩, hhiCut.2, incr.2, ctail.2, cfull.2⟩

end Kintali.QuoteSearch.Runs
