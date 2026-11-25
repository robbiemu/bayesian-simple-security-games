module

public import Kintali.QuoteSearch.QuantileWork

/-! # Slot and word bounds for selecting every quantile of one pair -/

@[expose] public section

namespace Kintali.QuoteSearch.Runs

open StochasticGames StochasticGames.CompilerRun

private theorem map_range (f : ℕ → ℕ) (n : ℕ) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Fin.val_zero, Fin.val_succ,
      List.cons.injEq, true_and]
    exact ih (fun i => f (i+1))

def selectedWork (rs : List WeightRun) (J : ℕ) : Run (List ℕ) := do
  let v ← totalWork rs
  let empty ← step v.size (v == 0)
  if empty then
    step 0 []
  else
    let count ← natSub J 1
    let ix ← finRange count
    CompilerRun.mapM (fun a => do
      let rank ← natAdd a.val 1
      quantileWork rs J rank) ix

@[simp] theorem selectedWork_value (rs : List WeightRun) (J : ℕ) :
    (selectedWork rs J).value = selected rs J := by
  by_cases h : weight rs = 0
  · simp [selectedWork, selected, h]
  · simp [selectedWork, selected, h, natAdd, natSub]
    exact map_range (fun a => quantile rs J (a+1)) (J-1)

def selectionSlots (N J t : ℕ) : ℕ := 8 + N * (4 + 2*t) + J * (15 + N * (11 + 4*t))

theorem selectedWork_bound (rs : List WeightRun) (J : ℕ) {t W : ℕ}
    (h : ∀ r ∈ rs, r.doublings ≤ t) (count : (quoteCount rs+1).size ≤ W)
    (weights : (weight rs).size + J.size + 1 ≤ W) (wide : t+2 ≤ W) :
    (selectedWork rs J).Bound (selectionSlots rs.length J t) W := by
  have wJ : J.size ≤ W := by omega
  have wV : (weight rs).size ≤ W := by omega
  have w1 : (1 : ℕ).size ≤ W := by change 1 ≤ W; omega
  have tot := totalWork_bound rs h
    ((Nat.size_le_size (Nat.le_succ (quoteCount rs))).trans count) wV wide
  unfold selectionSlots
  by_cases hzero : weight rs = 0
  · obtain ⟨slot,width⟩ := tot
    constructor
    · simp [selectedWork, hzero]
      omega
    · simp [selectedWork, hzero, width]
  · have wr : (J-1).size ≤ W := (Nat.size_le_size (Nat.sub_le J 1)).trans wJ
    have ids := (finRange_bound (J-1)).weaken le_rfl wr
    let find (a : Fin (J-1)) := natAdd a.val 1 >>= quantileWork rs J
    have each (a : Fin (J-1)) : (find a).Bound (9 + rs.length * (11 + 4*t)) W := by
      have s : a.val+1 ≤ J := by have hs := a.isLt; omega
      have sw := Nat.size_le_size s
      have aw := (Nat.size_le_size (show a.val ≤ J by omega)).trans wJ
      have work := quantileWork_bound rs J (a.val+1) h count (by omega) wJ wide
      constructor
      · change 1 + (quantileWork rs J (a.val+1)).work.slots ≤ _
        have := work.1
        omega
      · exact max_le (max_le aw w1) work.2
    have search := mapM_bound find (List.finRange (J-1))
      (9 + rs.length * (11 + 4*t)) W (fun a _ => each a)
    have hslots := search.1
    simp only [List.length_finRange] at hslots
    have mult := Nat.mul_le_mul_right (9+rs.length*(11+4*t)+2) (Nat.sub_le J 1)
    obtain ⟨iSlots,iWidth⟩ := ids
    obtain ⟨tSlots,tWidth⟩ := tot
    have prod : J*(15+rs.length*(11+4*t)) = J*4 + J*(9+rs.length*(11+4*t)+2) := by ring
    constructor
    · simp only [selectedWork, Run.bind_slots, step_slots, step_value, totalWork_value, hzero,
        beq_iff_eq, ite_false, natSub, finRange_value]
      change (totalWork rs).work.slots + (1 + (1 + ((finRange (J-1)).work.slots +
        (CompilerRun.mapM find (List.finRange (J-1))).work.slots))) ≤ _
      rw [prod]
      omega
    · simp only [selectedWork, Run.bind_width, step_width, step_value, totalWork_value, hzero,
        beq_iff_eq, ite_false, natSub, finRange_value, max_le_iff]
      exact ⟨tWidth,wV,⟨wJ,w1⟩,iWidth,search.2⟩

end Kintali.QuoteSearch.Runs
