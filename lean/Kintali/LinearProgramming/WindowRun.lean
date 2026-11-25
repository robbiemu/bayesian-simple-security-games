module

public import Kintali.LinearProgramming.ScalarRun

/-! # Integer implementation of the slack-window search

For a positive input denominator D and inverse precision Q, a slack s is
stored as the integer Z = D Q s. The endpoints tested against it are
D K^l and D K^(l+1). The run tabulates those endpoints once and returns a
stored mask for the pivot search.
-/

@[expose] public section

namespace Kintali.LinearProgramming.WindowRun

open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {m : ℕ}

private theorem get_ofFn {α : Type} {d : ℕ} (f : Fin d → α) (i : Fin d) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = _
  simp

def endpoints (m D K : ℕ) : Run (Vector ℕ (m+2)) :=
  ArithmeticRun.tabulate (m+2) fun l => do
    let p ← ScalarRun.power K l.val
    natMul D p

@[simp] theorem endpoints_value (m D K : ℕ) :
    (endpoints m D K).value = Vector.ofFn (fun l : Fin (m+2) => D * K^l.val) := by
  simp [endpoints, natMul]

/-- Two signed comparisons, the data and index reads, and packaging the
successful index use six primitive word transitions. -/
def obstacle (z : Vector ℤ m) (a b : ℕ) (i : Fin m) : Run (Option (Fin m)) :=
  let v := z[i.val]
  ⟨if (a : ℤ) < v ∧ v ≤ (b : ℤ) then some i else none,
    ⟨6, max m.size (max v.natAbs.size (max a.size b.size)+1)⟩⟩

def empty (rows : List (Fin m)) (z : Vector ℤ m) (bounds : Vector ℕ (m+2)) (l : Fin (m+1)) :
    Run (Option (Fin (m+1))) := do
  let a ← step (m+2).size (bounds.get l.castSucc)
  let b ← step (m+2).size (bounds.get l.succ)
  let bad ← ArithmeticRun.first (obstacle z a b) rows
  step 0 (if bad.isNone then some l else none)

def index (z : Vector ℤ m) (bounds : Vector ℕ (m+2)) : Run (Fin (m+1)) := do
  let rows ← finRange m
  let labels ← finRange (m+1)
  let found ← ArithmeticRun.first (empty rows z bounds) labels
  step (m+1).size (found.getD 0)

def mark (z : Vector ℤ m) (D K : ℕ) : Run (Vector Bool m) := do
  let table ← endpoints m D K
  let selected ← index z table
  let a ← step (m+2).size (table.get selected.castSucc)
  ArithmeticRun.tabulate m fun i =>
    ⟨decide (z[i.val].natAbs ≤ a), ⟨3, max m.size (max z[i.val].natAbs.size a.size+1)⟩⟩

def noObstacle (z : Vector ℤ m) (bounds : Vector ℕ (m+2)) (l : Fin (m+1)) : Prop :=
  ∀ i : Fin m, ¬ (((bounds.get l.castSucc) : ℤ) < z[i.val] ∧ z[i.val] ≤ ((bounds.get l.succ) : ℤ))

instance (z : Vector ℤ m) (bounds : Vector ℕ (m+2)) (l : Fin (m+1)) :
    Decidable (noObstacle z bounds l) := by unfold noObstacle; infer_instance

private theorem empty_value (z : Vector ℤ m) (bounds : Vector ℕ (m+2)) (l : Fin (m+1)) :
    (empty (List.finRange m) z bounds l).value =
      Option.guard (fun l => decide (noObstacle z bounds l)) l := by
  let bad := (ArithmeticRun.first (obstacle z (bounds.get l.castSucc) (bounds.get l.succ)) (List.finRange m)).value
  have iff : bad = none ↔ noObstacle z bounds l := by
    unfold bad noObstacle
    rw [ArithmeticRun.first_value, List.findSome?_eq_none_iff]
    simp [obstacle]
  change (if bad.isNone then some l else none) = _
  by_cases h : noObstacle z bounds l
  · simp [iff.mpr h, Option.guard, h]
  · have hn := mt iff.mp h
    cases hb : bad with
    | none => exact (hn hb).elim
    | some i => simp [Option.guard, h]

theorem index_value (z : Vector ℤ m) (bounds : Vector ℕ (m+2)) :
    (index z bounds).value =
      ((List.finRange (m+1)).find? (fun l => decide (noObstacle z bounds l))).getD 0 := by
  simp only [index, Run.bind_value, finRange_value, ArithmeticRun.first_value, empty_value,
    List.findSome?_guard, step_value]

theorem mark_value (z : Vector ℤ m) (D K Q : ℕ) (dpos : 0 < D) (qpos : 0 < Q)
    (s : Fin m → ℚ) (scaled : ∀ i : Fin m, (z[i.val] : ℚ) = (D : ℚ) * Q * s i) :
    (mark z D K).value = Vector.ofFn (fun i : Fin m =>
      decide (|s i| ≤ SlackWindow.lower (1 / (Q : ℚ)) K
        (SlackWindow.select s (1 / (Q : ℚ)) K))) := by
  let table := (endpoints m D K).value
  have pos : (0 : ℚ) < (D : ℚ)*Q := mul_pos (by exact_mod_cast dpos) (by exact_mod_cast qpos)
  have qnz : (Q : ℚ) ≠ 0 := by exact_mod_cast qpos.ne'
  have endpoint (l : Fin (m+2)) : ((table.get l) : ℚ) =
      ((D : ℚ)*Q) * SlackWindow.lower (1/(Q : ℚ)) K l.val := by
    simp [table, SlackWindow.lower, get_ofFn]
    field_simp
  have compare (l : Fin (m+1)) : noObstacle z table l ↔ SlackWindow.Empty s (1/(Q : ℚ)) K l := by
    apply forall_congr'
    intro i
    apply not_congr
    have left : (((table.get l.castSucc) : ℤ) < z[i.val]) ↔
        SlackWindow.lower (1/(Q : ℚ)) K l.val < s i := by
      rw [← Int.cast_lt (R := ℚ)]
      push_cast
      rw [endpoint l.castSucc, scaled i, mul_lt_mul_iff_right₀ pos]
      rfl
    have right : (z[i.val] ≤ ((table.get l.succ) : ℤ)) ↔
        s i ≤ SlackWindow.lower (1/(Q : ℚ)) K (l.val+1) := by
      rw [← Int.cast_le (R := ℚ)]
      push_cast
      rw [endpoint l.succ, scaled i, mul_le_mul_iff_right₀ pos]
      rfl
    exact and_congr left right
  have choose : (index z table).value = SlackWindow.select s (1/(Q : ℚ)) K := by
    rw [index_value]
    unfold SlackWindow.select
    congr 2
    funext l
    exact decide_eq_decide.mpr (compare l)
  let l := SlackWindow.select s (1/(Q : ℚ)) K
  have markI (i : Fin m) : (z[i.val].natAbs ≤ (table.get l.castSucc)) ↔
      |s i| ≤ SlackWindow.lower (1/(Q : ℚ)) K l.val := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, ← Int.cast_le (R := ℚ),
      Int.cast_abs, Int.cast_natCast, scaled i, abs_mul, abs_of_pos pos,
      endpoint l.castSucc, mul_le_mul_iff_right₀ pos]
    rfl
  simp only [mark, Run.bind_value, step_value, ArithmeticRun.tabulate_value]
  change Vector.ofFn (fun i : Fin m => decide (z[i.val].natAbs ≤ table.get (index z table).value.castSucc)) = _
  apply congrArg Vector.ofFn
  funext i
  have chosenEndpoint := congrArg (fun v : Fin (m+1) => table.get v.castSucc) choose
  change (table.get (index z table).value.castSucc) = table.get l.castSucc at chosenEndpoint
  rw [chosenEndpoint]
  exact decide_eq_decide.mpr (markI i)

theorem mark_work (z : Vector ℤ m) (D K L w : ℕ) (positive : 0 < K) (md : m+2 ≤ L)
    (idx : (m+2).size ≤ w) (Dfit : D.size ≤ w) (Kfit : K.size ≤ w)
    (powerFit : (K^(m+1)).size ≤ w) (hi : (D*K^(m+1)).size+1 ≤ w)
    (words : ∀ i : Fin m, z[i.val].natAbs.size+1 ≤ w) :
    (mark z D K).Bound (48*(L+2)^3) w := by
  let table := (endpoints m D K).value
  have i0 : m.size ≤ w := (Nat.size_le_size (by omega : m ≤ m+2)).trans idx
  have i1 : (m+1).size ≤ w := (Nat.size_le_size (by omega : m+1 ≤ m+2)).trans idx
  have ep (l : Fin (m+2)) : (table.get l).size+1 ≤ w := by
    simp only [table, endpoints_value, get_ofFn]
    have le := Nat.mul_le_mul_left D (Nat.pow_le_pow_right positive (by omega : l.val ≤ m+1))
    exact (Nat.add_le_add_right (Nat.size_le_size le) 1).trans hi
  have endpointCell (l : Fin (m+2)) :
      (ScalarRun.power K l.val >>= fun z => natMul D z).Bound (2+2*(m+1)) w := by
    have hn : l.val ≤ m+1 := by omega
    have a := ScalarRun.power_work K l.val (m+1) w hn positive i1 Kfit powerFit
    have q := (Nat.size_le_size (Nat.pow_le_pow_right positive hn)).trans powerFit
    have mul : (natMul D (ScalarRun.power K l.val).value).Bound 1 w := by
      exact ⟨le_rfl, max_le Dfit (by simpa using q)⟩
    exact (bound_bind (f := natMul D) a mul).weaken (by omega) le_rfl
  have endpointsWork := ArithmeticRun.tabulate_bound _ idx endpointCell
  have test (l : Fin (m+1)) (i : Fin m) :
      (obstacle z (table.get l.castSucc) (table.get l.succ) i).Bound 6 w := by
    have left := ep l.castSucc
    have right := ep l.succ
    have word := words i
    exact ⟨le_rfl, max_le i0 (by change max z[i.val].natAbs.size (max (table.get l.castSucc).size (table.get l.succ).size)+1 ≤ w; omega)⟩
  have emptyWork (l : Fin (m+1)) :
      (empty (List.finRange m) z table l).Bound (4+m*8) w := by
    have loop := ArithmeticRun.first_bound _ (test l) (List.finRange m)
    simp only [List.length_finRange] at loop
    constructor
    · simp only [empty, Run.bind_slots, step_slots, step_value]
      have hloop := loop.1
      omega
    · exact max_le idx (max_le idx (max_le loop.2 (Nat.zero_le w)))
  have selectWork := ArithmeticRun.first_bound _ emptyWork (List.finRange (m+1))
  simp only [List.length_finRange] at selectWork
  have ix : (index z table).Bound ((2*m+1)+(2*(m+1)+1)+(1+(m+1)*(4+m*8+2))+1) w := by
    have a := finRange_bound m
    have b := finRange_bound (m+1)
    constructor
    · simp only [index, Run.bind_slots, finRange_value, step_slots]
      have := a.1
      have := b.1
      have := selectWork.1
      omega
    · simp only [index, Run.bind_width, finRange_value, step_width]
      exact max_le (a.2.trans i0) (max_le (b.2.trans i1) (max_le selectWork.2 i1))
  let l := (index z table).value
  have finalCell (i : Fin m) :
      (⟨decide (z[i.val].natAbs ≤ (table.get l.castSucc)),
        ⟨3,max m.size (max z[i.val].natAbs.size (table.get l.castSucc).size + 1)⟩⟩ : Run Bool).Bound 3 w := by
    have e := ep l.castSucc
    have r := words i
    exact ⟨le_rfl, max_le i0 (by omega)⟩
  have finish := ArithmeticRun.tabulate_bound _ i0 finalCell
  constructor
  · change (endpoints m D K).work.slots + ((index z table).work.slots + (1+_)) ≤ _
    have b := ix.1
    have e := endpointsWork.1
    have f := finish.1
    change (endpoints m D K).work.slots ≤ _ at e
    apply Nat.le_trans (Nat.add_le_add e (Nat.add_le_add b (Nat.add_le_add_left f 1)))
    calc
      _ ≤ 3*(L+2)+(L+2)*(2+2*(L+1)) +
          ((2*L+1)+(2*(L+1)+1)+(1+(L+1)*(4+L*8+2))+1 + (1+(3*(L+1)+L*3))) := by gcongr <;> omega
      _ ≤ _ := by ring_nf; omega
  · exact max_le endpointsWork.2 (max_le ix.2 (max_le idx finish.2))

end Kintali.LinearProgramming.WindowRun
