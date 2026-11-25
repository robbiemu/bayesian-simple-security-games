module

public import Kintali.Recovery
public import Kintali.LinearProgramming.ArithmeticRun

/-! # Integer row compilation on prepared game data

A constant or coefficient reads at most one rational game field. The
common denominator is shared. These reads are charged separately from
the integer quotient, multiplication, and subtraction of two terms.
-/

@[expose] public section

namespace Kintali.ExactRecovery.RowWork

open StochasticGames.CompilerRun LinearProgramming.ArithmeticRun

variable {k m : ℕ}

inductive Datum (k m : ℕ)
  | zero
  | one
  | budget
  | prior (i : Fin k)
  | gain (j : Fin m)
  | intercept (i : Fin k) (j : Fin m)
  | slope (i : Fin k) (j : Fin m)

def datum (g : Game (Fin k) (Fin m)) : Datum k m → ℚ
  | .zero => 0
  | .one => 1
  | .budget => g.resources
  | .prior i => g.prior i
  | .gain j => g.gain j
  | .intercept i j => g.intercept i j
  | .slope i j => g.slope i j

def constantField : Atom (Fin k) (Fin m) → Datum k m
  | .one => .one
  | .budget => .budget
  | .prior i => .prior i
  | .cost i j => .intercept i j
  | _ => .zero

def coefficientField (a : Term (Fin k) (Fin m)) : Variable (Fin k) (Fin m) → Datum k m
  | .inl (i,j) => match a.atom with
    | .flow h l => if i = h ∧ j = l then .one else .zero
    | .flowSum h => if i = h then .one else .zero
    | .pressure l => if j = l then .gain l else .zero
    | _ => .zero
  | .inr (.inl j) => match a.atom with
    | .coverage l => if j = l then .one else .zero
    | .coverageSum => .one
    | .cost i l => if j = l then .slope i l else .zero
    | _ => .zero
  | .inr (.inr false) => match a.atom with
    | .threshold => .one
    | _ => .zero
  | .inr (.inr true) => if a.residual then .one else .zero

private theorem constant_value (g : Game (Fin k) (Fin m)) (a : Atom (Fin k) (Fin m)) :
    scaled g (datum g (constantField a)) = a.constant g := by
  cases a <;> simp [constantField, datum, scaled, Atom.constant]

private theorem coefficient_value (g : Game (Fin k) (Fin m)) (a : Term (Fin k) (Fin m))
    (v : Variable (Fin k) (Fin m)) :
    scaled g (datum g (coefficientField a v)) = a.coefficient g v := by
  rcases a with ⟨a,b⟩
  rcases v with ⟨i,j⟩ | j | bb
  · cases a <;> simp [coefficientField, Term.coefficient, datum, scaled] <;> split_ifs <;> simp_all
  · cases a <;> simp [coefficientField, Term.coefficient, datum, scaled] <;> split_ifs <;> simp_all
  · cases bb <;> cases a <;> cases b <;> simp [coefficientField, Term.coefficient, datum, scaled]

def scaleWord (d : ℕ) (q : ℚ) : Run ℤ := do
  let mult ← step (max d.size q.den.size) (d / q.den)
  intMul q.num mult

@[simp] theorem scaleWord_value (g : Game (Fin k) (Fin m)) (q : ℚ) :
    (scaleWord (denominator g) q).value = scaled g q := rfl

private theorem scaleWord_work (d : ℕ) (q : ℚ) {w : ℕ}
    (hd : d.size ≤ w) (hq : q.num.natAbs.size ≤ w) (hden : q.den.size ≤ w) :
    (scaleWord d q).Bound 2 (w+1) := by
  have h := (Nat.size_le_size (Nat.div_le_self d q.den)).trans hd
  exact ⟨le_rfl,max_le ((max_le hd hden).trans (Nat.le_succ _))
    (Nat.add_le_add_right (max_le hq (show ((d / q.den : ℕ) : ℤ).natAbs.size ≤ w from h)) _)⟩

def difference (d : ℕ) (read : Datum k m → Run ℚ) (a b : Datum k m) : Run ℤ := do
  let u ← read a
  let v ← read b
  let zu ← scaleWord d u
  let zv ← scaleWord d v
  intSub zu zv

theorem difference_value (g : Game (Fin k) (Fin m)) (read : Datum k m → Run ℚ)
    (same : ∀ a, (read a).value = datum g a) (a b : Datum k m) :
    (difference (denominator g) read a b).value =
      scaled g (datum g a) - scaled g (datum g b) := by
  simp [difference, same, intSub]

private theorem scaled_bits (d : ℕ) (q : ℚ) {w : ℕ} (hd : d.size ≤ w) (hq : q.num.natAbs.size ≤ w) :
    (scaleWord d q).value.natAbs.size ≤ 2*w := by
  change (q.num * ((d / q.den : ℕ) : ℤ)).natAbs.size ≤ 2*w
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have h := (Nat.size_le_size (Nat.div_le_self d q.den)).trans hd
  exact (StochasticGames.BinarySize.size_mul_le ..).trans (by omega)

theorem difference_work (d : ℕ) (read : Datum k m → Run ℚ) (a b : Datum k m)
    {w cost : ℕ} (hd : d.size ≤ w) (readWork : ∀ a, (read a).Bound cost w)
    (words : ∀ a, (read a).value.num.natAbs.size ≤ w ∧ (read a).value.den.size ≤ w) :
    (difference d read a b).Bound (2*cost+5) (2*w+1) := by
  have sa := scaleWord_work d (read a).value hd (words a).1 (words a).2
  have sb := scaleWord_work d (read b).value hd (words b).1 (words b).2
  have ua := scaled_bits d (read a).value hd (words a).1
  have ub := scaled_bits d (read b).value hd (words b).1
  obtain ⟨ac,aw⟩ := readWork a
  obtain ⟨bc,bw⟩ := readWork b
  constructor
  · simp only [difference, Run.bind_slots, intSub, step_slots]
    have := sa.1
    have := sb.1
    omega
  · simp only [difference, Run.bind_width, intSub, step_width, max_le_iff]
    exact ⟨by omega, by omega, sa.2.trans (by omega), sb.2.trans (by omega),
      Nat.add_le_add_right (max_le ua ub) 1⟩

def rule (p : Pattern (Fin k) (Fin m)) (i : Fin (exactRows k m)) :
    Option (Comparison (Fin k) (Fin m)) :=
  ((rowIndex k m).symm i).elim (some ∘ comparison p) (fun _ => none)

def constantWord (d : ℕ) (read : Datum k m → Run ℚ) :
    Option (Comparison (Fin k) (Fin m)) → Run ℤ
  | none => step 0 0
  | some cmp => difference d read (constantField cmp.right.atom) (constantField cmp.left.atom)

def compileRow (d : ℕ) (read : Datum k m → Run ℚ) (c : Option (Comparison (Fin k) (Fin m))) :
    Run (Vector ℤ (exactVars k m) × ℤ) := do
  let n := exactVars k m
  let columns ← tabulate n fun j =>
    match c with
    | none => step n.size (if j = varIndex k m (.inr (.inr true)) then 1 else 0)
    | some cmp => do
      let v ← step n.size ((varIndex k m).symm j)
      difference d read (coefficientField cmp.left v) (coefficientField cmp.right v)
  let rhs ← constantWord d read c
  step 0 (columns,rhs)

def compile (d : ℕ) (read : Datum k m → Run ℚ)
    (readRule : Fin (exactRows k m) → Run (Option (Comparison (Fin k) (Fin m)))) :
    Run (LinearProgramming.PivotRun.Input (exactRows k m) (exactVars k m)) := do
  let n := exactRows k m
  let rows ← tabulate n fun i => readRule i >>= compileRow d read
  let matrix ← tabulate n fun i => step n.size rows[i.val].1
  let rhs ← tabulate n fun i => step n.size rows[i.val].2
  step 0 ⟨matrix,rhs⟩

theorem compile_value (g : Game (Fin k) (Fin m)) (p : Pattern (Fin k) (Fin m))
    (read : Datum k m → Run ℚ) (same : ∀ a, (read a).value = datum g a)
    (readRule : Fin (exactRows k m) → Run (Option (Comparison (Fin k) (Fin m))))
    (rules : ∀ i, (readRule i).value = rule p i) :
    (compile (denominator g) read readRule).value = recoveryInput g p := by
  have eq (i : Fin (exactRows k m)) :
      (compileRow (denominator g) read (readRule i).value).value =
      (Vector.ofFn ((exactSystem g p).coeff i), (exactSystem g p).rhs i) := by
    rw [rules]
    cases h : (rowIndex k m).symm i with
    | inl r =>
      simp [rule, h, compileRow, constantWord, difference_value g read same, coefficient_value, constant_value,
        exactSystem, matrix, rhs]
    | inr u =>
      cases u
      simp [rule, h, compileRow, constantWord, exactSystem]
  simp only [compile, Run.bind_value, tabulate_value, Vector.getElem_ofFn, step_value, eq,
    recoveryInput]

def rowSlots (n readCost : ℕ) : ℕ := 3*(n+1) + (n+1)*(2*readCost+6) + 1

theorem compileRow_work (d : ℕ) (read : Datum k m → Run ℚ)
    (c : Option (Comparison (Fin k) (Fin m))) {w cost : ℕ}
    (hd : d.size ≤ w) (nw : (exactVars k m).size ≤ w) (readWork : ∀ a, (read a).Bound cost w)
    (words : ∀ a, (read a).value.num.natAbs.size ≤ w ∧ (read a).value.den.size ≤ w) :
    (compileRow d read c).Bound (rowSlots (exactVars k m) cost) (2*w+1) := by
  let n := exactVars k m
  let W := 2*w+1
  let cell (j : Fin n) : Run ℤ :=
    match c with
    | none => step n.size (if j = varIndex k m (.inr (.inr true)) then 1 else 0)
    | some cmp => do
      let v ← step n.size ((varIndex k m).symm j)
      difference d read (coefficientField cmp.left v) (coefficientField cmp.right v)
  have hn : n.size ≤ W := nw.trans (by unfold W; omega)
  have cells (j : Fin n) : (cell j).Bound (2*cost+6) W := by
    cases c with
    | none => exact ⟨by change 1 ≤ _; omega, hn⟩
    | some cmp =>
      have diff := difference_work d read (coefficientField cmp.left ((varIndex k m).symm j))
        (coefficientField cmp.right ((varIndex k m).symm j)) hd readWork words
      constructor
      · change 1 + (difference d read (coefficientField cmp.left ((varIndex k m).symm j))
          (coefficientField cmp.right ((varIndex k m).symm j))).work.slots ≤ _
        have := diff.1
        omega
      · exact max_le hn diff.2
  have tc := tabulate_bound cell hn cells
  have b : (constantWord d read c).Bound (2*cost+6) W := by
    cases c with
    | none => exact ⟨by change 1 ≤ _; omega,Nat.zero_le _⟩
    | some cmp => exact (difference_work d read _ _ hd readWork words).weaken (by omega) le_rfl
  constructor
  · change (tabulate n cell).work.slots + (_ + 1) ≤ rowSlots n cost
    have tc' := tc.1
    have b' := b.1
    unfold rowSlots
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · exact max_le tc.2 (max_le b.2 (Nat.zero_le _))


def denseSlots (rows vars readCost ruleCost : ℕ) : ℕ :=
  9*(rows+1) + rows*(ruleCost + rowSlots vars readCost + 2) + 1

theorem compile_work (d : ℕ) (read : Datum k m → Run ℚ)
    (readRule : Fin (exactRows k m) → Run (Option (Comparison (Fin k) (Fin m))))
    {w cost rowCost : ℕ} (hd : d.size ≤ w)
    (mw : (exactRows k m).size ≤ w) (nw : (exactVars k m).size ≤ w)
    (readWork : ∀ a, (read a).Bound cost w)
    (words : ∀ a, (read a).value.num.natAbs.size ≤ w ∧ (read a).value.den.size ≤ w)
    (rules : ∀ i, (readRule i).Bound rowCost w) :
    (compile d read readRule).Bound (denseSlots (exactRows k m) (exactVars k m) cost rowCost) (2*w+1) := by
  let n := exactRows k m
  let W := 2*w+1
  have grow : w ≤ W := by unfold W; omega
  have idx : n.size ≤ W := mw.trans grow
  let cells (i : Fin n) := readRule i >>= compileRow d read
  have boundCell (i : Fin n) : (cells i).Bound (rowCost + rowSlots (exactVars k m) cost) W :=
    bound_bind (f := compileRow d read) ((rules i).weaken le_rfl grow)
      (compileRow_work d read (readRule i).value hd nw readWork words)
  have allRows := tabulate_bound cells idx boundCell
  let mat (i : Fin n) := step n.size (tabulate n cells).value[i.val].1
  let vec (i : Fin n) := step n.size (tabulate n cells).value[i.val].2
  have mcost := tabulate_bound mat idx (fun _ => (bound_step _ _).weaken le_rfl idx)
  have vcost := tabulate_bound vec idx (fun _ => (bound_step _ _).weaken le_rfl idx)
  constructor
  · change (tabulate n cells).work.slots + ((tabulate n mat).work.slots +
      ((tabulate n vec).work.slots + 1)) ≤ _
    have r := allRows.1
    have mm := mcost.1
    have vv := vcost.1
    change _ ≤ denseSlots n _ _ _
    unfold denseSlots
    rw [Nat.mul_add n (rowCost + rowSlots (exactVars k m) cost) 2]
    omega
  · exact max_le allRows.2 (max_le mcost.2 (max_le vcost.2 (Nat.zero_le _)))


end Kintali.ExactRecovery.RowWork
