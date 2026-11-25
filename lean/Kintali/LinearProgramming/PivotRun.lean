module

public import Kintali.LinearProgramming.PivotSelection
public import Kintali.LinearProgramming.DeterminantCost

/-!
# Charged search for the pivot minor

Rows, columns, and the active-row mask are stored in vectors. Each candidate
minor is tabulated before its determinant is evaluated. Nested scans visit
the same pairs and stop at the same first nonsingular border as `Minor.choose`.
-/

@[expose] public section

namespace Kintali.LinearProgramming.PivotRun

open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {m n : ℕ}

abbrev Grid (r c : ℕ) := Vector (Vector ℤ c) r

structure Input (m n : ℕ) where
  coeff : Grid m n
  rhs : Vector ℤ m

def Input.system (P : Input m n) : System (Fin m) (Fin n) where
  coeff := .of fun i j => P.coeff[i.val][j.val]
  rhs i := P.rhs[i.val]

structure State (m n : ℕ) where
  rank : ℕ
  rows : Vector (Fin m) rank
  cols : Vector (Fin n) rank

abbrev State.view (s : State m n) : Minor m n :=
  ⟨s.rank, fun i => s.rows[i.val], fun j => s.cols[j.val]⟩

def initial (m n : ℕ) : State m n := ⟨0, #v[], #v[]⟩

def prepend {α : Type} {r : ℕ} (w : ℕ) (a : α) (v : Vector α r) : Run (Vector α (r+1)) :=
  ArithmeticRun.tabulate (r+1) fun j =>
    ⟨Fin.cases a (fun i => v[i.val]) j, ⟨3, w⟩⟩

def extend (s : State m n) (i : Fin m) (j : Fin n) : Run (State m n) := do
  let w := m.size+n.size+(s.rank+1).size+2
  let rows ← prepend w i s.rows
  let cols ← prepend w j s.cols
  step w ⟨s.rank+1, rows, cols⟩

@[simp] theorem extend_view (s : State m n) (i : Fin m) (j : Fin n) :
    (extend s i j).value.view = s.view.extend i j := by
  cases s
  simp [extend, prepend, State.view, Minor.extend]
  constructor <;> funext t <;> exact Fin.cases rfl (fun _ => rfl) t

private theorem extend_rank (s : State m n) (i : Fin m) (j : Fin n) :
    (extend s i j).value.rank = s.rank+1 := rfl

def width (L : ℕ) := 64*(L+2)^2
def detSlots (L : ℕ) := 64*(L+2)^4
def probeSlots (L : ℕ) := 100*(L+2)^4
def scanSlots (L : ℕ) := 128*(L+2)^6

private theorem index_width {k L : ℕ} (hm : m ≤ L) (hn : n ≤ L) (hk : k ≤ L) :
    m.size+n.size+k.size+2 ≤ width L := by
  have a := (size_le_self m).trans hm
  have b := (size_le_self n).trans hn
  have c := (size_le_self k).trans hk
  unfold width
  ring_nf
  omega

private theorem extend_work (s : State m n) (i : Fin m) (j : Fin n) {L : ℕ}
    (hm : m ≤ L) (hn : n ≤ L) (hk : s.rank+1 ≤ L) :
    (extend s i j).Bound (16*(L+2)) (width L) := by
  let w := m.size+n.size+(s.rank+1).size+2
  have fits : w ≤ width L := index_width hm hn hk
  have idx : (s.rank+1).size ≤ width L := by dsimp [w] at fits; omega
  have ofn {α : Type} (a : α) (v : Vector α s.rank) :=
    ArithmeticRun.tabulate_bound (fun t : Fin (s.rank+1) =>
      (⟨Fin.cases a (fun b => v[b.val]) t, ⟨3,w⟩⟩ : Run α)) idx
      (fun _ => (show (⟨_,⟨3,w⟩⟩ : Run α).Bound 3 (width L) from ⟨le_rfl,fits⟩))
  have rows := ofn i s.rows
  have cols := ofn j s.cols
  constructor
  · simp only [extend, Run.bind_slots, step_slots]
    change (prepend w i s.rows).work.slots + ((prepend w j s.cols).work.slots + 1) ≤ _
    have hr := rows.1
    have hc := cols.1
    change (prepend w i s.rows).work.slots ≤ _ at hr
    change (prepend w j s.cols).work.slots ≤ _ at hc
    omega
  · exact max_le rows.2 (max_le cols.2 fits)

/-- Four index reads into the pivot maps and the source row table. -/
def sample (P : Input m n) (s : State m n) (i j : Fin s.rank) : Run ℤ :=
  ⟨s.view.matrix P.system i j, ⟨4, m.size+n.size+s.rank.size+2⟩⟩

def determinantOf (P : Input m n) (s : State m n) : Run ℤ := do
  let A ← ArithmeticRun.tabulate s.rank fun i => ArithmeticRun.tabulate s.rank (sample P s i)
  BirdRun.compute A

@[simp] theorem determinantOf_value (P : Input m n) (s : State m n) :
    (determinantOf P s).value = (s.view.matrix P.system).det := by
  simp only [determinantOf, Run.bind_value, ArithmeticRun.tabulate_value, BirdRun.compute_value]
  change (Bird.entries (Bird.tabulate (s.view.matrix P.system))).det = _
  rw [Bird.entries_tabulate]

theorem determinantOf_work (P : Input m n) (s : State m n) {h L : ℕ}
    (height : ∀ i j, |P.system.coeff i j| ≤ (h : ℤ)) (hm : m ≤ L) (hn : n ≤ L)
    (hk : s.rank ≤ L) (bits : h.size ≤ L) :
    (determinantOf P s).Bound (detSlots L) (width L) := by
  have iw := index_width hm hn hk
  have idx : s.rank.size ≤ width L := by omega
  have cells (i j : Fin s.rank) : (sample P s i j).Bound 4 (width L) := ⟨le_rfl, iw⟩
  let A := ArithmeticRun.tabulate s.rank (fun i => ArithmeticRun.tabulate s.rank (sample P s i))
  have cap := ArithmeticRun.tabulate_bound _ idx (fun i => ArithmeticRun.tabulate_bound _ idx (cells i))
  have val : Bird.entries A.value = s.view.matrix P.system := by
    simp only [A, ArithmeticRun.tabulate_value]
    exact Bird.entries_tabulate _
  have hA (i j : Fin s.rank) : |Bird.entries A.value i j| ≤ (h : ℤ) := by
    rw [val]
    exact height _ _
  have d := BirdRun.compute_work A.value hA
  have wd := BirdRun.wordWidth_polynomial hk bits hk
  have dw : (BirdRun.compute A.value).work.width ≤ width L := d.2.trans (wd.trans (by unfold width; omega))
  have calls : 3*(s.rank+1)+s.rank*(3*(s.rank+1)+s.rank*4) + 40*(s.rank+1)^4 ≤ detSlots L := by
    calc
      _ ≤ 3*(L+1)+L*(3*(L+1)+L*4) + 40*(L+1)^4 := by gcongr
      _ ≤ _ := by unfold detSlots; ring_nf; omega
  exact (bound_bind (f := BirdRun.compute) cap ⟨d.1,dw⟩).weaken calls le_rfl

def probe (P : Input m n) (active : Vector Bool m) (s : State m n) (i : Fin m) (j : Fin n) :
    Run (Option (Fin m × Fin n)) := do
  let candidate ← extend s i j
  let d ← determinantOf P candidate
  let flag ← step m.size active[i.val]
  step (d.natAbs.size+1) (if flag && decide (d ≠ 0) then some (i,j) else none)

@[simp] theorem probe_value (P : Input m n) (mask : Vector Bool m) (s : State m n)
    (i : Fin m) (j : Fin n) :
    (probe P mask s i j).value = Option.guard (fun p : Fin m × Fin n =>
      mask[p.1.val] && decide (determinant ((s.view.extend p.1 p.2).matrix P.system) ≠ 0)) (i,j) := by
  have he := congrArg (fun z : Minor m n => (z.matrix P.system).det) (extend_view s i j)
  change ((extend s i j).value.view.matrix P.system).det = ((s.view.extend i j).matrix P.system).det at he
  simp [probe, Option.guard, he]
  split
  · rename_i yes
    exact ite_eq_left yes
  · rename_i no
    exact ite_eq_right no

theorem probe_work (P : Input m n) (mask : Vector Bool m) (s : State m n) (i : Fin m) (j : Fin n)
    {h L : ℕ} (height : ∀ u v, |P.system.coeff u v| ≤ (h : ℤ)) (hm : m ≤ L) (hn : n ≤ L)
    (hk : s.rank+1 ≤ L) (bits : h.size ≤ L) :
    (probe P mask s i j).Bound (probeSlots L) (width L) := by
  let candidate := (extend s i j).value
  have rank : candidate.rank ≤ L := hk
  have tag := extend_work s i j hm hn hk
  have det := determinantOf_work P candidate height hm hn rank bits
  have val : (determinantOf P candidate).value.natAbs ≤ minorBound candidate.rank h := by
    rw [determinantOf_value, ← determinant_eq]
    apply determinant_natAbs_le
    exact fun _ _ => height _ _
  have db := (Nat.size_le_size val).trans (minorBound_size candidate.rank h)
  have sd := (size_le_self candidate.rank).trans rank
  have bound : (determinantOf P candidate).value.natAbs.size + 1 ≤ width L := by
    have sq : candidate.rank*(candidate.rank.size+h.size) ≤ L*(L+L) :=
      Nat.mul_le_mul rank (Nat.add_le_add sd bits)
    have boundedBits := db.trans (Nat.add_le_add_left sq 1)
    unfold width
    ring_nf at boundedBits ⊢
    omega
  have mi : m.size ≤ width L := (size_le_self m).trans (hm.trans (by unfold width; ring_nf; omega))
  constructor
  · change (extend s i j).work.slots + ((determinantOf P candidate).work.slots + (1+1)) ≤ _
    have ht := tag.1
    have hd := det.1
    unfold probeSlots detSlots at *
    ring_nf at ht hd ⊢
    omega
  · exact max_le tag.2 (max_le det.2 (max_le mi bound))

def next (P : Input m n) (mask : Vector Bool m) (s : State m n) : Run (Option (Fin m × Fin n)) := do
  let rows ← finRange m
  let cols ← finRange n
  ArithmeticRun.first (fun i => ArithmeticRun.first (probe P mask s i) cols) rows

@[simp] theorem next_value (P : Input m n) (mask : Vector Bool m) (s : State m n) :
    (next P mask s).value = s.view.next? P.system (fun i => mask[i.val]) := by
  unfold Minor.next? Minor.pairs List.product
  rw [List.find?_flatMap]
  simp only [next, Run.bind_value, finRange_value, ArithmeticRun.first_value, probe_value,
    List.find?_eq_findSome?_guard, List.findSome?_map, Function.comp_def]

theorem next_work (P : Input m n) (mask : Vector Bool m) (s : State m n) {h L : ℕ}
    (height : ∀ u v, |P.system.coeff u v| ≤ (h : ℤ)) (hm : m ≤ L) (hn : n ≤ L)
    (hk : s.rank+1 ≤ L) (bits : h.size ≤ L) :
    (next P mask s).Bound (scanSlots L) (width L) := by
  have a := finRange_bound m
  have b := finRange_bound n
  have iw := index_width hm hn (k := 0) (Nat.zero_le _)
  have ma := a.weaken le_rfl (show m.size ≤ width L by omega)
  have na := b.weaken le_rfl (show n.size ≤ width L by omega)
  have scan := ArithmeticRun.first_bound _ (fun i => ArithmeticRun.first_bound _
    (fun j => probe_work P mask s i j height hm hn hk bits) (List.finRange n)) (List.finRange m)
  simp only [List.length_finRange] at scan
  have costs :
      (2*m+1)+((2*n+1)+(1+m*(1+n*(probeSlots L+2)+2))) ≤ scanSlots L := by
    calc
      _ ≤ (2*L+1)+((2*L+1)+(1+L*(1+L*(probeSlots L+2)+2))) := by gcongr
      _ ≤ _ := by unfold probeSlots scanSlots; ring_nf; omega
  constructor
  · simp only [next, Run.bind_slots, finRange_value]
    exact (Nat.add_le_add ma.1 (Nat.add_le_add na.1 scan.1)).trans costs
  · simp only [next, Run.bind_width, finRange_value]
    exact max_le ma.2 (max_le na.2 scan.2)

def grow (P : Input m n) (mask : Vector Bool m) : ℕ → State m n → Run (State m n)
  | 0, s => step 0 s
  | t+1, s => do
    let _ ← step (t+1).size t
    let found ← next P mask s
    match ← step 0 found with
    | none => pure s
    | some (i,j) =>
      let candidate ← extend s i j
      grow P mask t candidate

theorem grow_value (P : Input m n) (mask : Vector Bool m) (t : ℕ) (s : State m n) :
    (grow P mask t s).value.view = Minor.grow P.system (fun i => mask[i.val]) t s.view := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    simp only [grow, Run.bind_value, step_value, next_value, Minor.grow]
    cases found : s.view.next? P.system (fun i => mask[i.val]) with
    | none => rfl
    | some point =>
      obtain ⟨i,j⟩ := point
      simp only [Run.bind_value, ih, extend_view]

theorem grow_work (P : Input m n) (mask : Vector Bool m) (t : ℕ) (s : State m n) {h L : ℕ}
    (height : ∀ u v, |P.system.coeff u v| ≤ (h : ℤ)) (hm : m ≤ L) (hn : n ≤ L)
    (room : s.rank+t ≤ L) (bits : h.size ≤ L) :
    (grow P mask t s).Bound (1+t*(scanSlots L+16*(L+2)+2)) (width L) := by
  induction t generalizing s with
  | zero => exact (bound_step _ _).weaken (by simp) (Nat.zero_le _)
  | succ t ih =>
    have nw := next_work P mask s height hm hn (by omega) bits
    have widx : (t+1).size ≤ width L := (size_le_self _).trans (by
      have H := index_width hm hn (k := L) le_rfl
      unfold width
      ring_nf
      omega)
    let branch : Option (Fin m × Fin n) → Run (State m n) := fun found => match found with
      | none => pure s
      | some (i,j) => extend s i j >>= grow P mask t
    have rest : (branch (next P mask s).value).Bound
        (16*(L+2)+(1+t*(scanSlots L+16*(L+2)+2))) (width L) := by
      cases (next P mask s).value with
      | none => exact (bound_pure s _).weaken (Nat.zero_le _) le_rfl
      | some p =>
        obtain ⟨i,j⟩ := p
        have ex := extend_work s i j hm hn (by omega : s.rank+1 ≤ L)
        exact bound_bind (f := grow P mask t) ex (ih _ (by rw [extend_rank]; omega))
    have check := bound_bind (f := branch)
      ((bound_step 0 (next P mask s).value).weaken le_rfl (Nat.zero_le _)) rest
    have run := bound_bind (f := fun found => step 0 found >>= branch) nw check
    exact (bound_bind (f := fun _ : ℕ => next P mask s >>= (fun found => step 0 found >>= branch))
      ((bound_step (t+1).size t).weaken le_rfl widx) run).weaken (by rw [Nat.succ_mul t (scanSlots L+16*(L+2)+2)]; omega) le_rfl

def choose (P : Input m n) (mask : Vector Bool m) : Run (State m n) :=
  grow P mask n (initial m n)

theorem choose_value (P : Input m n) (mask : Vector Bool m) :
    (choose P mask).value.view = Minor.choose P.system (fun i => mask[i.val]) := by
  have start : (initial m n).view = Minor.empty m n := by
    simp [initial, State.view, Minor.empty]
    constructor <;> funext i <;> exact i.elim0
  exact (grow_value ..).trans (congrArg (Minor.grow P.system (fun i => mask[i.val]) n) start)

theorem choose_work (P : Input m n) (mask : Vector Bool m) {h L : ℕ}
    (height : ∀ u v, |P.system.coeff u v| ≤ (h : ℤ)) (hm : m ≤ L) (hn : n ≤ L) (bits : h.size ≤ L) :
    (choose P mask).Bound (160*(L+2)^7) (width L) := by
  have work := grow_work P mask n (initial m n) height hm hn (by simpa [initial] using hn) bits
  apply work.weaken _ le_rfl
  calc
    _ ≤ 1+L*(scanSlots L+16*(L+2)+2) := by gcongr
    _ ≤ _ := by unfold scanSlots; ring_nf; omega

end Kintali.LinearProgramming.PivotRun
