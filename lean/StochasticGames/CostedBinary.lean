module

public import StochasticGames.BinaryEncoding
public import StochasticGames.CompilerRun
import all StochasticGames.BinaryEncoding
import all StochasticGames.CompilationCost

/-!
# Executing the binary reader and writer with charged primitives

The input reader first counts its stream and adds three to obtain its word width.
A parsed unsigned magnitude occupies at most as many binary digits as its field.
Each reader returns a shared suffix. A natural-number loop charges the predecessor
exposed by its `k+1` case. Testing for an empty suffix inspects its constructor.
After all rows have parsed, the reader reserves their array and writes each slot once.
-/

@[expose] public section

namespace StochasticGames.CostedBinary

open CompilerRun CompilationCost

abbrev Bits := List Bool

/-- A successful result and an upper bound on the work of this very execution. -/
private structure Returns {α : Type} (r : Run α) (v : α) (k w : ℕ) : Prop where
  out : r.value = v
  cost : Run.Bound k w r

private theorem Returns.weaken {α : Type} {r : Run α} {v : α} {k w k' w' : ℕ}
    (h : Returns r v k w) (hk : k ≤ k') (hw : w ≤ w') : Returns r v k' w' :=
  ⟨h.out, h.cost.1.trans hk, h.cost.2.trans hw⟩

private theorem retStep {α : Type} (w : ℕ) (v : α) : Returns (step w v) v 1 w :=
  ⟨rfl, le_rfl, le_rfl⟩

private theorem Returns.seq {α β : Type} {r : Run α} {a : α} {k j w : ℕ} {f : α → Run β} {b : β}
    (h : Returns r a k w) (h' : Returns (f a) b j w) : Returns (r >>= f) b (k+j) w := by
  constructor
  · change (f r.value).value = b
    rw [h.out, h'.out]
  · change r.work.slots + (f r.value).work.slots ≤ k+j ∧ max r.work.width (f r.value).work.width ≤ w
    rw [h.out]
    exact ⟨Nat.add_le_add h.cost.1 h'.cost.1, max_le h.cost.2 h'.cost.2⟩

/-- A status check between two fields. Failed reads stop at the first invalid field. -/
def afterRead {α β : Type} (w : ℕ) (r : Run (Option (α × Bits)))
    (f : α → Bits → Run (Option β)) : Run (Option β) := do
  let result ← r
  match ← step w result with
  | none => pure none
  | some (a, tail) => f a tail

private theorem Returns.next {α β : Type} {w k j : ℕ} {r : Run (Option (α × Bits))}
    {f : α → Bits → Run (Option β)} {a : α} {tail : Bits} {v : Option β}
    (h : Returns r (some (a,tail)) k w) (hf : Returns (f a tail) v j w) :
    Returns (afterRead w r f) v (k + (1+j)) w :=
  h.seq ((retStep w (some (a,tail))).seq hf)

@[simp] theorem afterRead_value {α β : Type} (w : ℕ) (r : Run (Option (α × Bits)))
    (f : α → Bits → Run (Option β)) :
    (afterRead w r f).value = r.value.bind (fun p => (f p.1 p.2).value) := by
  cases h : r.value <;> simp [afterRead, h]

private theorem length_spec {α : Type} (xs : List α) :
    Returns (CompilerRun.length xs) xs.length (xs.length+1) xs.length.size :=
  ⟨length_value xs, length_bound xs⟩

def widthRun (w : ℕ) : Bits → Run (Option (ℕ × Bits))
  | [] => step w none
  | false::xs => step w (some (0,xs))
  | true::xs => afterRead w (widthRun w xs) fun k tail => step w (some (k+1,tail))

def blockRun (w : ℕ) : ℕ → Bits → Run (Option (Bits × Bits))
  | 0, xs => step w (some ([],xs))
  | _+1, [] => step w none
  | k+1, b::xs => do
    let _ ← step w k
    afterRead w (blockRun w k xs) fun digits tail =>
      step w (some (b::digits,tail))

def unpackRun (w : ℕ) : Bits → Run ℕ
  | [] => step w 0
  | b::bs => do
    let a ← unpackRun w bs
    step w (Nat.bit b a)

def natRun (w : ℕ) (xs : Bits) : Run (Option (ℕ × Bits)) :=
  afterRead w (widthRun w xs) fun k rest =>
    afterRead w (blockRun w k rest) fun digits tail => do
      let v ← unpackRun w digits
      step w (if v.size = k then some (v,tail) else none)

def intRun (w : ℕ) : Bits → Run (Option (ℤ × Bits))
  | [] => step w none
  | sign::xs => afterRead w (natRun w xs) fun a tail =>
      step w (if sign && a == 0 then none else some (if sign then -(a : ℤ) else (a : ℤ),tail))

def positionRun (w n : ℕ) : Bits → Run (Option (Source.Position (Fin n) × Bits))
  | true :: b :: tail => step w (some (.inr b,tail))
  | false :: rest => afterRead w (natRun w rest) fun i tail =>
      step w (if hi : i < n then some (.inl ⟨i,hi⟩,tail) else none)
  | _ => step w none

def manyRun {α : Type} (w : ℕ) (read : Bits → Run (Option (α × Bits))) :
    ℕ → Bits → Run (Option (List α × Bits))
  | 0, xs => step w (some ([],xs))
  | k+1, xs => do
    let _ ← step w k
    afterRead w (read xs) fun a rest =>
      afterRead w (manyRun w read k rest) fun as tail => step w (some (a::as,tail))

def rowRun (w n : ℕ) : Bits → Run (Option (Source.Row (Fin n) × Bits))
  | true::xs => afterRead w (positionRun w n xs) fun a rest =>
      afterRead w (positionRun w n rest) fun b tail => step w (some (.chance a b,tail))
  | false :: isMin :: xs => afterRead w (natRun w xs) fun k rest =>
      afterRead w (manyRun w (positionRun w n) k rest) fun choices tail =>
        step w (match choices with
          | [] => none
          | a::l => some (if isMin then .min a l else .max a l,tail))
  | _ => step w none

/-- Each push transfers the accumulator to the next iteration. When called by `inputRun`,
the freshly reserved array has one slot per row. `row_reservation` proves this from the parse. -/
def arrayRun {α : Type} (w : ℕ) : List α → Array α → Run (Array α)
  | [], acc => step w acc
  | a::as, acc => do
    let next ← step w (acc.push a)
    arrayRun w as next

theorem arrayRun_slots {α : Type} (w : ℕ) (rs : List α) (acc : Array α) :
    (arrayRun w rs acc).work.slots = rs.length+1 := by
  induction rs generalizing acc with
  | nil => rfl
  | cons a rs ih => simp [arrayRun, ih, Nat.add_comm 1]

def checkedRows (n : ℕ) (rs : Array (Source.Row (Fin n))) : Option (Vector (Source.Row (Fin n)) n) :=
  if h : rs.size = n then some ⟨rs,h⟩ else none

def inputRun (w : ℕ) (xs : Bits) : Run (Option ((Σ n, ThresholdInput n) × Bits)) :=
  afterRead w (natRun w xs) fun n rest =>
    afterRead w (manyRun w (rowRun w n) n rest) fun rs rest => do
      let empty ← step w (Array.emptyWithCapacity n)
      let arr ← arrayRun w rs empty
      match ← step w (checkedRows n arr) with
      | some rows =>
        afterRead w (positionRun w n rest) fun start rest =>
          afterRead w (intRun w rest) fun num rest =>
            afterRead w (natRun w rest) fun den tail =>
              step w (if hd : 0 < den then some (⟨n,⟨rows,start,num,den,hd⟩⟩,tail) else none)
      | none => step w none

def finishValue {α : Type} (parsed : Option (α × Bits)) : Option α :=
  match parsed with | some (x, []) => some x | _ => none

def decodeRun (xs : Bits) : Run (Option (Σ n, ThresholdInput n)) := do
  let len ← CompilerRun.length xs
  let width ← natAdd len 3
  let result ← inputRun width xs
  step width (finishValue result)

private theorem width_value (w : ℕ) (xs : Bits) :
    (widthRun w xs).value = BinaryEncoding.readWidth xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => rfl
    | true =>
      simp only [widthRun, BinaryEncoding.readWidth, afterRead_value, ih]
      cases BinaryEncoding.readWidth xs <;> rfl

private theorem block_value (w k : ℕ) (xs : Bits) :
    (blockRun w k xs).value = BinaryEncoding.readBlock k xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      simp only [blockRun, Run.bind_value, BinaryEncoding.readBlock, afterRead_value, ih]
      cases BinaryEncoding.readBlock k xs <;> rfl

private theorem unpack_value (w : ℕ) (bs : Bits) : (unpackRun w bs).value = bs.foldr Nat.bit 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [unpackRun, ih]

/-- The accumulator at each recursive digit read fits in the consumed digit block,
including blocks that the subsequent canonicality check rejects. -/
theorem unpackRun_width (w : ℕ) (bs : Bits) : (unpackRun w bs).value.size ≤ bs.length := by
  rw [unpack_value]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldr_cons, List.length_cons]
    by_cases h : Nat.bit b (bs.foldr Nat.bit 0) = 0
    · simp [h]
    · rw [Nat.size_bit h]
      exact Nat.succ_le_succ ih

private theorem nat_value (w : ℕ) (xs : Bits) : (natRun w xs).value = BinaryEncoding.readNat xs := by
  simp [natRun, afterRead_value, width_value, block_value, unpack_value, BinaryEncoding.readNat,
    Option.bind_eq_bind]

private theorem int_value (w : ℕ) (xs : Bits) : (intRun w xs).value = BinaryEncoding.readInt xs := by
  cases xs <;> simp [intRun, BinaryEncoding.readInt, nat_value, Option.bind_eq_bind]

private theorem position_value (w n : ℕ) (xs : Bits) :
    (positionRun w n xs).value = BinaryEncoding.readPosition n xs := by
  rcases xs with _ | ⟨b,xs⟩
  · rfl
  · cases b
    · simp [positionRun, BinaryEncoding.readPosition, nat_value, Option.bind_eq_bind]
    · cases xs <;> rfl

private theorem many_value {α : Type} (w : ℕ) (read : Bits → Run (Option (α × Bits)))
    (r : BinaryEncoding.Reader α) (h : ∀ xs, (read xs).value = r xs) (k : ℕ) (xs : Bits) :
    (manyRun w read k xs).value = BinaryEncoding.readMany r k xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => simp [manyRun, BinaryEncoding.readMany, h, ih, Option.bind_eq_bind]

private theorem row_value (w n : ℕ) (xs : Bits) :
    (rowRun w n xs).value = BinaryEncoding.readRow n xs := by
  rcases xs with _ | ⟨b,xs⟩
  · rfl
  · cases b
    · cases xs with
      | nil => rfl
      | cons isMin xs =>
        simp only [rowRun, afterRead_value, nat_value, BinaryEncoding.readRow, Option.bind_eq_bind,
          many_value _ _ _ (position_value w n)]
        cases h : BinaryEncoding.readNat xs with
        | none => rfl
        | some p =>
          rcases p with ⟨k,rest⟩
          cases h' : BinaryEncoding.readMany (BinaryEncoding.readPosition n) k rest with
          | none => simp [h']
          | some p =>
            rcases p with ⟨l,tail⟩
            cases l <;> simp [h']
    · simp [rowRun, BinaryEncoding.readRow, position_value, Option.bind_eq_bind]

private theorem array_value {α : Type} (w : ℕ) (xs : List α) (acc : Array α) :
    (arrayRun w xs acc).value = (acc.toList ++ xs).toArray := by
  induction xs generalizing acc with
  | nil => simp [arrayRun]
  | cons a xs ih => simp [arrayRun, ih, List.append_assoc]

private theorem input_value (w : ℕ) (xs : Bits) :
    (inputRun w xs).value = BinaryEncoding.readInput xs := by
  simp only [inputRun, afterRead_value, nat_value, many_value _ _ _ (row_value w _),
    BinaryEncoding.readInput, Option.bind_eq_bind]
  cases hn : BinaryEncoding.readNat xs with
  | none => rfl
  | some p =>
    rcases p with ⟨n,t₁⟩
    simp only [Option.bind_some]
    cases hrs : BinaryEncoding.readMany (BinaryEncoding.readRow n) n t₁ with
    | none => rfl
    | some p =>
      rcases p with ⟨rs,t₂⟩
      simp only [Option.bind_some]
      by_cases h : rs.length = n <;>
        simp [array_value, checkedRows, h, position_value, int_value, nat_value]

theorem decodeRun_value (xs : Bits) : (decodeRun xs).value = BinaryEncoding.decodeInput xs := by
  simp only [decodeRun, natAdd, Run.bind_value, step_value, input_value, BinaryEncoding.decodeInput,
    BinaryEncoding.finish, finishValue]
  rcases BinaryEncoding.readInput xs with _ | ⟨a, _ | ⟨b,bs⟩⟩ <;> rfl

private theorem width_spec (w k : ℕ) (tail : Bits) :
    Returns (widthRun w (List.replicate k true ++ false::tail)) (some (k,tail)) (2*k+1) w := by
  induction k with
  | zero => exact retStep w _
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, widthRun]
    refine (Returns.next (f := fun k tail => step w (some (k+1,tail))) ih (retStep w _)).weaken ?_ le_rfl
    omega

private theorem block_spec (w : ℕ) (bs tail : Bits) :
    Returns (blockRun w bs.length (bs++tail)) (some (bs,tail)) (3*bs.length+1) w := by
  induction bs with
  | nil => exact retStep w _
  | cons b bs ih =>
    simp only [List.length_cons, List.cons_append, blockRun]
    refine ((retStep w bs.length).seq (f := fun _ => _)
      (Returns.next (f := fun l tail => step w (some (b::l,tail))) ih (retStep w _))).weaken ?_ le_rfl
    omega

private theorem unpack_spec (w : ℕ) (bs : Bits) :
    Returns (unpackRun w bs) (bs.foldr Nat.bit 0) (bs.length+1) w := by
  induction bs with
  | nil => exact retStep w _
  | cons b bs ih => exact ih.seq (f := fun a => step w (Nat.bit b a)) (retStep w _)

private theorem nat_spec (w a : ℕ) (tail : Bits) :
    Returns (natRun w (natBits a ++ tail)) (some (a,tail)) (8*(natBits a).length) w := by
  have hb : Returns (blockRun w a.size (a.bits++tail)) (some (a.bits,tail)) (3*a.size+1) w := by
    simpa only [Nat.size_eq_bits_len] using block_spec w a.bits tail
  have hu : Returns (unpackRun w a.bits) a (a.size+1) w := by
    simpa only [BinaryEncoding.fold_bits, Nat.size_eq_bits_len] using unpack_spec w a.bits
  unfold natRun
  rw [show natBits a ++ tail = List.replicate a.size true ++ false::(a.bits++tail) by simp [natBits]]
  refine Returns.weaken (Returns.next (width_spec w a.size (a.bits++tail)) (Returns.next hb
    (hu.seq (j := 1) (f := fun z => step w (if z.size = a.size then some (z, tail) else none)) ?_))) ?_ le_rfl
  · simpa using retStep w (some (a,tail))
  · simp only [natBits_length]; omega

private theorem int_spec (w : ℕ) (z : ℤ) (tail : Bits) :
    Returns (intRun w (intBits z ++ tail)) (some (z,tail)) (10*(intBits z).length) w := by
  simp only [intBits, List.cons_append, intRun]
  refine Returns.weaken (Returns.next (j := 1) (nat_spec w z.natAbs tail) ?_) ?_ le_rfl
  · have hv : (if decide (z < 0) && (z.natAbs == 0) then none
        else some (if decide (z < 0) then -(z.natAbs : ℤ) else (z.natAbs : ℤ),tail)) = some (z,tail) := by
      by_cases hz : z < 0
      · have hne := (Int.natAbs_pos.mpr hz.ne).ne'
        simp [hz, hne, abs_of_neg hz]
      · simp [hz, abs_of_nonneg (le_of_not_gt hz)]
    rw [hv]
    exact retStep w _
  · simp only [List.length_cons]; omega

private theorem pos_spec (w : ℕ) {n : ℕ} (p : Source.Position (Fin n)) (tail : Bits) :
    Returns (positionRun w n (positionBits p ++ tail)) (some (p,tail)) (10*(positionBits p).length) w := by
  cases p with
  | inr b => exact (retStep w _).weaken (by simp [positionBits]) le_rfl
  | inl i =>
    simp only [positionBits, List.cons_append, positionRun]
    refine Returns.weaken (Returns.next (j := 1) (nat_spec w i.val tail) ?_) ?_ le_rfl
    · simpa only [dite_eq_left i.isLt] using (retStep w (some (Sum.inl i,tail)))
    · simp only [List.length_cons]; omega

private theorem many_spec {α : Type} (w C : ℕ) (read : Bits → Run (Option (α × Bits)))
    (encode : α → Bits) (nonempty : ∀ a, 0 < (encode a).length)
    (valid : ∀ a tail, Returns (read (encode a ++ tail)) (some (a,tail)) (C*(encode a).length) w)
    (xs : List α) (tail : Bits) :
    Returns (manyRun w read xs.length (xs.flatMap encode ++ tail)) (some (xs,tail))
      ((C+4)*(xs.flatMap encode).length + 1) w := by
  induction xs generalizing tail with
  | nil => simpa [manyRun] using retStep w (some (([] : List α),tail))
  | cons a xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, manyRun]
    refine ((retStep w xs.length).seq (f := fun _ => _)
      (Returns.next (valid a _) (Returns.next (ih tail) (retStep w _)))).weaken ?_ le_rfl
    have := nonempty a
    simp only [List.length_append, Nat.mul_add, Nat.add_mul]
    omega

private theorem pos_bits_pos {n : ℕ} (p : Source.Position (Fin n)) : 0 < (positionBits p).length := by
  cases p <;> simp [positionBits]

private theorem row_spec (w : ℕ) {n : ℕ} (row : Source.Row (Fin n)) (tail : Bits) :
    Returns (rowRun w n (sourceRowBits row ++ tail)) (some (row,tail)) (32*(sourceRowBits row).length) w := by
  cases row with
  | chance a b =>
    simp only [sourceRowBits, List.append_assoc, List.cons_append, List.nil_append, rowRun]
    refine Returns.weaken (Returns.next (pos_spec w a _) (Returns.next (pos_spec w b _) (retStep w _))) ?_ le_rfl
    simp only [List.length_cons, List.length_append]
    omega
  | max a l | min a l =>
    have hm := many_spec w 10 (positionRun w n) positionBits pos_bits_pos (pos_spec w) (a::l) tail
    simp only [List.length_cons] at hm
    simp only [sourceRowBits, List.append_assoc, List.cons_append, List.nil_append, rowRun]
    refine Returns.weaken (Returns.next (nat_spec w (l.length+1) _) (Returns.next hm (retStep w _))) ?_ le_rfl
    simp only [List.length_cons, List.length_append]
    omega

private theorem row_bits_pos {n : ℕ} (row : Source.Row (Fin n)) : 0 < (sourceRowBits row).length := by
  cases row <;> simp [sourceRowBits]

private theorem array_spec {α : Type} (w : ℕ) (xs : List α) (acc : Array α) :
    Returns (arrayRun w xs acc) (acc.toList ++ xs).toArray (xs.length+1) w := by
  induction xs generalizing acc with
  | nil => simpa [arrayRun] using retStep w acc
  | cons a xs ih =>
    have h := (retStep w (acc.push a)).seq (f := arrayRun w xs) (ih (acc.push a))
    simpa [arrayRun, List.append_assoc, Nat.add_comm 1] using h

private theorem input_spec {n : ℕ} (w : ℕ) (I : ThresholdInput n) (tail : Bits) :
    Returns (inputRun w (inputBits I ++ tail)) (some (⟨n,I⟩,tail)) (90*((inputBits I).length+1)) w := by
  let rs := I.rows.toList
  have hflat : (List.finRange n).flatMap (fun i => sourceRowBits (I.rows.get i)) =
      rs.flatMap sourceRowBits := by
    dsimp only [rs]
    rw [← BinaryEncoding.vector_rows I.rows, List.flatMap_map]
  have hrs (rest : Bits) := many_spec w 32 (rowRun w n) sourceRowBits row_bits_pos (row_spec w) rs rest
  have hrn : rs.length = n := Vector.length_toList
  simp only [hrn] at hrs
  have hv : (⟨rs.toArray, by simp [hrn]⟩ : Vector _ n) = I.rows := by
    apply Vector.toArray_inj.mp
    simp [rs, Vector.toList]
  have harr : Returns (arrayRun w rs (Array.emptyWithCapacity n)) rs.toArray (n+1) w := by
    simpa [hrn] using array_spec w rs (Array.emptyWithCapacity n)
  have hcheck : Returns (step w (checkedRows n rs.toArray)) (some I.rows) 1 w := by
    simpa [checkedRows, hrn, hv] using retStep w (some I.rows)
  have hrd := CompilationCost.list_length_le_flatMap sourceRowBits row_bits_pos rs
  rw [hrn] at hrd
  unfold inputRun
  simp only [inputBits, List.append_assoc, hflat]
  refine Returns.weaken (Returns.next (nat_spec w n _) (Returns.next (hrs _)
    ((retStep w (Array.emptyWithCapacity n)).seq (f := _) (harr.seq (f := _) (hcheck.seq (f := _)
      (j := 10*(positionBits I.start).length + (1 + (10*(intBits I.numerator).length +
        (1 + (8*(natBits I.denominator).length + (1+1)))))) ?_))))) ?_ le_rfl
  · dsimp only
    refine Returns.next (pos_spec w I.start _) (Returns.next (int_spec w I.numerator _)
      (Returns.next (j := 1) (nat_spec w I.denominator _) ?_))
    simp only [dite_eq_left I.denominator_pos]
    exact retStep w _
  · simp only [List.length_append]
    omega

theorem decodeRun_bound {n : ℕ} (I : ThresholdInput n) :
    (decodeRun (inputBits I)).Bound (100*((inputBits I).length+1)) ((inputBits I).length+3) := by
  let xs := inputBits I
  let w := xs.length+3
  have hl := (length_spec xs).weaken le_rfl (show xs.length.size ≤ w by
    dsimp [w]; have := BinarySize.size_le_self xs.length; omega)
  have hi : Returns (inputRun w xs) (some (⟨n,I⟩,[])) (90*(xs.length+1)) w := by
    simpa only [List.append_nil] using input_spec w I []
  have hw : Returns (natAdd xs.length 3) w 1 w :=
    (retStep _ _).weaken le_rfl (by
      apply max_le
      · have := BinarySize.size_le_self xs.length; dsimp [w]; omega
      · have : (3 : ℕ).size = 2 := by decide
        dsimp [w]; omega)
  have h : Returns (decodeRun xs) (some ⟨n,I⟩) (xs.length+1+(1+(90*(xs.length+1)+1))) w :=
    hl.seq (f := fun k => do
      let width ← natAdd k 3
      let result ← inputRun width xs
      step width (finishValue result))
      (hw.seq (f := fun width => do
        let result ← inputRun width xs
        step width (finishValue result))
        (hi.seq (f := fun result => step w (finishValue result)) (retStep w _)))
  exact h.cost.weaken (by dsimp only [xs]; omega) le_rfl

/-! The writer receives a suffix and prepends its field. Each bit is emitted once,
and the list constructors share the suffix already written. -/

def digitsRun (w : ℕ) : ℕ → ℕ → Bits → Run Bits
  | 0, _, tail => step w tail
  | k+1, a, tail => do
    let _ ← step w k
    let half ← step w a.div2
    let b ← step w a.bodd
    let digits ← digitsRun w k half tail
    step w (b::digits)

def headerRun (w : ℕ) : ℕ → Bits → Run Bits
  | 0, digits => step w (false::digits)
  | k+1, digits => do
    let _ ← step w k
    let bits ← headerRun w k digits
    step w (true::bits)

def writeNat (a : ℕ) (tail : Bits) : Run Bits := do
  let k ← step a.size a.size
  let w ← natAdd k 2
  let digits ← digitsRun w k a tail
  headerRun w k digits

def writeInt (z : ℤ) (tail : Bits) : Run Bits := do
  let a ← step z.natAbs.size z.natAbs
  let sign ← step z.natAbs.size (decide (z<0))
  let bits ← writeNat a tail
  step 0 (sign::bits)

def writeArc (e : ArenaEncoding.ArcRecord) (tail : Bits) : Run Bits := do
  let weight ← writeInt e.weight tail
  let dst ← writeNat e.dst weight
  writeNat e.src dst

def writeArcs : List ArenaEncoding.ArcRecord → Bits → Run Bits
  | [], tail => step 0 tail
  | e::es, tail => do
    let arc ← step 0 e
    let bs ← writeArcs es tail
    writeArc arc bs

def serializeRun (t : ArenaEncoding.Table) : Run Bits := do
  let edges ← CompilerRun.length t.arcs
  let vertices ← CompilerRun.length t.owners
  let bs ← writeArcs t.arcs []
  let bs ← writeNat edges bs
  let bs ← CompilerRun.append t.owners bs
  let bs ← writeNat vertices bs
  writeNat t.start bs

private theorem digits_spec (w a : ℕ) (tail : Bits) :
    Returns (digitsRun w a.size a tail) (a.bits++tail) (4*a.size+1) w := by
  induction a using Nat.binaryRec' with
  | zero => exact retStep w _
  | bit b a ha ih =>
    have hs := Nat.size_bit (Nat.bit_ne_zero_iff.mpr ha)
    simp only [hs, Nat.bits_append_bit a b ha, List.cons_append, digitsRun,
      Nat.div2_bit, Nat.bodd_bit]
    refine ((retStep w a.size).seq (f := fun _ => _) (Returns.seq (retStep w a)
      (Returns.seq (retStep w b) (ih.seq (f := fun xs => step w (b::xs))
        (retStep w _))))).weaken ?_ le_rfl
    omega

private theorem header_spec (w k : ℕ) (tail : Bits) :
    Returns (headerRun w k tail) (List.replicate k true ++ false::tail) (2*k+1) w := by
  induction k with
  | zero => exact retStep w _
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, headerRun]
    refine ((retStep w k).seq (f := fun _ => _)
      (ih.seq (f := fun xs => step w (true::xs)) (retStep w _))).weaken ?_ le_rfl
    omega

private theorem writeNat_spec (a : ℕ) (tail : Bits) {W : ℕ} (ha : a.size ≤ W) :
    Returns (writeNat a tail) (natBits a ++ tail) (4*(natBits a).length) (W+3) := by
  have hk := (retStep a.size a.size).weaken le_rfl (show a.size ≤ a.size+2 by omega)
  have hw : Returns (natAdd a.size 2) (a.size+2) 1 (a.size+2) :=
    (retStep _ _).weaken le_rfl (by
      apply max_le
      · have := BinarySize.size_le_self a.size; omega
      · have : (2 : ℕ).size = 2 := by decide
        omega)
  unfold writeNat
  rw [show natBits a ++ tail = List.replicate a.size true ++ false::(a.bits++tail) by simp [natBits]]
  refine (Returns.seq hk (Returns.seq hw (Returns.seq (digits_spec (a.size+2) a tail)
    (header_spec (a.size+2) a.size (a.bits++tail))))).weaken ?_ (by omega)
  simp only [natBits_length]; omega

private theorem writeInt_spec (z : ℤ) (tail : Bits) {W : ℕ} (hz : z.natAbs.size ≤ W) :
    Returns (writeInt z tail) (intBits z ++ tail) (4*(intBits z).length) (W+3) := by
  have hw : z.natAbs.size ≤ W+3 := by omega
  unfold writeInt
  simp only [intBits, List.cons_append, List.length_cons]
  refine Returns.weaken (Returns.seq ((retStep _ _).weaken le_rfl hw)
    (Returns.seq ((retStep _ _).weaken le_rfl hw) (Returns.seq (writeNat_spec z.natAbs tail hz)
      ((retStep 0 _).weaken le_rfl (Nat.zero_le _))))) ?_ le_rfl
  omega

private theorem writeArc_spec (e : ArenaEncoding.ArcRecord) (tail : Bits) {W : ℕ}
    (h : e.src.size ≤ W ∧ e.dst.size ≤ W ∧ e.weight.natAbs.size ≤ W) :
    Returns (writeArc e tail) (arcBits e ++ tail) (4*(arcBits e).length) (W+3) := by
  unfold writeArc
  simp only [arcBits, List.append_assoc, List.length_append]
  refine Returns.weaken (Returns.seq (writeInt_spec e.weight tail h.2.2)
    (Returns.seq (writeNat_spec e.dst _ h.2.1) (writeNat_spec e.src _ h.1))) ?_ le_rfl
  omega

private theorem writeArcs_spec (es : List ArenaEncoding.ArcRecord) (tail : Bits) {W : ℕ}
    (h : ∀ e ∈ es, e.src.size ≤ W ∧ e.dst.size ≤ W ∧ e.weight.natAbs.size ≤ W) :
    Returns (writeArcs es tail) (es.flatMap arcBits ++ tail) (5*(es.flatMap arcBits).length+1) (W+3) := by
  induction es with
  | nil => exact (retStep 0 tail).weaken le_rfl (Nat.zero_le _)
  | cons e es ih =>
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem e ha))
    simp only [writeArcs, List.flatMap_cons, List.length_append, List.append_assoc]
    refine (((retStep 0 e).weaken le_rfl (Nat.zero_le (W+3))).seq (f := fun _ => _)
      (ht.seq (f := writeArc e) (writeArc_spec e _ (h e (List.mem_cons_self ..))))).weaken ?_ le_rfl
    have : 0 < (arcBits e).length := by simp [arcBits,intBits]
    omega

private theorem serialization_spec (t : ArenaEncoding.Table) (W : ℕ)
    (hs : t.start.size ≤ W) (hv : t.owners.length.size ≤ W) (he : t.arcs.length.size ≤ W)
    (hf : ∀ e ∈ t.arcs, e.src.size ≤ W ∧ e.dst.size ≤ W ∧ e.weight.natAbs.size ≤ W) :
    Returns (serializeRun t) (tableBits t) (20*((tableBits t).length+1)) (W+3) := by
  have hE := (length_spec t.arcs).weaken le_rfl (show t.arcs.length.size ≤ W+3 by omega)
  have hV := (length_spec t.owners).weaken le_rfl (show t.owners.length.size ≤ W+3 by omega)
  have hArcs : Returns (writeArcs t.arcs []) (t.arcs.flatMap arcBits)
      (5*(t.arcs.flatMap arcBits).length+1) (W+3) := by
    simpa only [List.append_nil] using writeArcs_spec t.arcs [] hf
  have hOwner (tail : Bits) : Returns (CompilerRun.append t.owners tail) (t.owners++tail)
      (t.owners.length+1) (W+3) := ⟨append_value _ _, append_bound _ _ _⟩
  have hp (e : ArenaEncoding.ArcRecord) : 0 < (arcBits e).length := by
    simp [arcBits, intBits]
  have ha := CompilationCost.list_length_le_flatMap arcBits hp t.arcs
  unfold serializeRun
  simp only [tableBits, List.append_assoc, List.length_append]
  refine Returns.weaken (Returns.seq hE (Returns.seq hV (Returns.seq hArcs
    (Returns.seq (writeNat_spec t.arcs.length _ he) (Returns.seq (hOwner _)
      (Returns.seq (writeNat_spec t.owners.length _ hv) (writeNat_spec t.start _ hs))))))) ?_ le_rfl
  omega

theorem serializeRun_bound (t : ArenaEncoding.Table) (W : ℕ)
    (hs : t.start.size ≤ W) (hv : t.owners.length.size ≤ W) (he : t.arcs.length.size ≤ W)
    (hf : ∀ e ∈ t.arcs, e.src.size ≤ W ∧ e.dst.size ≤ W ∧ e.weight.natAbs.size ≤ W) :
    (serializeRun t).Bound (20*((tableBits t).length+1)) (W+3) :=
  (serialization_spec t W hs hv he hf).cost

theorem serializeRun_value (t : ArenaEncoding.Table) : (serializeRun t).value = tableBits t := by
  let fields (e : ArenaEncoding.ArcRecord) := e.src.size + e.dst.size + e.weight.natAbs.size
  let W := t.start.size + t.owners.length.size + t.arcs.length.size + (t.arcs.map fields).sum
  apply (serialization_spec t W (by dsimp [W]; omega) (by dsimp [W]; omega) (by dsimp [W]; omega) ?_).out
  intro e he
  have own (es : List ArenaEncoding.ArcRecord) (hm : e ∈ es) : fields e ≤ (es.map fields).sum := by
    induction es with
    | nil => simp at hm
    | cons a es ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · simp
      · have := ih hm
        simp only [List.map_cons, List.sum_cons]
        omega
  have he' := own t.arcs he
  dsimp only [W,fields] at *
  omega

/-! ## Canonicality of successful source reads

Every accepted bit stream has exactly the fields written by the encoder.
This gives the execution bounds on the whole domain of successful parses. -/

open BinaryEncoding

private theorem width_sound {xs tail : Bits} {k : ℕ} (h : readWidth xs = some (k,tail)) :
    xs = List.replicate k true ++ false::tail := by
  induction xs generalizing k tail with
  | nil => simp [readWidth] at h
  | cons b xs ih =>
    cases b with
    | false => cases h; rfl
    | true =>
      obtain ⟨⟨j,rest⟩, hj, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      simp [List.replicate_succ, ih hj]

private theorem block_sound {k : ℕ} {xs digits tail : Bits} (h : readBlock k xs = some (digits,tail)) :
    digits.length = k ∧ xs = digits++tail := by
  induction k generalizing xs digits tail with
  | zero => cases h; exact ⟨rfl,rfl⟩
  | succ k ih =>
    cases xs with
    | nil => simp [readBlock] at h
    | cons b xs =>
      obtain ⟨⟨ds,rest⟩,hd,he⟩ := Option.map_eq_some_iff.mp h
      cases he
      obtain ⟨len, eq⟩ := ih hd
      simp [len,eq]

private theorem canonical_digits (ds : Bits) (h : (ds.foldr Nat.bit 0).size = ds.length) :
    (ds.foldr Nat.bit 0).bits = ds := by
  induction ds with
  | nil => rfl
  | cons b ds ih =>
    simp only [List.foldr_cons, List.length_cons] at h ⊢
    have hn : Nat.bit b (ds.foldr Nat.bit 0) ≠ 0 := by
      apply Nat.ne_of_gt
      apply Nat.size_pos.mp
      omega
    rw [Nat.bits_append_bit _ _ (Nat.bit_ne_zero_iff.mp hn)]
    rw [Nat.size_bit hn] at h
    rw [ih (Nat.succ.inj h)]

private theorem nat_sound {xs tail : Bits} {a : ℕ} (h : readNat xs = some (a,tail)) :
    xs = natBits a ++ tail := by
  unfold readNat at h
  obtain ⟨⟨k,t₁⟩, hw, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨ds,t₂⟩, hb, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  next he =>
    cases h
    obtain ⟨hlen, hsplit⟩ := block_sound hb
    have hd := canonical_digits ds (he.trans hlen.symm)
    rw [width_sound hw, hsplit]
    simp [natBits, he, hd]
  next => contradiction

/-- The actual unsigned word and the header counter fit in the size of their field. -/
theorem natRun_field_length {w a : ℕ} {xs tail : Bits}
    (h : (natRun w xs).value = some (a,tail)) : 2*a.size+1+tail.length = xs.length := by
  rw [nat_value] at h
  rw [nat_sound h, List.length_append, natBits_length]

private theorem int_sound {xs tail : Bits} {z : ℤ} (h : readInt xs = some (z,tail)) :
    xs = intBits z ++ tail := by
  cases xs with
  | nil => simp [readInt] at h
  | cons sign xs =>
    unfold readInt at h
    obtain ⟨⟨a,t⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
    cases sign
    · simp only [Bool.false_and, Bool.false_eq_true, ite_false] at h
      cases h
      simp [intBits,nat_sound ha]
    · cases a with
      | zero => simp at h
      | succ k =>
        change some (Int.negSucc k,t) = some (z,tail) at h
        cases h
        rw [nat_sound ha]
        simp only [intBits, Int.negSucc_lt_zero, decide_true, Int.natAbs_negSucc, List.cons_append]

private theorem position_sound {n : ℕ} {xs tail : Bits} {p : Source.Position (Fin n)}
    (h : readPosition n xs = some (p,tail)) : xs = positionBits p ++ tail := by
  cases xs with
  | nil => simp [readPosition] at h
  | cons b xs =>
    cases b with
    | true =>
      cases xs with
      | nil => simp [readPosition] at h
      | cons b xs => cases h; rfl
    | false =>
      unfold readPosition at h
      obtain ⟨⟨i,t⟩,hi,h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · cases h; simp [positionBits, nat_sound hi]
      · contradiction

private theorem many_sound {α : Type} {read : Reader α} {encode : α → Bits}
    (hr : ∀ {xs a tail}, read xs = some (a,tail) → xs = encode a ++ tail)
    {k : ℕ} {xs tail : Bits} {as : List α} (h : readMany read k xs = some (as,tail)) :
    as.length = k ∧ xs = as.flatMap encode ++ tail := by
  induction k generalizing xs as tail with
  | zero => cases h; exact ⟨rfl,rfl⟩
  | succ k ih =>
    unfold readMany at h
    obtain ⟨⟨a,t⟩,ha,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨rest,t'⟩,hrest,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    obtain ⟨hl,hbs⟩ := ih hrest
    simp [hl, hr ha, hbs, List.append_assoc]

private theorem row_sound {n : ℕ} {xs tail : Bits} {r : Source.Row (Fin n)}
    (h : readRow n xs = some (r,tail)) : xs = sourceRowBits r ++ tail := by
  cases xs with
  | nil => simp [readRow] at h
  | cons tag xs =>
    cases tag with
    | true =>
      unfold readRow at h
      obtain ⟨⟨a,t₁⟩,ha,h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨b,t₂⟩,hb,h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      simp [sourceRowBits, position_sound ha, position_sound hb, List.append_assoc]
    | false =>
      cases xs with
      | nil => simp [readRow] at h
      | cons isMin xs =>
        unfold readRow at h
        obtain ⟨⟨k,t₁⟩,hk,h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨moves,t₂⟩,hm,h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨hlen,hbs⟩ := many_sound position_sound hm
        cases moves with
        | nil => contradiction
        | cons a l =>
          cases isMin <;> cases h <;>
            simp [sourceRowBits, nat_sound hk, hbs, ← hlen, List.append_assoc]

/-- At every reached array reservation, its capacity equals the number of rows ready to
write and is at most the number of bits consumed by those rows. -/
theorem row_reservation {w n : ℕ} {xs tail : Bits} {rs : List (Source.Row (Fin n))}
    (h : (manyRun w (rowRun w n) n xs).value = some (rs,tail)) :
    rs.length = n ∧ n + tail.length ≤ xs.length := by
  rw [many_value _ _ _ (row_value w n)] at h
  obtain ⟨len,fields⟩ := many_sound row_sound h
  have count := CompilationCost.list_length_le_flatMap sourceRowBits row_bits_pos rs
  rw [fields, List.length_append]
  exact ⟨len, by omega⟩

private theorem input_sound {xs tail : Bits} {v : Σ n, ThresholdInput n}
    (h : readInput xs = some (v,tail)) : xs = inputBits v.2 ++ tail := by
  unfold readInput at h
  obtain ⟨⟨n,t₁⟩,hn,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨rs,t₂⟩,hrs,h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  next heq =>
    obtain ⟨⟨start,t₃⟩,hstart,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨num,t₄⟩,hnum,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨den,t₅⟩,hden,h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    next hpos =>
      cases h
      obtain ⟨_,hrows⟩ := many_sound row_sound hrs
      let vec : Vector (Source.Row (Fin n)) n := ⟨rs.toArray, by simpa using heq⟩
      have hflat : (List.finRange n).flatMap (fun i => sourceRowBits (vec.get i)) = rs.flatMap sourceRowBits := by
        rw [← List.flatMap_map, BinaryEncoding.vector_rows]
        simp [vec, Vector.toList]
      change xs = (natBits n ++ (List.finRange n).flatMap (fun i => sourceRowBits (vec.get i)) ++
        positionBits start ++ intBits num ++ natBits den) ++ tail
      dsimp only at hnum hden
      simp only [hflat, List.append_assoc, nat_sound hn, hrows, position_sound hstart, int_sound hnum, nat_sound hden]
    next => contradiction
  next => contradiction

/-- Every accepted bit stream is the canonical code of the input returned by the reader. -/
theorem inputBits_of_decode {xs : Bits} {n : ℕ} {I : ThresholdInput n}
    (h : BinaryEncoding.decodeInput xs = some ⟨n,I⟩) : xs = inputBits I := by
  unfold BinaryEncoding.decodeInput BinaryEncoding.finish at h
  rcases hp : readInput xs with _ | ⟨v, _ | ⟨b,rest⟩⟩ <;> simp [hp] at h
  subst v
  simpa only [List.append_nil] using input_sound hp

theorem inputLength_le_of_decode {xs : Bits} {n : ℕ} {I : ThresholdInput n}
    (h : BinaryEncoding.decodeInput xs = some ⟨n,I⟩) : inputLength I ≤ xs.length := by
  rw [inputBits_of_decode h]
  exact inputLength_le_bits I

theorem decodeRun_bound_of_success {xs : Bits} {n : ℕ} {I : ThresholdInput n}
    (h : BinaryEncoding.decodeInput xs = some ⟨n,I⟩) :
    (decodeRun xs).Bound (100*(xs.length+1)) (xs.length+3) := by
  rw [inputBits_of_decode h]
  exact decodeRun_bound I

end StochasticGames.CostedBinary
