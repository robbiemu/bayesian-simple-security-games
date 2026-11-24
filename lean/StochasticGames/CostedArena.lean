module

public import StochasticGames.ArenaEncoding
public import StochasticGames.BinarySize
public import StochasticGames.CompilerRun
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Traversal and arithmetic costs of emitting the indexed arena

The edge passes follow the order of the public table: variable starts, row
entries, all term occurrences, and idle loops. Rows carry their numeric
positions during the passes, and variable IDs are found by equality scans.
-/
@[expose] public section
namespace StochasticGames.CostedArena
open ArenaEncoding IntegerAtoms AtomArena
variable {ν : Type} [DecidableEq ν]

private def flip (N : ℕ) (w : ℤ) := -(N : ℤ) * w - 1

private def raw (xs : List ν) (rows : List (IntAtom ν)) : Table :=
  let P := xs.length
  let N := 1 + P + rows.length
  let varId v := (xs.idxOf v) + 1
  let rowId i := 1 + P + i
  let starts := xs.map fun v => (⟨0, varId v, -1⟩ : ArcRecord)
  let enter := rows.zipIdx.map fun (r,i) => (⟨varId r.lhs, rowId i, -1⟩ : ArcRecord)
  let replies := rows.zipIdx.flatMap fun (r,i) => r.terms.map fun (v,w) =>
    (⟨rowId i, varId v, flip N w⟩ : ArcRecord)
  let idle := xs.flatMap fun v => if rows.any (fun r => r.lhs == v) then [] else
    [(⟨varId v, varId v, -1⟩ : ArcRecord)]
  ⟨0, true :: xs.map (fun _ => true) ++ rows.map (fun _ => false),
    starts ++ (enter ++ (replies ++ idle))⟩

private theorem idx_map {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (inj : Function.Injective f) (xs : List α) (v : α) :
    (xs.map f).idxOf (f v) = xs.idxOf v := by
  simp only [List.idxOf, List.findIdx_map]
  congr 1
  funext a
  rw [Bool.eq_iff_iff]
  simp [inj.eq_iff]

private theorem index_idx {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] (xs : Listing α) (v : α) :
    (xs.index v).val = xs.items.idxOf v := by
  have get : xs.items.get (xs.index v) = v := xs.index.symm_apply_apply v
  calc
    _ = xs.items.idxOf (xs.items.get (xs.index v)) := (xs.nodup.idxOf_getElem _ _).symm
    _ = _ := congrArg xs.items.idxOf get

private theorem var_id (vs : Listing ν) (rs : List (IntAtom ν)) (v : ν) :
    ((vertices vs rs).index (some (.inl v))).val = vs.items.idxOf v + 1 := by
  rw [index_idx]
  simp only [vertices, Listing.option, Listing.sum]
  rw [List.idxOf_cons_ne _ (by simp), idx_map some (Option.some_injective _),
    List.idxOf_append_of_mem (by exact List.mem_map.mpr ⟨v, vs.complete _, rfl⟩),
    idx_map Sum.inl Sum.inl_injective]

private theorem row_id (vs : Listing ν) (rs : List (IntAtom ν)) (i : Row rs) :
    ((vertices vs rs).index (some (.inr i))).val = 1 + vs.items.length + i.val := by
  rw [index_idx]
  simp only [vertices, Listing.option, Listing.sum, Listing.fin]
  rw [List.idxOf_cons_ne _ (by simp), idx_map some (Option.some_injective _),
    List.idxOf_append_of_notMem (by simp), idx_map Sum.inr Sum.inr_injective]
  simp [List.idxOf_finRange]
  omega

private theorem map_indexed {α β : Type*} (xs : List α) (f : α → ℕ → β) :
    (List.finRange xs.length).map (fun i => f (xs.get i) i.val) =
      xs.zipIdx.map (fun x => f x.1 x.2) := by
  apply List.ext_getElem <;> simp

private theorem map_get {α β : Type*} (xs : List α) (f : α → β) :
    (List.finRange xs.length).map (fun i => f (xs.get i)) = xs.map f := by
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map f) (List.map_get_finRange xs)

private theorem idle_pass (vs : Listing ν) (rs : List (IntAtom ν))
    (f : ν → ArcRecord) :
    ((vs.subtype (fun v => ∀ r : Row rs, (rs.get r).lhs ≠ v)).items.map (fun v => f v.val)) =
      vs.items.flatMap fun v => if rs.any (fun r => r.lhs == v) then [] else [f v] := by
  change List.map _ (vs.items.filterMap _) = _
  rw [List.filterMap_eq_flatMap_toList, List.map_flatMap]
  apply List.flatMap_congr
  intro v _
  have missing : (∀ r : Row rs, (rs.get r).lhs ≠ v) ↔
      ¬ rs.any (fun r => r.lhs == v) = true := by
    simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and]
    exact (List.forall_mem_iff_get (l := rs) (p := fun r => r.lhs ≠ v)).symm
  by_cases h : ∀ r : Row rs, (rs.get r).lhs ≠ v
  · simp only [dite_eq_left h, ite_eq_right (missing.mp h)]
    rfl
  · simp only [dite_eq_right h, ite_eq_left (Classical.not_not.mp (mt missing.mpr h))]
    rfl

private theorem raw_eq (vs : Listing ν) (rows : List (IntAtom ν)) :
    raw vs.items rows = ArenaEncoding.table vs rows true := by
  let nodes := vertices vs rows
  have zero : (nodes.index none).val = 0 := by
    rw [index_idx]; exact List.idxOf_cons_self
  have card : nodes.items.length = 1 + vs.items.length + rows.length := vertices_length vs rows
  have owners : nodes.items.map (fun v => !(isMax v)) =
      true :: vs.items.map (fun _ => true) ++ rows.map (fun _ => false) := by
    simp [nodes, vertices, Listing.option, Listing.sum, Listing.fin, List.map_map, Function.comp_def, isMax]
  simp only [raw, table, ↓reduceIte, Table.mk.injEq]
  refine ⟨zero.symm, owners.symm, ?_⟩
  symm
  simp only [edges, Listing.sum, List.map_append, List.map_map, Function.comp_def]
  apply congrArg₂ List.append
  · have hz : ((vertices vs rows).index none).val = 0 := zero
    simp only [AtomArena.src, AtomArena.dst, AtomArena.weight, hz, var_id, mul_zero, zero_sub]
  apply congrArg₂ List.append
  · simpa [Listing.fin, AtomArena.src, AtomArena.dst, AtomArena.weight, nodes, var_id, row_id] using
      (map_indexed rows (fun r i => (⟨vs.items.idxOf r.lhs+1, 1+vs.items.length+i, -1⟩ : ArcRecord)))
  apply congrArg₂ List.append
  · simp only [Listing.sigma, Listing.fin, List.sigma, List.map_flatMap, List.map_map, Function.comp_def]
    simp only [AtomArena.src, AtomArena.dst, AtomArena.weight, row_id, var_id, vertices_length]
    rw [List.flatMap_def, List.flatMap_def]
    congr 1
    have hm := map_indexed rows (fun r i => r.terms.map fun t =>
      (⟨1 + vs.items.length + i, vs.items.idxOf t.1 + 1, flip (1+vs.items.length+rows.length) t.2⟩ : ArcRecord))
    rw [← hm]
    apply List.map_congr_left
    intro r _
    exact map_get (rows.get r).terms (fun t => (⟨1+vs.items.length+r.val,vs.items.idxOf t.1+1,
      flip (1+vs.items.length+rows.length) t.2⟩ : ArcRecord))
  · simpa only [AtomArena.src, AtomArena.dst, AtomArena.weight, nodes, var_id, mul_zero,
      zero_sub, Prod.mk.eta] using
      (idle_pass vs rows (fun v => (⟨vs.items.idxOf v + 1, vs.items.idxOf v + 1,-1⟩ : ArcRecord)))

-- Executable passes
open CompilerRun

def indexed {α : Type} : List α → ℕ → Run (List (α × ℕ))
  | [], _ => step 0 []
  | x::xs, k => do
    let j ← natAdd k 1
    let t ← indexed xs j
    step 0 ((x,k)::t)

@[simp] private theorem indexed_value {α : Type} (xs : List α) (k : ℕ) :
    (indexed xs k).value = xs.zipIdx k := by
  induction xs generalizing k with
  | nil => rfl
  | cons a l ih => simp [indexed, natAdd, ih, List.zipIdx_cons]

def findId (w : ℕ) (v : ν) : List ν → Run ℕ
  | [] => step 0 0
  | a::xs => do
    let same ← step w (a == v)
    if same then pure 0 else do let j ← findId w v xs; natAdd j 1

@[simp] private theorem findId_value (w : ℕ) (v : ν) (xs : List ν) :
    (findId w v xs).value = xs.idxOf v := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a = v
    · subst a; simp [findId]
    · simp [findId, h, ih, natAdd, List.idxOf_cons_ne _ h]

def noRow (w : ℕ) (v : ν) : List (IntAtom ν) → Run Bool
  | [] => step 0 true
  | r::rs => do
    let hit ← step w (r.lhs == v)
    if hit then pure false else noRow w v rs

@[simp] private theorem noRow_value (w : ℕ) (v : ν) (rs : List (IntAtom ν)) :
    (noRow w v rs).value = !(rs.any fun r => r.lhs == v) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => by_cases h : r.lhs = v <;> simp [noRow, h, ih]

def variableId (w : ℕ) (xs : List ν) (v : ν) : Run ℕ := do
  let i ← findId w v xs
  natAdd i 1

def startArc (w : ℕ) (xs : List ν) (v : ν) : Run ArcRecord := do
  let i ← variableId w xs v
  step 0 ⟨0,i,-1⟩

def enterArc (w : ℕ) (xs : List ν) (startRow : ℕ) (r : IntAtom ν × ℕ) : Run ArcRecord := do
  let i ← variableId w xs r.1.lhs
  let j ← natAdd startRow r.2
  step 0 ⟨i,j,-1⟩

/-- Convert the binary vertex count to a signed word and compute its negation. -/
def signedFactor (N : ℕ) : Run ℤ := do
  let z ← step N.size (N : ℤ)
  intSub 0 z

@[simp] theorem signedFactor_value (N : ℕ) : (signedFactor N).value = -(N : ℤ) := by
  simp [signedFactor, intSub]

def replyArc (w : ℕ) (xs : List ν) (N rowId : ℕ) (t : ν × ℤ) : Run ArcRecord := do
  let j ← variableId w xs t.1
  let factor ← signedFactor N
  let a ← intMul factor t.2
  let b ← intSub a 1
  step 0 ⟨rowId,j,b⟩

def rowArcs (w : ℕ) (xs : List ν) (N startRow : ℕ) (r : IntAtom ν × ℕ) :
    Run (List ArcRecord) := do
  let i ← natAdd startRow r.2
  CompilerRun.mapM (replyArc w xs N i) r.1.terms

def idleArcs (w : ℕ) (xs : List ν) (rs : List (IntAtom ν)) (v : ν) :
    Run (List ArcRecord) := do
  let idle ← noRow w v rs
  if idle then
    let i ← variableId w xs v
    step 0 [⟨i,i,-1⟩]
  else step 0 []

/-- Emit the public table by four ordered arc passes, scanning variable IDs
and testing row incidence directly. The width argument is the comparison
width of one variable label. Integer primitives observe their actual inputs. -/
def emit (w : ℕ) (xs : List ν) (rows : List (IntAtom ν)) : Run Table := do
  let P ← CompilerRun.length xs
  let startRow ← natAdd 1 P
  let R ← CompilerRun.length rows
  let N ← natAdd startRow R
  let rs ← indexed rows 0
  let starts ← CompilerRun.mapM (startArc w xs) xs
  let entries ← CompilerRun.mapM (enterArc w xs startRow) rs
  let replies ← CompilerRun.flatMapM (rowArcs w xs N startRow) rs
  let idle ← CompilerRun.flatMapM (idleArcs w xs rows) xs
  let last ← append replies idle
  let rest ← append entries last
  let arcs ← append starts rest
  let vars ← CompilerRun.mapM (fun _ => step 0 true) xs
  let owners ← CompilerRun.mapM (fun _ => step 0 false) rows
  let all ← append vars owners
  step 0 ⟨0, true::all, arcs⟩

@[simp] private theorem idle_value (w : ℕ) (xs : List ν) (rs : List (IntAtom ν)) (v : ν) :
    (idleArcs w xs rs v).value = if rs.any (fun r => r.lhs == v) then [] else
      [⟨xs.idxOf v + 1, xs.idxOf v + 1,-1⟩] := by
  simp only [idleArcs, Run.bind_value, noRow_value]
  cases rs.any (fun r => r.lhs == v) <;> simp [variableId, natAdd]

theorem emit_value (w : ℕ) (vs : Listing ν) (rows : List (IntAtom ν)) :
    (emit w vs.items rows).value = ArenaEncoding.table vs rows true := by
  rw [← raw_eq]
  simp only [emit, Run.bind_value, step_value, length_value, natAdd, indexed_value,
    mapM_value, flatMapM_value, append_value, startArc, enterArc, rowArcs,
    idle_value, replyArc, signedFactor_value, intMul, intSub, variableId, findId_value, raw, flip, List.cons_append]

def slotBudget (B : ℕ) := 200 * (B+1)^3
def widthBudget (labelWidth B magnitudeBits : ℕ) := labelWidth + 4*(B+1) + magnitudeBits + 10

private theorem indexed_bound {α : Type} (xs : List α) (z W : ℕ) (hw : z+xs.length+1 ≤ W) :
    (indexed xs z).Bound (2*xs.length+1) W := by
  induction xs generalizing z with
  | nil => exact (bound_step 0 _).weaken (by simp) (by omega)
  | cons a xs ih =>
    have inc : (natAdd z 1).Bound 1 W := by
      refine (bound_step _ _).weaken le_rfl (max_le ?_ ?_)
      · exact (BinarySize.size_le_self _).trans (by omega)
      · norm_num; omega
    have rest := ih (z+1) (by simp only [List.length_cons] at hw; omega)
    unfold indexed
    refine (bound_bind inc (bound_bind rest ((bound_step 0 _).weaken le_rfl (Nat.zero_le W)))).weaken ?_ le_rfl
    simp; omega

private theorem find_bound (w : ℕ) (v : ν) (xs : List ν) (W : ℕ)
    (hw : w ≤ W) (hx : xs.length+1 ≤ W) : (findId w v xs).Bound (2*xs.length+1) W := by
  induction xs with
  | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
  | cons a xs ih =>
    simp only [List.length_cons] at hx ⊢
    have rest := ih (by omega)
    have k : (xs.idxOf v).size ≤ W := (BinarySize.size_le_self _).trans (List.idxOf_le_length.trans (by omega))
    have inc : (natAdd (findId w v xs).value 1).Bound 1 W := by
      refine (bound_step _ _).weaken le_rfl ?_
      exact max_le (by simpa using k) (by norm_num; omega)
    unfold findId
    refine (bound_bind (l := 2*xs.length+2) ((bound_step w _).weaken le_rfl hw) ?_).weaken ?_ le_rfl
    · simp only [step_value]
      by_cases eq : (a == v) = true <;> simp only [eq, ↓reduceIte]
      · exact (bound_pure _ _).weaken (Nat.zero_le (2*xs.length+2)) le_rfl
      · exact bound_bind (k := 2*xs.length+1) (l := 1) rest inc
    · omega

private theorem noRow_bound (w : ℕ) (v : ν) (xs : List (IntAtom ν)) (W : ℕ) (hw : w ≤ W) :
    (noRow w v xs).Bound (xs.length+1) W := by
  induction xs with
  | nil => exact (bound_step 0 _).weaken (by simp) (Nat.zero_le _)
  | cons a xs ih =>
    unfold noRow
    refine (bound_bind (l := xs.length+1) ((bound_step w _).weaken le_rfl hw) ?_).weaken ?_ le_rfl
    · simp only [step_value]
      by_cases eq : (a.lhs == v) = true <;> simp only [eq, ↓reduceIte]
      · exact (bound_pure _ _).weaken (Nat.zero_le (xs.length+1)) le_rfl
      · exact ih
    · simp; omega

private theorem id_bound (w : ℕ) (xs : List ν) (v : ν) (B M : ℕ) (hx : xs.length ≤ B) :
    (variableId w xs v).Bound (2*B+2) (widthBudget w B M) := by
  let W := widthBudget w B M
  have h := find_bound w v xs W (by dsimp [W, widthBudget]; omega) (by dsimp [W, widthBudget]; omega)
  have hi := BinarySize.size_le_self (xs.idxOf v)
  have hi' : xs.idxOf v ≤ xs.length := List.idxOf_le_length
  unfold variableId
  apply (bound_bind h ((bound_step _ _).weaken le_rfl ?_)).weaken (by omega) le_rfl
  simp only [findId_value, max_le_iff]
  dsimp [W, widthBudget]
  exact ⟨by omega, (BinarySize.size_le_self 1).trans (by omega)⟩

private theorem start_bound (w : ℕ) (xs : List ν) (v : ν) (B M : ℕ) (hx : xs.length ≤ B) :
    (startArc w xs v).Bound (2*B+3) (widthBudget w B M) :=
  bound_bind (k := 2*B+2) (l := 1) (id_bound w xs v B M hx) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))

private theorem add_bound (a b W : ℕ) (ha : a ≤ W) (hb : b ≤ W) :
    (natAdd a b).Bound 1 W := (bound_step _ _).weaken le_rfl (max_le
      ((BinarySize.size_le_self _).trans ha) ((BinarySize.size_le_self _).trans hb))

private theorem enter_bound (w : ℕ) (xs : List ν) (p B M : ℕ) (r : IntAtom ν × ℕ)
    (hx : xs.length ≤ B) (hp : p ≤ B+1) (hr : r.2 ≤ B) :
    (enterArc w xs p r).Bound (2*B+4) (widthBudget w B M) := by
  unfold enterArc
  exact bound_bind (k := 2*B+2) (l := 2) (id_bound w xs r.1.lhs B M hx) (bound_bind (k := 1) (l := 1) (add_bound p r.2 (widthBudget w B M)
    (by unfold widthBudget; omega) (by unfold widthBudget; omega))
    ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))

private theorem reply_bound (w : ℕ) (xs : List ν) (N i B M : ℕ) (t : ν × ℤ)
    (hx : xs.length ≤ B) (hN : N ≤ 2*B+1) (hm : t.2.natAbs.size ≤ M) :
    (replyArc w xs N i t).Bound (2*B+7) (widthBudget w B M) := by
  let W := widthBudget w B M
  have hsize := BinarySize.size_le_self N
  have prod := BinarySize.size_mul_le N t.2.natAbs
  have factor : (signedFactor N).Bound 2 W := by
    unfold signedFactor
    apply bound_bind (k := 1) (l := 1)
    · exact (bound_step _ _).weaken le_rfl (by dsimp [W, widthBudget]; omega)
    · apply (bound_step _ _).weaken le_rfl
      simp [W, widthBudget]; omega
  have a : (intMul (-(N : ℤ)) t.2).Bound 1 W := by
    refine (bound_step _ _).weaken le_rfl ?_
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    dsimp [W, widthBudget]; omega
  have b : (intSub (intMul (-(N : ℤ)) t.2).value 1).Bound 1 W := by
    refine (bound_step _ _).weaken le_rfl ?_
    simp only [intMul, step_value, Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_one]
    dsimp [W, widthBudget]; norm_num; omega
  unfold replyArc
  apply bound_bind (k := 2*B+2) (l := 5) (id_bound w xs t.1 B M hx)
  apply bound_bind (k := 2) (l := 3) factor
  rw [signedFactor_value]
  exact bound_bind (k := 1) (l := 2) a
    (bound_bind (k := 1) (l := 1) b ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))

private theorem idle_bound (w : ℕ) (xs : List ν) (rows : List (IntAtom ν)) (v : ν) (B M : ℕ)
    (hx : xs.length ≤ B) (hr : rows.length ≤ B) :
    (idleArcs w xs rows v).Bound (3*B+4) (widthBudget w B M) := by
  unfold idleArcs
  refine (bound_bind (l := 2*B+3) (noRow_bound w v rows _ (by unfold widthBudget; omega)) ?_).weaken ?_ le_rfl
  · split
    · exact bound_bind (k := 2*B+2) (l := 1) (id_bound w xs v B M hx) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _))
    · exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)
  · omega

private theorem phase {α β : Type} {p : Run α} {f : α → Run β} {W K : ℕ}
    (n : ℕ) (h : p.Bound K W) (rest : (f p.value).Bound (n*K) W) :
    (p >>= f).Bound ((n+1)*K) W :=
  (bound_bind h rest).weaken (by rw [Nat.add_mul]; simp [Nat.add_comm]) le_rfl

private theorem flat_length {α β : Type} (xs : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ n) : (xs.flatMap f).length ≤ xs.length * n := by
  rw [List.length_flatMap]
  simpa only [List.length_map, nsmul_eq_mul, Nat.cast_id] using
    List.sum_le_length_nsmul (xs.map (fun x => (f x).length)) n (by simpa using h)

set_option maxHeartbeats 1000000 in
theorem emit_bound (w : ℕ) (xs : List ν) (rows : List (IntAtom ν)) (B M : ℕ)
    (hx : xs.length ≤ B) (hr : rows.length ≤ B)
    (ht : ∀ r ∈ rows, r.terms.length ≤ B)
    (hm : ∀ r ∈ rows, ∀ t ∈ r.terms, t.2.natAbs.size ≤ M) :
    (emit w xs rows).Bound (slotBudget B) (widthBudget w B M) := by
  let W := widthBudget w B M
  let K := 10*(B+1)^3
  let P := 1+xs.length
  let N := P+rows.length
  let rs := rows.zipIdx
  have wr : 2*B+2 ≤ W := by dsimp [W,widthBudget]; omega
  have hp : P ≤ B+1 := by dsimp [P]; omega
  have hn : N ≤ 2*B+1 := by dsimp [N]; omega
  have rslen : rs.length ≤ B := by simpa [rs] using hr
  have heads := mapM_bound (startArc w xs) xs (2*B+3) W (fun v _ => start_bound w xs v B M hx)
  have entries := mapM_bound (enterArc w xs P) rs (2*B+4) W (fun r mem =>
    enter_bound w xs P B M r hx hp (by
      have := List.snd_lt_add_of_mem_zipIdx mem
      omega))
  have rowLength (r : IntAtom ν × ℕ) (mem : r ∈ rs) :
      (rowArcs w xs N P r).value.length ≤ B := by
    simpa [rowArcs] using ht r.1 (List.fst_mem_of_mem_zipIdx mem)
  have rowsBound (r : IntAtom ν × ℕ) (mem : r ∈ rs) :
      (rowArcs w xs N P r).Bound (B*(2*B+9)+2) W := by
    have inr := List.fst_mem_of_mem_zipIdx mem
    have ri := List.snd_lt_add_of_mem_zipIdx mem
    have mi (i : ℕ) := mapM_bound (replyArc w xs N i) r.1.terms (2*B+7) W
      (fun t mt => reply_bound w xs N i B M t hx hn (hm r.1 inr t mt))
    unfold rowArcs
    apply (bound_bind (add_bound P r.2 W (by omega) (by omega)) (mi _)).weaken _ le_rfl
    have hh := Nat.mul_le_mul_right (2*B+9) (ht _ inr)
    change 1+(r.1.terms.length*(2*B+9)+1) ≤ B*(2*B+9)+2
    omega
  have replies := flatMapM_bound (rowArcs w xs N P) rs (B*(2*B+9)+2) B W rowsBound rowLength
  have idleLength (v : ν) : (idleArcs w xs rows v).value.length ≤ 1 := by
    rw [idle_value]; split <;> simp
  have idles := flatMapM_bound (idleArcs w xs rows) xs (3*B+4) 1 W
    (fun v _ => idle_bound w xs rows v B M hx hr) (fun v _ => idleLength v)
  have sizeReplies : (CompilerRun.flatMapM (rowArcs w xs N P) rs).value.length ≤ B*B := by
    rw [flatMapM_value]
    exact (flat_length rs _ _ rowLength).trans (Nat.mul_le_mul_right _ rslen)
  have copies {α : Type} (as : List α) (c : Bool) :
      (CompilerRun.mapM (fun _ => step 0 c) as).Bound (as.length*3+1) W :=
    mapM_bound _ _ 1 W fun _ _ => (bound_step 0 _).weaken le_rfl (Nat.zero_le _)
  have small : 4*(B+1)^2+2 ≤ K := by dsimp [K]; nlinarith [Nat.zero_le (B^3)]
  have limit : B*(B*(2*B+9)+2+B+2)+1 ≤ K := by dsimp [K]; nlinarith
  have budgetHead : xs.length*(2*B+3+2)+1 ≤ K := by
    apply le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hx) _); dsimp [K]; nlinarith
  have budgetEnter : rs.length*(2*B+4+2)+1 ≤ K := by
    apply le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ rslen) _); dsimp [K]; nlinarith
  have budgetIdle : xs.length*(3*B+4+1+2)+1 ≤ K := by
    apply le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hx) _); dsimp [K]; nlinarith
  have large : B*B + 10*B+10 ≤ K := by dsimp [K]; nlinarith
  suffices bound : (emit w xs rows).Bound (16*K) W from
    bound.weaken (by dsimp [slotBudget,K]; omega) le_rfl
  unfold emit
  apply phase 15 ((length_bound xs).weaken (by omega) ((BinarySize.size_le_self _).trans (by omega)))
  simp only [length_value]
  apply phase 14 ((add_bound 1 xs.length W (by omega) (by omega)).weaken (by omega) le_rfl)
  apply phase 13 ((length_bound rows).weaken (by omega) ((BinarySize.size_le_self _).trans (by omega)))
  simp only [length_value]
  apply phase 12 ((add_bound P rows.length W (by omega) (by omega)).weaken (by omega) le_rfl)
  apply phase 11 ((indexed_bound rows 0 W (by omega)).weaken (by omega) le_rfl)
  simp only [indexed_value]
  apply phase 10 (heads.weaken budgetHead le_rfl)
  apply phase 9 (entries.weaken budgetEnter le_rfl)
  apply phase 8 (replies.weaken ((Nat.add_le_add_right (Nat.mul_le_mul_right _ rslen) 1).trans limit) le_rfl)
  apply phase 7 (idles.weaken budgetIdle le_rfl)
  apply phase 6 ((append_bound _ _ W).weaken (by omega) le_rfl)
  apply phase 5 ((append_bound _ _ W).weaken (by simp only [mapM_value, List.length_map]; omega) le_rfl)
  apply phase 4 ((append_bound _ _ W).weaken (by simp only [mapM_value, List.length_map]; omega) le_rfl)
  apply phase 3 ((copies xs true).weaken (by omega) le_rfl)
  apply phase 2 ((copies rows false).weaken (by omega) le_rfl)
  apply phase 1 ((append_bound _ _ W).weaken (by simp only [mapM_value, List.length_map]; omega) le_rfl)
  exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)

open AtomEncoding

/-- A packed compiler label has a two-bit constructor field and up to two
unsigned index fields. Equality of such labels is one word comparison. -/
def labelWidth (n a r : ℕ) := 2 + n.size + a.size + (r+1).size

/-- Compute the comparison width before dispatching to the arena emitter. -/
def labelWidthRun (n a r : ℕ) : Run ℕ := do
  let rounds ← natAdd r 1
  let ns ← step n.size n.size
  let as ← step a.size a.size
  let ts ← step rounds.size rounds.size
  let s ← natAdd 2 ns
  let u ← natAdd s as
  natAdd u ts

@[simp] theorem labelWidthRun_value (n a r : ℕ) : (labelWidthRun n a r).value = labelWidth n a r := by
  simp [labelWidthRun, labelWidth, natAdd]

theorem labelWidthRun_bound (n a r : ℕ) : (labelWidthRun n a r).Bound 7 (n+a+r+4) := by
  have hn := BinarySize.size_le_self n
  have ha := BinarySize.size_le_self a
  have hr := BinarySize.size_le_self (r+1)
  unfold labelWidthRun
  apply bound_bind (k := 1) (l := 6) (add_bound _ _ _ (by omega) (by omega))
  apply bound_bind (k := 1) (l := 5) ((bound_step _ _).weaken le_rfl (by omega))
  apply bound_bind (k := 1) (l := 4) ((bound_step _ _).weaken le_rfl (by omega))
  apply bound_bind (k := 1) (l := 3) ((bound_step _ _).weaken le_rfl (by change (r+1).size ≤ _; omega))
  apply bound_bind (k := 1) (l := 2) (add_bound _ _ _ (by omega) (by simpa using hn.trans (by omega)))
  apply bound_bind (k := 1) (l := 1) (add_bound _ _ _ (by change 2+n.size ≤ _; omega) (by change a.size ≤ _; omega))
  exact add_bound _ _ _ (by change 2+n.size+a.size ≤ _; omega) (by change (r+1).size ≤ _; omega)

def labelBits {n a r : ℕ} : Var (Fin n) a r → ℕ
  | .reference => 2
  | .source i => 2 + i.val.size
  | .high i j | .low i j => 2 + i.val.size + j.val.size

theorem labelBits_le {n a r : ℕ} (v : Var (Fin n) a r) : labelBits v ≤ labelWidth n a r := by
  cases v with
  | reference => dsimp [labelBits, labelWidth]; omega
  | source i =>
    have := Nat.size_le_size i.isLt.le
    dsimp [labelBits, labelWidth]; omega
  | high i j | low i j =>
    have := Nat.size_le_size i.isLt.le
    have := Nat.size_le_size j.isLt.le
    dsimp [labelBits, labelWidth]; omega

/-- The equality witness transports the finite-index type, while the range
enumerator consumes the actual result of the measured increment. -/
def roundRange (r : ℕ) : Run (List (Fin (r+1))) := do
  let add := natAdd r 1
  let next ← (⟨⟨add.value,rfl⟩,add.work⟩ : Run {k : ℕ // k = r+1})
  next.property ▸ CompilerRun.finRange next.val

@[simp] theorem roundRange_value (r : ℕ) :
    (roundRange r).value = List.finRange (r+1) := finRange_value _

private theorem roundRange_bound (r B : ℕ) (hr : r+1 ≤ B) :
    (roundRange r).Bound (1+(2*(r+1)+1)) (B+1) := by
  unfold roundRange
  apply bound_bind (k := 1) (l := 2*(r+1)+1)
  · exact (add_bound r 1 (B+1) (by omega) (by omega))
  · exact (finRange_bound (r+1)).weaken le_rfl ((BinarySize.size_le_self (r+1)).trans (by omega))

/-- Enumerate both families of rounded wires in the same row-major order as
the typed arena. Each constructor is emitted by a measured traversal. -/
def variableItems (n a r : ℕ) : Run (List (Var (Fin n) a r)) := do
  let src ← CompilerRun.finRange n
  let rows ← CompilerRun.finRange a
  let times ← roundRange r
  let ss ← CompilerRun.mapM (fun i => step 0 (Var.source i)) src
  let hs ← CompilerRun.flatMapM (fun i => CompilerRun.mapM (fun j => step 0 (Var.high i j)) times) rows
  let ls ← CompilerRun.flatMapM (fun i => CompilerRun.mapM (fun j => step 0 (Var.low i j)) times) rows
  let wires ← append hs ls
  let all ← append ss wires
  step 0 (.reference :: all)

theorem variableItems_value (n a r : ℕ) :
    (variableItems n a r).value = (compilerVariables n a r).items := by
  simp [variableItems, compilerVariables, Listing.fin, Listing.map, Listing.option,
    Listing.sum, Listing.product, List.map_flatMap, SProd.sprod, List.product, List.map_map,
    Function.comp_def]

theorem variableItems_bound (n a r B : ℕ) (hn : n ≤ B) (ha : a ≤ B) (hr : r+1 ≤ B) :
    (variableItems n a r).Bound (100*(B+1)^2) (B+1) := by
  let K := 10*(B+1)^2
  let W := B+1
  have large : 4*B*B + 4*B+2 ≤ K := by dsimp [K]; nlinarith
  have range (v : ℕ) (hv : v ≤ B) :=
    (finRange_bound v).weaken (show 2*v+1 ≤ K by omega) ((BinarySize.size_le_self _).trans (hv.trans (Nat.le_succ _)))
  let sources (i : Fin n) := step 0 (Var.source i : Var (Fin n) a r)
  have sm := mapM_bound sources (List.finRange n) 1 W (fun _ _ => (bound_step 0 _).weaken le_rfl (Nat.zero_le _))
  have wires (f : Fin a → Fin (r+1) → Var (Fin n) a r) :
      (CompilerRun.flatMapM (fun i => CompilerRun.mapM (fun j => step 0 (f i j)) (List.finRange (r+1)))
        (List.finRange a)).Bound K W := by
    apply (flatMapM_bound _ _ ((r+1)*3+1) (r+1) W ?_ ?_).weaken _ le_rfl
    · intro i _
      simpa using mapM_bound (fun j => step 0 (f i j)) (List.finRange (r+1)) 1 W
        (fun _ _ => (bound_step 0 _).weaken le_rfl (Nat.zero_le _))
    · simp
    · simp only [List.length_finRange]
      dsimp [K]
      calc
        _ ≤ B * (B * 3 + 1 + B + 2) + 1 := by gcongr
        _ ≤ _ := by nlinarith
  have highLength : (CompilerRun.flatMapM (fun i =>
      CompilerRun.mapM (fun j => step 0 (Var.high i j : Var (Fin n) a r)) (List.finRange (r+1)))
      (List.finRange a)).value.length + 1 ≤ K := by
    simp only [flatMapM_value, mapM_value, step_value]
    have hl := flat_length (List.finRange a) (fun i => (List.finRange (r+1)).map
      (fun j => (Var.high i j : Var (Fin n) a r))) (r+1) (by simp)
    simp only [List.length_finRange] at hl
    have hmul := Nat.mul_le_mul ha hr
    have wide : B*B+1 ≤ K := by dsimp [K]; nlinarith
    omega
  suffices h : (variableItems n a r).Bound (9*K) W from h.weaken (by dsimp [K]; omega) le_rfl
  unfold variableItems
  apply phase 8 (range n hn)
  apply phase 7 (range a ha)
  apply phase 6 ((roundRange_bound r B hr).weaken (by omega) le_rfl)
  simp only [finRange_value, roundRange_value]
  apply phase 5 (sm.weaken (by simp only [List.length_finRange]; omega) le_rfl)
  apply phase 4 (wires Var.high)
  apply phase 3 (wires Var.low)
  apply phase 2 ((append_bound _ _ W).weaken highLength le_rfl)
  apply phase 1 ((append_bound _ _ W).weaken (by simp only [mapM_value,List.length_map,List.length_finRange]; omega) le_rfl)
  exact (bound_step 0 _).weaken (by omega) (Nat.zero_le _)

end StochasticGames.CostedArena
