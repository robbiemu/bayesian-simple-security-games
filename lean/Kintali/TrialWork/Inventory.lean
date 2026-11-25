module

public import Kintali.RetainedQuotes
public import Kintali.TrialWork.Fields
public import Kintali.TrialWork.ListBuild

/-! # Restricted bid and cut lists from the compressed selection -/

@[expose] public section

namespace Kintali.TrialWork.Inventory

open StochasticGames StochasticGames.CompilerRun QuoteSearch ExactRecovery
open Sparse ListBuild ContactSize

variable {k m G : ℕ}

def parse (G : ℕ) : List ℕ → Run (List (Quote G))
  | [] => step 0 []
  | z::zs => do
    let _ ← step (max z.size G.size) ()
    let rest ← parse G zs
    step 0 (if h : z < G then ⟨z,Nat.lt_succ_of_lt h⟩::rest else rest)

@[simp] theorem parse_value (G : ℕ) (zs : List ℕ) :
    (parse G zs).value = parseQuotes G zs := by
  induction zs with
  | nil => rfl
  | cons z zs ih => by_cases h : z < G <;> simp [parse, parseQuotes, ih, h]

theorem parse_work (G : ℕ) (zs : List ℕ) {w : ℕ} (hw : G.size ≤ w)
    (fit : ∀ z ∈ zs, z.size ≤ w) : (parse G zs).Bound (1+2*zs.length) w := by
  induction zs with
  | nil => simp [parse, Run.Bound]
  | cons z zs ih =>
    obtain ⟨slots,width⟩ := ih (fun x hx => fit x (by simp [hx]))
    constructor
    · simp only [parse, Run.bind_slots, step_slots, List.length_cons]
      omega
    · exact max_le (max_le (fit z (by simp)) hw) (max_le width (Nat.zero_le _))

def test (f : Fields k m) (outside : Fin k → Run ℚ) (i : Fin k) (j : Fin m)
    (z : Quote G) : Run Bool := do
  let gain ← f.gain j
  let live ← lt 0 gain
  if live then
    let price ← divide z.val G
    let offer ← f.costAt i j price
    let reserve ← outside i
    le offer reserve
  else step 0 false

theorem test_true (f : Fields k m) (outside : Fin k → Run ℚ) (redirect : Fin k → Fin m)
    (out : ∀ i, (outside i).value = Holdings.outsideCost f.game redirect i)
    (i : Fin k) (j : Fin m) (z : Quote G) :
    (test f outside i j z).value = true ↔ Holdings.Eligible f.game redirect i j z := by
  by_cases h : 0 < f.game.gain j
  · have hg : 0 < (f.gain j).value := h
    simp [test, hg, Holdings.Eligible, Holdings.quoteCost, price, h, out]
  · have hg : ¬0 < (f.gain j).value := h
    simp [test, hg, Holdings.Eligible, h]

def pair (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m))
    (i : Fin k) (j : Fin m) : Run (List (ListedBid k m G)) := do
  let p := finProdFinEquiv (i,j)
  let indices ← step (k*m).size s[p]
  let optional ← parse G indices
  let kept ← retain (test f outside i j) (cap G::optional)
  CompilerRun.mapM (fun z => step 0 (i,j,z)) kept

theorem pair_mem (f : Fields k m) (outside : Fin k → Run ℚ) (redirect : Fin k → Fin m)
    (out : ∀ i, (outside i).value = Holdings.outsideCost f.game redirect i)
    (s : Selection (k*m)) (i : Fin k) (j : Fin m) (bid : ListedBid k m G) :
    bid ∈ (pair f outside s i j).value ↔
      bid ∈ (realAt f.game redirect s (i,j)).image (fun z => (i,j,z)) := by
  rcases bid with ⟨i',j',z⟩
  simp only [pair, Run.bind_value, step_value, parse_value, retain_value, mapM_value,
    test_true f outside redirect out, List.mem_map, List.mem_filter, List.mem_cons,
    realAt, Finset.mem_image, Finset.mem_filter, Finset.mem_insert, List.mem_toFinset, Holdings.Eligible]

def candidates (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m)) :
    Run (List (ListedBid k m G)) := do
  let is ← finRange k
  let js ← finRange m
  CompilerRun.flatMapM (fun i => CompilerRun.flatMapM (pair f outside s i) js) is

theorem candidates_mem (f : Fields k m) (outside : Fin k → Run ℚ) (redirect : Fin k → Fin m)
    (out : ∀ i, (outside i).value = Holdings.outsideCost f.game redirect i)
    (s : Selection (k*m)) (bid : ListedBid k m G) :
    bid ∈ (candidates f outside s).value ↔ bid ∈ realBids f.game redirect s := by
  simp [candidates, pair_mem f outside redirect out, realBids, Finset.mem_biUnion]

section Sorting

local instance : LinearOrder (ListedBid k m G) :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

def listed (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m))
    (cmp : ListedBid k m G → ListedBid k m G → Run Ordering) : Run (List (ListedBid k m G)) :=
  candidates f outside s >>= sortedSet cmp

theorem listed_value (f : Fields k m) (outside : Fin k → Run ℚ) (redirect : Fin k → Fin m)
    (out : ∀ i, (outside i).value = Holdings.outsideCost f.game redirect i)
    (s : Selection (k*m)) (cmp : ListedBid k m G → ListedBid k m G → Run Ordering)
    (same : ∀ x y, (cmp x y).value = compare x y) :
    (listed f outside s cmp).value = realOrder f.game redirect s := by
  simp only [listed,Run.bind_value,sortedSet_value cmp same,realOrder]
  congr 1
  ext r
  simp only [List.mem_toFinset, candidates_mem f outside redirect out]

end Sorting

def quoteCompare (a b : Quote G) : Run Ordering :=
  ⟨compare a b, ⟨2, max a.val.size b.val.size⟩⟩

theorem quoteCompare_work (a b : Quote G) {w : ℕ} (h : G.size ≤ w) :
    (quoteCompare a b).Bound 2 w := by
  have A := Nat.size_le_size (Nat.le_of_lt_succ a.isLt)
  have B := Nat.size_le_size (Nat.le_of_lt_succ b.isLt)
  exact ⟨le_rfl, max_le (A.trans h) (B.trans h)⟩

def cutLevels (bids : List (ListedBid k m G)) (j : Fin m) : Run (List ℕ) := do
  let own ← retain (fun r => step m.size (r.2.1 == j)) bids
  let quotes ← CompilerRun.mapM (fun r => step G.size r.2.2) own
  let sorted ← sortedSet quoteCompare (0 :: cap G :: quotes)
  CompilerRun.mapM (fun r => step G.size r.val) sorted

theorem cutLevels_value (f : Fields k m) (redirect : Fin k → Fin m)
    (s : Selection (k*m)) (bids : List (ListedBid k m G))
    (same : bids = realOrder f.game redirect s) (j : Fin m) :
    (cutLevels bids j).value = (siteCuts (G := G) f.game redirect s j).sort := by
  let qs : List (Quote G) := 0 :: cap G :: (bids.filter (fun r => r.2.1 == j)).map (·.2.2)
  let B := (sortedSet quoteCompare qs).value
  have hB : (cutLevels bids j).value = B.map Fin.val := by
    simp [cutLevels, B, qs]
  have spec := sortedSet_spec quoteCompare (fun x y : Quote G => rfl) qs
  have ordered : (B.map Fin.val).Pairwise (· < ·) :=
    List.pairwise_map.mpr (spec.1.imp (fun h => h))
  have target := (siteCuts (G := G) f.game redirect s j).sortedLT_sort.pairwise
  have perm : (B.map Fin.val).Perm ((siteCuts (G := G) f.game redirect s j).sort) := by
    apply (List.perm_ext_iff_of_nodup (ordered.imp (fun h => h.ne))
      (target.imp (fun h => h.ne))).mpr
    intro z
    simp only [siteCuts, Finset.mem_sort, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      List.mem_map, B, spec.2, qs, List.mem_cons]
    constructor
    · rintro ⟨x,(rfl | rfl | ⟨r,hr,rfl⟩),rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · have one := List.mem_filter.mp hr
        exact Or.inr (Or.inr ⟨r,⟨(by simpa [same, realOrder] using one.1),
          by simpa using one.2⟩,rfl⟩)
    · rintro (rfl | rfl | ⟨r,⟨hr,hrj⟩,rfl⟩)
      · exact ⟨0,Or.inl rfl,rfl⟩
      · exact ⟨cap _,Or.inr (Or.inl rfl),rfl⟩
      · exact ⟨r.2.2, Or.inr (Or.inr ⟨r, List.mem_filter.mpr
          ⟨by simpa [same, realOrder] using hr, by simpa using hrj⟩, rfl⟩),rfl⟩
  rw [hB]
  exact perm.eq_of_pairwise' (ordered.imp (fun h => h.le)) (target.imp (fun h => h.le))

theorem cutLevels_work (bids : List (ListedBid k m G)) (j : Fin m) {w : ℕ}
    (grid : G.size ≤ w) (sites : m.size ≤ w) :
    (cutLevels bids j).Bound (20 * (bids.length+3)^2) w := by
  let choose (r : ListedBid k m G) := step m.size (r.2.1 == j)
  let own := retain choose bids
  let prices := CompilerRun.mapM (fun r : ListedBid k m G => step G.size r.2.2) own.value
  let sorted := sortedSet quoteCompare (0 :: cap G :: prices.value)
  let values := CompilerRun.mapM (fun r : Quote G => step G.size r.val) sorted.value
  have kept := retain_work choose bids (fun _ _ => ⟨le_rfl, sites⟩)
  have mapped := mapM_bound (fun r : ListedBid k m G => step G.size r.2.2) own.value 1 w
    (fun _ _ => ⟨le_rfl, grid⟩)
  have sorting := sortedSet_work quoteCompare (0 :: cap G :: prices.value)
    (fun x y => quoteCompare_work x y grid)
  have numeric := mapM_bound (fun r : Quote G => step G.size r.val) sorted.value 1 w
    (fun _ _ => ⟨le_rfl, grid⟩)
  have lenO : own.value.length ≤ bids.length := by simp [own, List.length_filter_le]
  have lenP : prices.value.length = own.value.length := by simp [prices]
  have lenS := sortedSet_length quoteCompare (0 :: cap G :: prices.value)
  have sel : sorted.value.length ≤ bids.length+2 := by
    change sorted.value.length ≤ _ at lenS
    simp only [List.length_cons] at lenS
    omega
  have limit : (0 :: cap G :: prices.value).length ≤ bids.length+2 := by simp; omega
  have product : (0 :: cap G :: prices.value).length * ((0 :: cap G :: prices.value).length+1) * (2+4) ≤
      (bids.length+2)*(bids.length+3)*6 :=
    Nat.mul_le_mul_right 6 (Nat.mul_le_mul limit (by omega))
  constructor
  · change own.work.slots + (prices.work.slots + (sorted.work.slots + values.work.slots)) ≤ _
    have a := kept.1
    have b := mapped.1
    have c := sorting.1
    have d := numeric.1
    have hquad : (bids.length+2)*(bids.length+3)*6 ≤ (bids.length+3)^2 * 6 := by
      rw [pow_two]
      gcongr
      omega
    nlinarith
  · exact max_le kept.2 (max_le mapped.2 (max_le sorting.2 numeric.2))


end Kintali.TrialWork.Inventory
