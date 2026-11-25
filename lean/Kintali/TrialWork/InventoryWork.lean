module

public import Kintali.TrialWork.Inventory
public import Kintali.TrialWork.SelectedLists
public import Kintali.QuotaSweep.EncodedKeyRun

/-! # Word bounds for parsing and comparing the selected bids -/

@[expose] public section

namespace Kintali.TrialWork.Inventory

open StochasticGames StochasticGames.CompilerRun ExactRecovery QuoteSearch
open Sparse ListBuild ContactSize

variable {k m G : ℕ}

def testSlots (w c : ℕ) :=
  2*c + 12 + scalarSlots (w+1) + costSlots c (2*(w+1))

def testWidth (w : ℕ) := scalarWidth (6*(w+1)+1)

theorem test_work (f : Fields k m) (outside : Fin k → Run ℚ) {w c : ℕ}
    (d : FieldBound f c w) (hg : G.size ≤ w)
    (outsideWork : ∀ i, (outside i).Bound c w ∧ Fits w (outside i).value)
    (i : Fin k) (j : Fin m) (z : Quote G) :
    (test f outside i j z).Bound (testSlots w c) (testWidth w) := by
  let q := (z.val : ℚ) / G
  let wide := testWidth w
  have hf : Fits (w+1) (z.val : ℚ) := (Fits.natCast _).mono
    (Nat.add_le_add_right ((Nat.size_le_size (Nat.le_of_lt_succ z.isLt)).trans hg) 1)
  have hg' : Fits (w+1) (G : ℚ) := (Fits.natCast _).mono (Nat.add_le_add_right hg 1)
  have price := divide_work hf hg'
  have qfit : Fits (2*(w+1)) q := (hf.div hg').mono (by omega)
  have dw := d.mono (show w ≤ 2*(w+1) by omega)
  have offer := f.costAt_work dw i j qfit
  have wf : Fits (6*(w+1)+1) (f.game.cost i j q) :=
    (f.cost_fits dw i j qfit).mono (by omega)
  have final := le_work wf ((outsideWork i).2.mono (by omega))
  have live := lt_work (Fits.zero.mono d.positive) (d.gain j).2
  have aw : w ≤ wide := by unfold wide testWidth scalarWidth; omega
  have al : scalarWidth w ≤ wide := by unfold wide testWidth scalarWidth; omega
  have ap : scalarWidth (w+1) ≤ wide := by unfold wide testWidth scalarWidth; omega
  have ao : costWidth (2*(w+1)) ≤ wide := by unfold wide testWidth costWidth scalarWidth; omega
  cases yes : (lt 0 (f.gain j).value).value with
  | false =>
    constructor
    · simp only [test, Run.bind_slots, step_slots, Bool.false_eq_true, ite_false, yes]
      have := (d.gain j).1.1
      have := live.1
      unfold testSlots
      omega
    · simp only [test, Run.bind_width, step_width, Bool.false_eq_true, ite_false, yes, max_le_iff]
      exact ⟨(d.gain j).1.2.trans aw, live.2.trans al, Nat.zero_le _⟩
  | true =>
    constructor
    · simp only [test, Run.bind_slots, yes, ite_true, divide_value, Fields.costAt_value]
      have := (d.gain j).1.1
      have := (outsideWork i).1.1
      have := live.1
      have := price.1
      have so : (f.costAt i j ((z.val : ℚ)/G)).work.slots ≤ costSlots c (2*(w+1)) := offer.1
      have hf := final.1
      dsimp [q] at hf
      unfold testSlots
      omega
    · simp only [test, Run.bind_width, yes, ite_true, divide_value, Fields.costAt_value, max_le_iff]
      exact ⟨(d.gain j).1.2.trans aw, live.2.trans al, price.2.trans ap, offer.2.trans ao,
        (outsideWork i).1.2.trans aw, final.2⟩

theorem pair_length (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m))
    (i : Fin k) (j : Fin m) :
    (pair (G := G) f outside s i j).value.length ≤ s[finProdFinEquiv (i,j)].length+1 := by
  simp [pair]
  exact (List.length_filter_le _ _).trans (Nat.succ_le_succ (List.length_filterMap_le _ _))

def pairSlots (J w c : ℕ) := 10 + 2*J + (J+1)*(testSlots w c+4)

theorem pair_work (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m))
    (i : Fin k) (j : Fin m) {J w c : ℕ} (d : FieldBound f c w) (hg : G.size ≤ w)
    (outsideWork : ∀ i, (outside i).Bound c w ∧ Fits w (outside i).value)
    (idx : (k*m).size ≤ w) (short : s[finProdFinEquiv (i,j)].length ≤ J)
    (quotes : ∀ z ∈ s[finProdFinEquiv (i,j)], z ≤ G) :
    (pair (G := G) f outside s i j).Bound (pairSlots J w c) (testWidth w) := by
  let ids := s[finProdFinEquiv (i,j)]
  let parsed := parse G ids
  let kept := retain (test f outside i j) (cap G::parsed.value)
  have width : w ≤ testWidth w := by unfold testWidth scalarWidth; omega
  have parseB := (parse_work G ids hg (fun z hz => (Nat.size_le_size (quotes z hz)).trans hg)).weaken
    le_rfl width
  have retainB := retain_work (test f outside i j) (cap G::parsed.value)
    (fun a _ => test_work f outside d hg outsideWork i j a)
  have tag := mapM_bound (fun z : Quote G => step 0 (i,j,z)) kept.value
    1 (testWidth w) fun _ _ => ⟨le_rfl,Nat.zero_le _⟩
  have plen : (cap G::parsed.value).length ≤ J+1 := by
    have h : (parseQuotes G ids).length ≤ ids.length := List.length_filterMap_le _ _
    simpa [parsed] using Nat.succ_le_succ (h.trans short)
  have klen : kept.value.length ≤ J+1 := by
    simpa [kept] using (List.length_filter_le _ (cap G::parsed.value)).trans plen
  constructor
  · change 1 + (parsed.work.slots + (kept.work.slots +
      (CompilerRun.mapM (fun z : Quote G => step 0 (i,j,z)) kept.value).work.slots)) ≤ _
    have hp : parsed.work.slots ≤ 1+2*ids.length := parseB.1
    have hk : kept.work.slots ≤ 1+(cap G::parsed.value).length*(testSlots w c+1) := retainB.1
    have ht := tag.1
    have hJ : ids.length ≤ J := short
    have hmul := Nat.mul_le_mul_right (testSlots w c+1) plen
    unfold pairSlots
    rw [Nat.mul_add (J+1) (testSlots w c+1) 3]
    omega
  · exact max_le (idx.trans width) (max_le parseB.2 (max_le retainB.2 tag.2))

private theorem flat_length {α β : Type} (l : List α) (f : α → List β) {n : ℕ}
    (short : ∀ a ∈ l, (f a).length ≤ n) : (l.flatMap f).length ≤ l.length*n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    rw [Nat.add_comm (l.length*n) n]
    exact Nat.add_le_add (short a (by simp)) (ih (fun b hb => short b (by simp [hb])))

theorem candidates_length (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m)) (J : ℕ)
    (short : ∀ p : Fin (k*m), s[p].length ≤ J) :
    (candidates (G := G) f outside s).value.length ≤ k*m*(J+1) := by
  have row (i : Fin k) : ((List.finRange m).flatMap (fun j => (pair (G := G) f outside s i j).value)).length ≤
      m*(J+1) := by
    exact (flat_length _ _ (fun j _ => (pair_length f outside s i j).trans
      (Nat.add_le_add_right (short _) 1))).trans_eq (by simp)
  simp only [candidates, Run.bind_value, finRange_value, flatMapM_value]
  exact (flat_length _ _ (fun i _ => row i)).trans_eq (by simp [Nat.mul_assoc])

def allPairSlots (k m J w c : ℕ) :=
  2*k+2*m+3+k*(m*(pairSlots J w c + (J+1) + 2) + 1 + m*(J+1) + 2)

theorem candidates_work (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m))
    {J w c : ℕ} (d : FieldBound f c w) (hg : G.size ≤ w)
    (outsideWork : ∀ i, (outside i).Bound c w ∧ Fits w (outside i).value)
    (idx : (k*m).size ≤ w) (short : ∀ p : Fin (k*m), s[p].length ≤ J)
    (quotes : ∀ (p : Fin (k*m)) z, z ∈ s[p] → z ≤ G) :
    (candidates (G := G) f outside s).Bound (allPairSlots k m J w c) (testWidth w) := by
  let row (i : Fin k) := CompilerRun.flatMapM (pair (G := G) f outside s i) (List.finRange m)
  have wide : w ≤ testWidth w := by unfold testWidth scalarWidth; omega
  have pairLen (i : Fin k) (j : Fin m) : (pair (G := G) f outside s i j).value.length ≤ J+1 :=
    (pair_length f outside s i j).trans (Nat.add_le_add_right (short _) 1)
  have rowLen (i : Fin k) : (row i).value.length ≤ m*(J+1) := by
    simp only [row, flatMapM_value]
    exact (flat_length _ _ (fun j _ => pairLen i j)).trans_eq (by simp)
  have rowCost (i : Fin k) : (row i).Bound (m*(pairSlots J w c+(J+1)+2)+1) (testWidth w) := by
    simpa [row] using flatMapM_bound (pair (G := G) f outside s i) (List.finRange m)
      (pairSlots J w c) (J+1) (testWidth w)
      (fun j _ => pair_work f outside s i j d hg outsideWork idx (short _) (quotes _)) (fun j _ => pairLen i j)
  have cost := flatMapM_bound row (List.finRange k) _ (m*(J+1)) (testWidth w)
    (fun i _ => rowCost i) (fun i _ => rowLen i)
  constructor
  · simp only [candidates, Run.bind_slots, finRange_value]
    have h1 := (finRange_bound k).1
    have h2 := (finRange_bound m).1
    have h3 := cost.1
    simp only [List.length_finRange] at h3
    change (finRange k).work.slots + ((finRange m).work.slots +
      (CompilerRun.flatMapM row (List.finRange k)).work.slots) ≤ _
    unfold allPairSlots
    omega
  · simp only [candidates, Run.bind_width, finRange_value]
    exact max_le ((finRange_bound k).2.trans (d.kSize.trans wide))
      (max_le ((finRange_bound m).2.trans (d.mSize.trans wide)) cost.2)


section Sorting

open Kintali.QuotaSweep.StoredLookup

def bidKey (a : ListedBid k m G) : Run ℕ := do
  let i ← finKey a.1
  let j ← finKey a.2.1
  let z ← finKey a.2.2
  let tail ← pairKey j z
  pairKey i tail

@[simp] theorem bidKey_value (a : ListedBid k m G) :
    (bidKey a).value = Encodable.encode a := by
  simp [bidKey]
  rfl

private theorem pair_size {a b w : ℕ} (ha : a.size ≤ w) (hb : b.size ≤ w) :
    (Nat.pair a b).size ≤ 2*w := by
  apply Nat.size_le.mpr
  have h := max_lt (Nat.size_le.mp ha) (Nat.size_le.mp hb)
  calc
    _ < (max a b+1)^2 := Nat.pair_lt_max_add_one_sq ..
    _ ≤ (2^w)^2 := Nat.pow_le_pow_left (by omega) _
    _ = 2^(2*w) := by rw [← pow_mul, Nat.mul_comm w 2]

theorem bidKey_bound {w : ℕ} (hk : k.size ≤ w) (hm : m.size ≤ w) (hg : G.size ≤ w) :
    KeyBound (@bidKey k m G) 11 (4*w+2) := by
  constructor
  · intro a
    let i := a.1
    let j := a.2.1
    let z := a.2.2
    have si := (finKey_bound hk).size i
    have sj := (finKey_bound hm).size j
    have sz : z.val.size ≤ w := (Nat.size_le_size (Nat.le_of_lt_succ z.isLt)).trans hg
    have tail := pairKey_work j.val z.val sj sz
    have tailSize := pair_size sj sz
    have icoord := (finKey_bound hk).work i
    have jcoord := (finKey_bound hm).work j
    have zcoord : (finKey z).Bound 1 w := ⟨le_rfl,sz⟩
    have all := pairKey_work i.val (Nat.pair j.val z.val) (si.trans (by omega : w ≤ 2*w)) tailSize
    constructor
    · simp only [bidKey, Run.bind_slots, finKey_value, pairKey_value]
      exact Nat.add_le_add icoord.1 (Nat.add_le_add jcoord.1
        (Nat.add_le_add zcoord.1 (Nat.add_le_add tail.1 all.1)))
    · simp only [bidKey, Run.bind_width, finKey_value, pairKey_value, max_le_iff]
      exact ⟨icoord.2.trans (by omega),jcoord.2.trans (by omega),zcoord.2.trans (by omega),
        tail.2.trans (by omega), all.2.trans (by omega)⟩
  · intro a
    have si := (finKey_bound hk).size a.1
    have sj := (finKey_bound hm).size a.2.1
    have sz : (Encodable.encode a.2.2).size ≤ w :=
      (Nat.size_le_size (Nat.le_of_lt_succ a.2.2.isLt)).trans hg
    have tailSize := pair_size sj sz
    have all := pair_size (si.trans (by omega : w ≤ 2*w)) tailSize
    rw [bidKey_value, Encodable.encode_prod_val, Encodable.encode_prod_val]
    simp only [finKey_value] at all
    exact all.trans (by omega)

local instance : LinearOrder (ListedBid k m G) :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

def bidCompare (a b : ListedBid k m G) : Run Ordering := do
  let x ← bidKey a
  let y ← bidKey b
  ⟨compare x y, ⟨2,max x.size y.size⟩⟩

@[simp] theorem bidCompare_value (a b : ListedBid k m G) :
    (bidCompare a b).value = compare a b := by
  simp only [bidCompare, Run.bind_value, bidKey_value]
  rfl

theorem bidCompare_work {w : ℕ} (hk : k.size ≤ w) (hm : m.size ≤ w) (hg : G.size ≤ w)
    (a b : ListedBid k m G) :
    (bidCompare a b).Bound 24 (4*w+2) := by
  have key := bidKey_bound (k := k) (m := m) (G := G) hk hm hg
  exact ⟨Nat.add_le_add (key.work a).1 (Nat.add_le_add (key.work b).1 le_rfl),
    max_le (key.work a).2 (max_le (key.work b).2 (max_le (key.size a) (key.size b)))⟩

def realSlots (k m J w c : ℕ) :=
  let R := k*m*(J+1)
  allPairSlots k m J w c + (1+R*(R+1)*28)

theorem listed_work (f : Fields k m) (outside : Fin k → Run ℚ) (s : Selection (k*m))
    {J w c : ℕ} (d : FieldBound f c w) (hg : G.size ≤ w)
    (outsideWork : ∀ i, (outside i).Bound c w ∧ Fits w (outside i).value)
    (idx : (k*m).size ≤ w) (short : ∀ p : Fin (k*m), s[p].length ≤ J)
    (quotes : ∀ (p : Fin (k*m)) z, z ∈ s[p] → z ≤ G) :
    (listed (G := G) f outside s bidCompare).Bound (realSlots k m J w c) (testWidth w) := by
  let R := k*m*(J+1)
  let cs := candidates (G := G) f outside s
  have run := candidates_work (G := G) f outside s d hg outsideWork idx short quotes
  have clen : cs.value.length ≤ R := candidates_length f outside s J short
  have grow : 4*w+2 ≤ testWidth w := by unfold testWidth scalarWidth; omega
  have sorted := sortedSet_work bidCompare cs.value (bidCompare_work d.kSize d.mSize hg)
  have limit : cs.value.length*(cs.value.length+1)*28 ≤ R*(R+1)*28 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul clen (Nat.add_le_add_right clen _))
  have ms := sorted.weaken (Nat.add_le_add_left limit 1) grow
  exact bound_bind (f := sortedSet bidCompare) run ms

end Sorting


end Kintali.TrialWork.Inventory
