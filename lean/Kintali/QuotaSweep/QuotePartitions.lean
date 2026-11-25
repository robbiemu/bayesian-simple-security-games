module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.Linarith

/-!
# Group boundaries and elementary gaps

Consecutive retained quote levels partition the private gaps. The
runtime uses the sorted boundary list and group sizes. The equivalence
to individual gaps is used in the correctness proof.
-/

@[expose] public section

namespace Kintali.QuotaSweep

structure QuotePartition (G : ℕ) where
  groups : ℕ
  cut : Fin (groups + 1) → ℕ
  increasing : StrictMono cut
  first : cut 0 = 0
  last : cut (Fin.last groups) = G

namespace QuotePartition

variable {G : ℕ} (D : QuotePartition G)

def lo (h : Fin D.groups) : ℕ := D.cut h.castSucc
def hi (h : Fin D.groups) : ℕ := D.cut h.succ
def size (h : Fin D.groups) : ℕ := D.hi h - D.lo h

theorem lo_lt_hi (h : Fin D.groups) : D.lo h < D.hi h :=
  D.increasing (show h.val < h.val + 1 from Nat.lt_succ_self _)

theorem hi_le_end (h : Fin D.groups) : D.hi h ≤ G := by
  exact (D.increasing.monotone
    (show h.succ ≤ Fin.last D.groups from h.isLt)).trans_eq D.last

theorem separated {i j : Fin D.groups} (h : i < j) : D.hi i ≤ D.lo j :=
  D.increasing.monotone (show i.val + 1 ≤ j.val from h)

/-- List the elementary gaps in one group from highest quote to lowest. -/
def gapAt (p : Σ h : Fin D.groups, Fin (D.size h)) : Fin G :=
  ⟨D.hi p.1 - 1 - p.2.val, by
    have hPos := D.lo_lt_hi p.1
    have hEnd := D.hi_le_end p.1
    omega⟩

theorem gapAt_bounds (p : Σ h : Fin D.groups, Fin (D.size h)) :
    D.lo p.1 ≤ (D.gapAt p).val ∧ (D.gapAt p).val < D.hi p.1 := by
  have h := p.2.isLt
  dsimp only [size] at h
  change D.lo p.1 ≤ D.hi p.1 - 1 - p.2.val ∧ _
  constructor <;> first | omega | (change D.hi p.1 - 1 - p.2.val < _; omega)

theorem gapAt_descends (h : Fin D.groups) {i j : Fin (D.size h)} (hij : i < j) :
    D.gapAt ⟨h, j⟩ < D.gapAt ⟨h, i⟩ := by
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [size] at hi hj
  change D.hi h - 1 - j.val < D.hi h - 1 - i.val
  omega

theorem gapAt_injective : Function.Injective D.gapAt := by
  rintro ⟨i, a⟩ ⟨j, b⟩ eq
  have ha := D.gapAt_bounds ⟨i, a⟩
  have hb := D.gapAt_bounds ⟨j, b⟩
  change D.lo i ≤ (D.gapAt ⟨i, a⟩).val ∧ (D.gapAt ⟨i, a⟩).val < D.hi i at ha
  change D.lo j ≤ (D.gapAt ⟨j, b⟩).val ∧ (D.gapAt ⟨j, b⟩).val < D.hi j at hb
  rcases lt_trichotomy i j with h | rfl | h
  · have hs := D.separated h
    rw [eq] at ha
    omega
  · congr 1
    apply Fin.ext
    have haa := a.isLt
    have hbb := b.isLt
    dsimp only [size] at haa hbb
    have he := congrArg Fin.val eq
    change D.hi i - 1 - a.val = D.hi i - 1 - b.val at he
    omega
  · have hs := D.separated h
    rw [eq] at ha
    omega

theorem gapAt_surjective : Function.Surjective D.gapAt := by
  intro a
  let above := Finset.univ.filter fun i : Fin (D.groups + 1) => a.val < D.cut i
  have hLast : Fin.last D.groups ∈ above := by simp [above, D.last, a.isLt]
  let upper := above.min' ⟨_, hLast⟩
  have hUpper : a.val < D.cut upper := (Finset.mem_filter.mp (above.min'_mem _)).2
  have hNZ : 0 < upper.val := by
    by_contra! h
    have hZero : upper = 0 := Fin.ext (by simpa using h)
    simp [hZero, D.first] at hUpper
  let seg : Fin D.groups := ⟨upper.val - 1, by have hu := upper.isLt; omega⟩
  have hNext : seg.succ = upper := Fin.ext (by dsimp [seg]; omega)
  have hh : a.val < D.hi seg := by simpa [hi, hNext] using hUpper
  have hl : D.lo seg ≤ a.val := by
    by_contra! less
    have hm : seg.castSucc ∈ above := by simp [above, lo] at less ⊢; exact less
    have hmin := Finset.min'_le above seg.castSucc hm
    change upper.val ≤ seg.val at hmin
    dsimp [seg] at hmin
    omega
  refine ⟨⟨seg, ⟨D.hi seg - 1 - a.val, by unfold size; omega⟩⟩, Fin.ext ?_⟩
  change D.hi seg - 1 - (D.hi seg - 1 - a.val) = _
  omega

noncomputable def equivalence : (Σ h : Fin D.groups, Fin (D.size h)) ≃ Fin G :=
  Equiv.ofBijective D.gapAt ⟨D.gapAt_injective, D.gapAt_surjective⟩

def representative (h : Fin D.groups) : Fin G :=
  D.gapAt ⟨h, ⟨0, Nat.sub_pos_of_lt (D.lo_lt_hi h)⟩⟩

theorem representative_injective : Function.Injective D.representative := by
  intro i j h
  exact congrArg Sigma.fst (D.gapAt_injective h)

theorem cut_outside_open (h : Fin D.groups) (j : Fin (D.groups + 1)) :
    D.cut j ≤ D.lo h ∨ D.hi h ≤ D.cut j := by
  by_cases hc : j.val ≤ h.val
  · exact Or.inl (D.increasing.monotone (show j ≤ h.castSucc from hc))
  · exact Or.inr (D.increasing.monotone (show h.succ ≤ j from Nat.lt_of_not_ge hc))

theorem size_sum : (∑ h : Fin D.groups, D.size h) = G := by
  let c (i : Fin (D.groups + 1)) : ℤ := D.cut i
  have hs := Fin.sum_univ_succ c
  have ht := Fin.sum_univ_castSucc c
  have h := show (∑ i : Fin D.groups, ((D.size i : ℕ) : ℤ)) = (G : ℤ) by
    have hdiff (i : Fin D.groups) : (D.size i : ℤ) = c i.succ - c i.castSucc := by
      exact Int.ofNat_sub (D.lo_lt_hi i).le
    simp_rw [hdiff]
    rw [Finset.sum_sub_distrib]
    have hfirst : c 0 = 0 := by simp [c, D.first]
    have hlast : c (Fin.last D.groups) = G := by simp [c, D.last]
    linarith
  exact_mod_cast h

/-- Construct interval endpoints from an explicit set of retained
quotes containing the boundary levels. -/
def ofCuts (cuts : Finset ℕ) (hz : 0 ∈ cuts) (hg : G ∈ cuts) (hb : ∀ j ∈ cuts, j ≤ G) :
    QuotePartition G := by
  let levels := cuts.sort
  have hpos : 0 < levels.length := by
    have h : 0 ∈ levels := by simpa [levels] using hz
    exact List.length_pos_of_mem h
  let n := levels.length - 1
  have hlen : n + 1 = levels.length := by dsimp [n]; omega
  let index := finCongr hlen
  have hsort : levels.SortedLT := cuts.sortedLT_sort
  let atLevel := fun i => levels.get (index i)
  have hMono : StrictMono atLevel := fun _ _ h => hsort.strictMono_get h
  have hFirst : atLevel 0 = 0 := by
    obtain ⟨j, hj, hv⟩ := List.getElem_of_mem (show 0 ∈ levels by simpa [levels] using hz)
    let v : Fin (n + 1) := index.symm ⟨j, hj⟩
    have hValue : atLevel v = 0 := by simpa [atLevel, v] using hv
    exact Nat.le_zero.mp ((hMono.monotone (Fin.zero_le v)).trans_eq hValue)
  have hLast : atLevel (Fin.last n) = G := by
    obtain ⟨j, hj, hv⟩ := List.getElem_of_mem (show G ∈ levels by simpa [levels] using hg)
    let v : Fin (n + 1) := index.symm ⟨j, hj⟩
    have hValue : atLevel v = G := by simpa [atLevel, v] using hv
    have hlower : G ≤ atLevel (Fin.last n) := hValue ▸ hMono.monotone (Fin.le_last v)
    have hm : atLevel (Fin.last n) ∈ levels := List.get_mem ..
    exact le_antisymm (hb _ (by simpa [levels] using hm)) hlower
  exact ⟨n, atLevel, hMono, hFirst, hLast⟩

theorem exists_cut_of_mem (cuts : Finset ℕ) (hz : 0 ∈ cuts) (hg : G ∈ cuts)
    (hb : ∀ j ∈ cuts, j ≤ G) {j : ℕ} (hj : j ∈ cuts) :
    ∃ i, (ofCuts cuts hz hg hb).cut i = j := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem (show j ∈ cuts.sort by simpa using hj)
  refine ⟨⟨i, by change i < (cuts.sort.length - 1) + 1; omega⟩, ?_⟩
  exact he

end QuotePartition
end Kintali.QuotaSweep
