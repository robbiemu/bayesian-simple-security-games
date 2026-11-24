module

public import StochasticGames.IntegerAtoms
import all StochasticGames.IntegerAtoms
import all StochasticGames.MaxAverageReduction
import all StochasticGames.Precision
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Clear the compiler offsets at the explicit dyadic scale

The input width is one. The input scale clears the literal offsets, and a
factor of two for each shifted comparison clears every new dyadic offset.
-/

@[expose] public section

namespace StochasticGames.CompilationScale

open AverageFeasibility AtomEncoding IntegerAtoms Precision

variable {ι ν : Type*} {d r : ℕ}

def scale (d r : ℕ) : ℕ := d * 2 ^ (r + 1)

theorem scale_pos (hd : 0 < d) : 0 < scale d r := by
  exact Nat.mul_pos hd (pow_pos (by decide) _)

theorem clears_multiple {a b : ℕ} {q : ℚ} (h : a ∣ b) (hc : Clears a q) : Clears b q := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨z, hz⟩ := hc
  exact ⟨(k : ℤ) * z, by
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_mul, mul_comm (a : ℚ), mul_assoc, hz]⟩

theorem clears_shift (d : ℕ) (j : Fin r) :
    Clears (scale d r) (ShiftedComparisons.gapBound 1 j.val / 4) := by
  let e := j.val + 2
  have shift : ShiftedComparisons.gapBound 1 j.val / 4 = 1 / ((2 ^ e : ℕ) : ℚ) := by
    rw [ShiftedComparisons.gapBound_eq, div_div, Nat.cast_pow, pow_add]
    norm_num [e, pow_add]
  rw [shift]
  apply clears_multiple
  · have exp : e ≤ r + 1 := by dsimp [e]; omega
    exact (pow_dvd_pow 2 exp).trans (dvd_mul_left _ _)
  · exact ⟨1, by simp⟩

private theorem shift_unit (j : Fin r) :
    0 ≤ ShiftedComparisons.gapBound 1 j.val / 4 ∧
      ShiftedComparisons.gapBound 1 j.val / 4 ≤ 1 := by
  rw [ShiftedComparisons.gapBound_eq, div_div]
  have p : (1 : ℚ) ≤ 2 ^ j.val := one_le_pow₀ (by norm_num)
  have b : (1 : ℚ) ≤ 2 ^ j.val * 4 := by linarith
  exact ⟨by positivity, (div_le_one (by positivity)).2 b⟩

private def boundedOffset (D : ℕ) (q : ℚ) : Prop := Clears D q ∧ |q| ≤ 1

private theorem signal_offsets {D : ℕ} (lhs : Signal ν) (terms : List (Signal ν))
    (clearL : Clears D lhs.2)
    (clearR : ∀ t ∈ terms, Clears D t.2)
    (size : ∀ t ∈ terms, |t.2 - lhs.2| ≤ 1) :
    ∀ t ∈ (fromSignals lhs terms).terms, boundedOffset D t.2 := by
  intro t mem
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp mem
  exact ⟨(clearR s hs).sub clearL, size s hs⟩

private theorem comparison_offsets {D : ℕ} (u v : ν) (a b : Signal ν)
    (ha : boundedOffset D a.2) (hb : boundedOffset D b.2) :
    ∀ atom ∈ comparison u v a b,
      ∀ t ∈ (atom : Atom ν).terms, boundedOffset D t.2 := by
  have bound (c : ν) {ss : List (Signal ν)}
      (h : ∀ t ∈ ss, boundedOffset D t.2) :
      ∀ t ∈ (fromSignals (c, 0) ss).terms, boundedOffset D t.2 :=
    signal_offsets _ _ (Clears.zero _) (fun t ht => (h t ht).1)
      (fun t ht => by simpa only [sub_zero] using (h t ht).2)
  intro atom mem
  rcases (by simpa only [comparison, List.mem_cons, List.not_mem_nil, or_false] using mem :
    atom = fromSignals (u, 0) [a, b] ∨ atom = fromSignals (v, 0) [a] ∨
      atom = fromSignals (v, 0) [b]) with rfl | rfl | rfl
  · apply bound
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ha
    · exact hb
  · exact bound _ (by simpa only [List.forall_mem_singleton] using ha)
  · exact bound _ (by simpa only [List.forall_mem_singleton] using hb)

private theorem small_difference {x y : ℚ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    |x - y| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

set_option maxHeartbeats 900000 in
private theorem average_offsets {n r d : ℕ} (i : Fin n) (row : AverageRow ι)
    (input : ∀ q ∈ [row.lhs.offset, row.first.offset, row.second.offset],
      Clears (scale d r) q ∧ (0 ≤ q ∧ q ≤ 1)) :
    ∀ a ∈ (AtomEncoding.averageAtoms (rounds := r) 1 i row),
      ∀ t ∈ (a : Atom (Var ι n r)).terms, boundedOffset (scale d r) t.2 := by
  have lhs := input row.lhs.offset (by simp)
  have first := input row.first.offset (by simp)
  have second := input row.second.offset (by simp)
  intro a hi
  rw [AtomEncoding.averageAtoms, List.mem_append, List.mem_append] at hi
  rcases hi with (initial | round) | terminal
  · have firstSize : |row.first.offset| ≤ 1 := by
      rw [abs_of_nonneg first.2.1]
      exact first.2.2
    have secondSize : |row.second.offset| ≤ 1 := by
      rw [abs_of_nonneg second.2.1]
      exact second.2.2
    change a ∈ comparison (.high i 0) (.low i 0) (sourceSignal row.first)
      (sourceSignal row.second) at initial
    exact comparison_offsets (D := scale d r) (.high i 0 : Var ι n r) (.low i 0)
      (sourceSignal row.first) (sourceSignal row.second)
      ⟨first.1, firstSize⟩ ⟨second.1, secondSize⟩ a initial
  · obtain ⟨j, _, hround⟩ := List.mem_flatMap.mp round
    have clear := clears_shift d j
    have hshift := shift_unit j
    have size : |ShiftedComparisons.gapBound 1 j.val / 4| ≤ 1 := by
      rw [abs_of_nonneg hshift.1]
      exact hshift.2
    apply comparison_offsets _ _ _ _ _ _ a hround
    · exact ⟨by simpa only [zero_sub] using (Clears.zero (scale d r)).sub clear,
        by simpa only [abs_neg] using size⟩
    · exact ⟨clear, size⟩
  · obtain rfl := List.mem_singleton.mp terminal
    refine signal_offsets _ _ lhs.1 ?_ ?_
    · simp only [List.forall_mem_singleton]
      exact Clears.zero _
    · simp only [List.forall_mem_singleton]
      exact small_difference (by norm_num) lhs.2

/-- Every printed offset in the compiled atom list has absolute value at most
one and is cleared by the displayed scale. -/
theorem offsets_bounded (system : System ι) (d r : ℕ)
    (input : ∀ q ∈ MaxAverageReduction.offsets system, Clears d q ∧ (0 ≤ q ∧ q ≤ 1)) :
    ∀ q ∈ atomOffsets (allAtoms system 1 r), Clears (scale d r) q ∧ |q| ≤ 1 := by
  have inScale {q : ℚ} (hq : q ∈ MaxAverageReduction.offsets system) :
      Clears (scale d r) q ∧ (0 ≤ q ∧ q ≤ 1) :=
    ⟨clears_multiple (dvd_mul_right _ _) (input _ hq).1, (input _ hq).2⟩
  have difference (row : DifferenceRow ι) (hr : row ∈ system.differences) :
      ∀ q ∈ [row.lhs.offset, row.rhs.offset],
        Clears (scale d r) q ∧ (0 ≤ q ∧ q ≤ 1) := by
    intro q hq
    apply inScale
    simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inl ⟨row, hr, hq⟩)
  have maximum (row : MaxRow ι) (hr : row ∈ system.maxima) :
      ∀ q ∈ row.lhs.offset :: row.terms.map AverageFeasibility.Term.offset,
        Clears (scale d r) q ∧ (0 ≤ q ∧ q ≤ 1) := by
    intro q hq
    apply inScale
    simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨row, hr, hq⟩)
  have average (row : AverageRow ι) (hr : row ∈ system.averages) :
      ∀ q ∈ [row.lhs.offset, row.first.offset, row.second.offset],
        Clears (scale d r) q ∧ (0 ≤ q ∧ q ≤ 1) := by
    intro q hq
    apply inScale
    simp only [MaxAverageReduction.offsets, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨row, hr, hq⟩
  suffices all : ∀ atom ∈ allAtoms system 1 r,
      ∀ t ∈ (atom : Atom (vars system r)).terms, boundedOffset (scale d r) t.2 by
    intro q hq
    obtain ⟨atom, atomMem, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨t, tMem, rfl⟩ := List.mem_map.mp hq
    exact all atom atomMem t tMem
  intro a ha
  rw [allAtoms, List.mem_append, List.mem_append] at ha
  rcases ha with (hd | hm) | hv
  · obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hd
    have lhs := difference row hr row.lhs.offset (by simp)
    have rhs := difference row hr row.rhs.offset (by simp)
    refine signal_offsets _ _ lhs.1 ?_ ?_
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      exact rhs.1
    · intro s hs
      obtain rfl := List.mem_singleton.mp hs
      exact small_difference rhs.2 lhs.2
  · obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hm
    have lhs := maximum row hr row.lhs.offset (by simp)
    have rhs (s : Signal (vars system r)) (hs : s ∈ row.terms.map sourceSignal) :
        Clears (scale d r) s.2 ∧ (0 ≤ s.2 ∧ s.2 ≤ 1) := by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact maximum row hr _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t, ht, rfl⟩))
    exact signal_offsets _ _ lhs.1 (fun s hs => (rhs s hs).1)
      (fun s hs => small_difference (rhs s hs).2 lhs.2)
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hv
    exact average_offsets i _ (average _ (List.get_mem _ i)) a hi

theorem integer_offsets_bounded (rows : List (Atom ν)) (Q : ℕ)
    (offsets : ∀ q ∈ atomOffsets rows, Clears Q q ∧ |q| ≤ 1) :
    ∀ row ∈ encodeAt Q rows, ∀ t ∈ (row : IntAtom ν).terms, |t.2| ≤ (Q : ℤ) := by
  intro row mem t termMem
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp mem
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp termMem
  have member : b.2 ∈ atomOffsets rows :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
  obtain ⟨⟨z, equals⟩, bound⟩ := offsets b.2 member
  change |⌊(Q : ℚ) * b.2⌋| ≤ (Q : ℤ)
  rw [equals, Int.floor_intCast]
  have magnitude : |(z : ℚ)| ≤ (Q : ℚ) := by
    rw [← equals, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (Q : ℚ))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left bound (by positivity : (0 : ℚ) ≤ (Q : ℚ))
  exact_mod_cast magnitude

end StochasticGames.CompilationScale
