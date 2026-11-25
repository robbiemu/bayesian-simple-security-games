module

public import Kintali.InputOutput.Lottery
public import Kintali.InputOutput.Binary
public import Kintali.LinearProgramming.RationalBounds

/-! # Common denominator for the sparse pure-defense lottery of §1 -/

open scoped BigOperators

@[expose] public section

namespace Kintali.InputOutput.Lottery

open LinearProgramming

private theorem prefix_dvd {m : ℕ} (x : Fin m → ℚ) (i : Fin (m+1)) :
    (Fin.partialSum x i).den ∣ ScaledPoint.denominator x := by
  induction i using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [Fin.partialSum_succ]
    exact (Rat.add_den_dvd_lcm ..).trans (Nat.lcm_dvd ih
      (Finset.dvd_prod_of_mem (fun t => (x t).den) (Finset.mem_univ j)))

private theorem cut_dvd {n : ℕ} (x : Fin (n+1) → ℚ) {t : ℚ} (ht : t ∈ cuts x) :
    t.den ∣ ScaledPoint.denominator x := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_mergeSort.mp ht)
  unfold Int.fract
  exact (Rat.sub_den_dvd_lcm ..).trans (Nat.lcm_dvd (prefix_dvd x _) (by simp))

private theorem sample_denominators {lo : ℚ} {ts : List ℚ} {D : ℕ} (hlo : lo.den ∣ D)
    (h : ∀ t ∈ ts, t.den ∣ D) (p : Sample) (hp : p ∈ samples lo ts) :
    p.2.den ∣ D ∧ p.1.den ∣ 2*D := by
  have cell {a b : ℚ} (ha : a.den ∣ D) (hb : b.den ∣ D) :
      (b-a).den ∣ D ∧ ((a+b)/2).den ∣ 2*D := by
    have add := (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)
    refine ⟨(Rat.sub_den_dvd_lcm b a).trans (Nat.lcm_dvd hb ha), ?_⟩
    rw [show (a+b)/2 = (1/2)*(a+b) by ring]
    apply (Rat.mul_den_dvd _ _).trans
    rw [show (1/2 : ℚ).den = 2 by norm_num]
    exact Nat.mul_dvd_mul_left 2 add
  induction ts generalizing lo with
  | nil =>
    simp only [samples, List.mem_singleton] at hp
    subst p
    exact cell hlo (by simp : (1 : ℚ).den ∣ D)
  | cons t ts ih =>
    rcases List.mem_cons.mp hp with rfl | later
    · exact cell hlo (h t (by simp))
    · exact ih (h t (by simp)) (fun u hu => h u (List.mem_cons_of_mem _ hu)) later

theorem sample_parts {n : ℕ} (x : Fin (n+1) → ℚ) (p : Sample) (hp : p ∈ samples 0 (cuts x)) :
    p.2.den ∣ ScaledPoint.denominator x ∧ p.1.den ∣ 2 * ScaledPoint.denominator x :=
  sample_denominators (by simp) (fun _ ht => cut_dvd x ht) p hp

private theorem weight_le_one {lo : ℚ} {ts : List ℚ} (hlo : 0 ≤ lo) (h : Ordered lo ts)
    (p : Sample) (hp : p ∈ samples lo ts) : p.2 ≤ 1 := by
  induction ts generalizing lo with
  | nil =>
    simp only [samples, List.mem_singleton] at hp
    subst p
    dsimp
    linarith
  | cons t ts ih =>
    rcases List.mem_cons.mp hp with rfl | later
    · have ht := h.upper t (by simp)
      dsimp
      linarith
    · exact ih (hlo.trans (h.lower t (by simp))) h.tail later

private theorem width_denom (xs : List ℚ) :
    (xs.map fun q => q.den.size).sum ≤ (Binary.many Binary.rational xs).length := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
    have a := (Binary.parts q).2
    simp [Binary.many] at *
    omega

/-- The denominator product has at most one more bit than the encoded
coverage list, including reducible and repeated rational coordinates. -/
theorem common_size {m : ℕ} (x : Fin m → ℚ) :
    (ScaledPoint.denominator x).size ≤ 1 + (Binary.many Binary.rational (List.ofFn x)).length := by
  apply (ScaledPoint.denominator_size x).trans (Nat.add_le_add_left ?_ _)
  simpa [List.map_ofFn, List.sum_ofFn, Function.comp_def] using width_denom (List.ofFn x)

theorem probability_parts {n : ℕ} (x : Fin (n+1) → ℚ) (p : Outcome (n+1)) (hp : p ∈ recover x) :
    p.2.num.natAbs.size ≤ 1 + (Binary.many Binary.rational (List.ofFn x)).length ∧
    p.2.den.size ≤ 1 + (Binary.many Binary.rational (List.ofFn x)).length := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hq, pos⟩ := List.mem_filter.mp hq
  have den := Nat.size_le_size (Nat.le_of_dvd (Finset.prod_pos (fun t _ => (x t).den_pos)) (sample_parts x q hq).1)
  have upper := weight_le_one (le_refl (0 : ℚ)) (cuts_ordered x) q hq
  rw [← Rat.num_div_den q.2, div_le_iff₀ (by exact_mod_cast q.2.den_pos), one_mul] at upper
  have nonneg := Rat.num_nonneg.mpr (of_decide_eq_true pos).le
  have num : q.2.num.natAbs ≤ q.2.den := by
    have bound : q.2.num ≤ (q.2.den : ℤ) := by exact_mod_cast upper
    have cast : (q.2.num.natAbs : ℤ) ≤ (q.2.den : ℤ) := by
      simpa only [Int.natCast_natAbs, abs_of_nonneg nonneg] using bound
    exact_mod_cast cast
  exact ⟨(Nat.size_le_size num).trans (den.trans (common_size x)), den.trans (common_size x)⟩

end Kintali.InputOutput.Lottery
