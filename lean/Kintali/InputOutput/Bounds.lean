module

public import Kintali.InputOutput.Binary
public import Kintali.ExactRecovery.Size

/-! # From the explicit wire length to the recovery determinant bound -/

open scoped BigOperators

@[expose] public section

namespace Kintali.InputOutput.Binary

open ExactRecovery

private def Fits (L : ℕ) (v : ℚ) : Prop := v.num.natAbs.size ≤ L ∧ v.den.size ≤ L

private theorem fits_of_width {L : ℕ} {q : ℚ} (h : (rational q).length ≤ L) : Fits L q :=
  ⟨(parts q).1.trans h, (parts q).2.trans h⟩

private theorem fits_diff {L : ℕ} {a b : ℚ} (ha : Fits L a) (hb : Fits L b) :
    Fits (2 * L + 1) (a - b) := by
  have prod {n t : ℕ} (hn : n.size ≤ L) (ht : t.size ≤ L) : n * t < 2 ^ (2 * L) := by
    rw [two_mul, pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.size_le.mp hn) (Nat.size_le.mp ht).le (by positivity)
  have p := prod ha.1 hb.2
  have q := prod hb.1 ha.2
  have d := prod ha.2 hb.2
  let z := a.num * (b.den : ℤ) - b.num * (a.den : ℤ)
  have bound : z.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den := by
    simpa [z, Int.natAbs_mul] using Int.natAbs_sub_le (a.num * (b.den : ℤ)) (b.num * (a.den : ℤ))
  have norm := LinearProgramming.divInt_parts_le z ((a.den * b.den : ℕ) : ℤ)
    (by exact_mod_cast mul_ne_zero a.den_ne_zero b.den_ne_zero)
  rw [Rat.divInt_ofNat] at norm
  simp only [Int.natAbs_natCast] at norm
  unfold Fits
  rw [Rat.sub_def']
  constructor <;> apply Nat.size_le.mpr <;> rw [pow_succ] <;> dsimp only [z] at * <;> omega

/-- Includes the constant 1 and resource count in the exact LP model. -/
theorem datum_parts (a : Input) (h : a.Valid) {q : ℚ} (included : q ∈ data a.game) :
    q.num.natAbs.size ≤ 2 * lengthInput a + 1 ∧ q.den.size ≤ 2 * lengthInput a + 1 := by
  let L := lengthInput a
  have widen {v : ℚ} (hv : Fits L v) : Fits (2 * L + 1) v := by
    rcases hv with ⟨hn, hd⟩
    exact ⟨by omega, by omega⟩
  change Fits (2 * L + 1) q
  simp only [data, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_univ, true_and] at included
  rcases included with ((((rfl | rfl) | ⟨i,rfl⟩) | ⟨j,rfl⟩) | ⟨⟨i,j⟩,rfl⟩) | ⟨⟨i,j⟩,rfl⟩
  · change 1 ≤ _ ∧ 1 ≤ _
    omega
  · have hb : a.1.size ≤ L := (dimensions a).2.2
    change _ ≤ _ ∧ _ ≤ _
    simp only [Input.game, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast, Nat.size_one]
    omega
  · exact widen (fits_of_width (prior_width a i))
  · have hd := defense_widths a j
    exact fits_diff (fits_of_width hd.2) (fits_of_width hd.1)
  · have ha := fits_of_width (attack_widths a h i j).1
    apply widen
    simpa [Fits, Input.game] using ha
  · have ha := attack_widths a h i j
    exact fits_diff (fits_of_width ha.1) (fits_of_width ha.2)

theorem data_count (a : Input) : (data a.game).card ≤
    2 + a.types + a.targets + a.types * a.targets + a.types * a.targets := by
  have img {α : Type} [Fintype α] (f : α → ℚ) : (Finset.univ.image f).card ≤ Fintype.card α :=
    Finset.card_image_le
  have two : ({1, (a.game.resources : ℚ)} : Finset ℚ).card ≤ 2 := by
    simpa only [Finset.card_singleton] using
      Finset.card_insert_le (1 : ℚ) {(a.game.resources : ℚ)}
  unfold data
  refine (Finset.card_union_le ..).trans (Nat.add_le_add ?_ ?_)
  · refine (Finset.card_union_le ..).trans (Nat.add_le_add ?_ ?_)
    · refine (Finset.card_union_le ..).trans (Nat.add_le_add ?_ ?_)
      · exact (Finset.card_union_le ..).trans (Nat.add_le_add two (by simpa using img a.game.prior))
      · simpa using img a.game.gain
    · simpa using img (fun p : Fin a.types × Fin a.targets => a.game.intercept p.1 p.2)
  · simpa using img (fun p : Fin a.types × Fin a.targets => a.game.slope p.1 p.2)

/-- An explicit polynomial in the true bit length of the public input bounds
the distinct reduced numerator and denominator lengths used in the LP. -/
theorem tableBits_bound (a : Input) (h : a.Valid) :
    let L := lengthInput a
    tableBits a.game ≤ (2 + L + L + L*L + L*L) * (4 * L + 2) := by
  let L := lengthInput a
  have dims := dimensions a
  have n : (data a.game).card ≤ 2 + L + L + L*L + L*L := by
    apply (data_count a).trans
    gcongr <;> first | exact dims.1 | exact dims.2.1
  apply (Finset.sum_le_card_nsmul (data a.game) _ (4 * L + 2) ?_).trans
  · exact Nat.mul_le_mul_right _ n
  · intro q hq
    have b := datum_parts a h hq
    dsimp [L]
    omega

end Kintali.InputOutput.Binary
