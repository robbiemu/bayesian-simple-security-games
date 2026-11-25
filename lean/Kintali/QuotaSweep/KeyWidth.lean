module

public import Kintali.QuotaSweep.SparseWork
public import Kintali.ContactSize.Rational
import Mathlib.Tactic.Positivity

/-!
# Bit lengths of sparse ordinal keys and exact scalar comparisons

Kintali's quote cost is affine in `z/G`. The remaining ordinal fields are
the finite buyer/site indices, a quote index, and an encoding of a fixed sum
of pairs. All bounds use the bit length of the grid size.
-/

@[expose] public section
namespace Kintali.QuotaSweep.KeyWidth

open StochasticGames.BinarySize
open Kintali.ExactRecovery
open Kintali.ContactSize

/-- The reduced rational comparison uses two signed cross products,
each with at most the sum of the input magnitude widths. -/
theorem rational_comparison {a b : ℚ} {u v : ℕ} (ha : Fits u a) (hb : Fits v b) :
    (a ≤ b ↔ a.num*(b.den : ℤ) ≤ b.num*(a.den : ℤ)) ∧
    (a < b ↔ a.num*(b.den : ℤ) < b.num*(a.den : ℤ)) ∧
    (a.num*(b.den : ℤ)).natAbs.size ≤ u+v ∧
    (b.num*(a.den : ℤ)).natAbs.size ≤ u+v := by
  refine ⟨Rat.le_iff ..,Rat.lt_iff ..,?_,?_⟩
  · simp only [Int.natAbs_mul,Int.natAbs_natCast]
    exact (size_mul_le ..).trans (Nat.add_le_add ha.1 hb.2)
  · simp only [Int.natAbs_mul,Int.natAbs_natCast]
    apply (size_mul_le ..).trans
    exact (Nat.add_le_add hb.1 ha.2).trans_eq (Nat.add_comm ..)

private def Codes (T : Type*) [Encodable T] (w : ℕ) := ∀ t : T, (Encodable.encode t).size ≤ w

private theorem code_mono {T : Type*} [Encodable T] {w v : ℕ} (h : Codes T w) (hle : w ≤ v) :
    Codes T v := fun t => (h t).trans hle

private theorem pair_bits {a b w : ℕ} (ha : a.size ≤ w) (hb : b.size ≤ w) :
    (Nat.pair a b).size ≤ 2*w := by
  apply Nat.size_le.mpr
  have hm := max_lt (Nat.size_le.mp ha) (Nat.size_le.mp hb)
  calc
    Nat.pair a b < (max a b+1)^2 := Nat.pair_lt_max_add_one_sq ..
    _ ≤ (2^w)^2 := Nat.pow_le_pow_left (by omega) _
    _ = 2^(2*w) := by rw [← pow_mul, Nat.mul_comm w 2]

private theorem product_code {A B : Type*} [Encodable A] [Encodable B] {w : ℕ}
    (ha : Codes A w) (hb : Codes B w) : Codes (A×B) (2*w) := by
  rintro ⟨a,b⟩
  rw [Encodable.encode_prod_val]
  exact pair_bits (ha a) (hb b)

private theorem sum_code {A B : Type*} [Encodable A] [Encodable B] {w : ℕ}
    (ha : Codes A w) (hb : Codes B w) : Codes (A⊕B) (w+1) := by
  rintro (a | b)
  · rw [Encodable.encode_inl,Nat.size_le,pow_succ]
    have h := Nat.size_le.mp (ha a)
    omega
  · rw [Encodable.encode_inr,Nat.size_le,pow_succ]
    have h := Nat.size_le.mp (hb b)
    omega

private theorem fin_code (n : ℕ) : Codes (Fin n) n.size := fun i =>
  Nat.size_le_size (show (Encodable.encode i) ≤ n from i.isLt.le)

private theorem quote_code (n : ℕ) : Codes (Quote n) n.size := fun i =>
  Nat.size_le_size (show (Encodable.encode i) ≤ n from Nat.le_of_lt_succ i.isLt)

/-- A record identifier in the elementary grid is used as the last key
field. Its fixed constructor depth gives a linear binary width. -/
theorem record_code {k m G w : ℕ} (hk : k.size ≤ w) (hm : m.size ≤ w) (hG : G.size ≤ w)
    (e : Expanded.R (Fin k) (Fin m) G) : (Encodable.encode e).size ≤ 4*w+3 := by
  have i := code_mono (fin_code k) hk
  have j := code_mono (fin_code m) hm
  have z := code_mono (quote_code G) hG
  have g := code_mono (fin_code G) hG
  have gap := product_code j g
  have quote := product_code j z
  have real := product_code (code_mono i (show w ≤ 2*w by omega)) quote
  have bid := sum_code real (code_mono gap (show 2*w ≤ 2*(2*w) by omega))
  have buyer := sum_code (code_mono i (show w ≤ 2*w by omega)) gap
  have vertex := sum_code buyer (code_mono j (show w ≤ 2*w+1 by omega))
  have recCode := sum_code (code_mono bid (show 2*(2*w)+1 ≤ 4*w+2 by omega))
    (code_mono vertex (show 2*w+1+1 ≤ 4*w+2 by omega))
  exact recCode e

private theorem interval_code {m G w : ℕ} (D : Fin m → QuotePartition G)
    (hm : m.size ≤ w) (hs : ∀ j, (D j).groups.size ≤ w) : Codes (Sparse.IntervalGroup D) (2*w) := by
  rintro ⟨j,h⟩
  rw [Encodable.encode_sigma_val]
  exact pair_bits ((fin_code m j).trans hm) ((fin_code _ h).trans (hs j))

/-- The index equality used in allocation and graph table lookups compares
these small sparse record codes. The group is a site paired with an interval
number, whose cardinality can be bounded directly by the sparse inventory. -/
theorem sparse_record_code {k m a G w : ℕ} (D : Fin m → QuotePartition G)
    (hk : k.size ≤ w) (hm : m.size ≤ w) (ha : a.size ≤ w) (hs : ∀ j, (D j).groups.size ≤ w)
    (e : Sparse.R (Fin k) (Fin m) (Fin a) (Sparse.IntervalGroup D)) :
    (Encodable.encode e).size ≤ 2*w+3 := by
  have h := interval_code D hm hs
  have i := code_mono (fin_code k) hk
  have j := code_mono (fin_code m) hm
  have a' := code_mono (fin_code a) ha
  have buyer := sum_code (code_mono i (show w ≤ 2*w by omega)) h
  have bid := sum_code (code_mono a' (show w ≤ 2*w by omega)) h
  have vertex := sum_code buyer (code_mono j (show w ≤ 2*w+1 by omega))
  have recCode := sum_code (code_mono bid (Nat.le_succ _)) vertex
  exact recCode e

theorem fits_neg {w : ℕ} {q : ℚ} (h : Fits w q) : Fits w (-q) := by
  simpa [Fits] using h

theorem quote_fits {I J : Type*} (g : Game I J) (i : I) (j : J) {G h w : ℕ}
    (ha : Fits h (g.intercept i j)) (hb : Fits h (g.slope i j)) (hG : G.size ≤ w) (z : Quote G) :
    Fits (2*h+2*w+3) (Holdings.quoteCost g i j z) := by
  have hz : z.val.size ≤ w := (Nat.size_le_size (Nat.le_of_lt_succ z.isLt)).trans hG
  have hp := ((Fits.natCast z.val).mono (Nat.succ_le_succ hz)).div
    ((Fits.natCast G).mono (Nat.succ_le_succ hG))
  exact (ha.add (hb.mul hp)).mono (by omega)

/-- The finite primary key at either endpoint has a uniform magnitude
width. Slack records use the separate top value. -/
theorem primary_fits {I J : Type*} (g : Game I J) {G h w : ℕ}
    (ha : ∀ i j, Fits h (g.intercept i j)) (hb : ∀ i j, Fits h (g.slope i j))
    (hG : G.size ≤ w) (v : Expanded.V I J G) (e : Expanded.R I J G) {q : ℚ}
    (hq : Expanded.primary g v e = (q : WithTop ℚ)) : Fits (2*h+2*w+8) q := by
  have two : Fits 2 (2 : ℚ) := by unfold Fits; decide
  rcases e with (⟨i,j,z⟩ | ⟨j,t⟩) | b
  · rcases v with b | s
    · have he : Holdings.quoteCost g i j z = q := WithTop.coe_inj.mp hq
      exact he ▸ (quote_fits g i j (ha i j) (hb i j) hG z).mono (by omega)
    · have he : -(2*(z.val : ℚ)) = q := WithTop.coe_inj.mp hq
      have hz := (Nat.size_le_size (Nat.le_of_lt_succ z.isLt)).trans hG
      exact he ▸ (fits_neg (two.mul (Fits.natCast z.val))).mono (by omega)
  · rcases v with b | s
    · have he : (0 : ℚ) = q := WithTop.coe_inj.mp hq
      exact he ▸ Fits.zero.mono (by omega)
    · have he : -(2*(t.val : ℚ)+1) = q := WithTop.coe_inj.mp hq
      have ht := (Nat.size_le_size t.isLt.le).trans hG
      exact he ▸ (fits_neg ((two.mul (Fits.natCast t.val)).add Fits.one)).mono (by omega)
  · exact False.elim (WithTop.top_ne_coe hq)

/-- Both earlier natural tie fields are finite input/quote indices. -/
theorem tie_bits {k m G w : ℕ} (hk : k.size ≤ w) (hm : m.size ≤ w) (hG : G.size ≤ w)
    (v : Expanded.V (Fin k) (Fin m) G) (e : Expanded.R (Fin k) (Fin m) G) :
    (Expanded.tie Fin.val Fin.val v e).1.size ≤ w ∧
    (Expanded.tie Fin.val Fin.val v e).2.size ≤ w := by
  rcases e with (⟨i,j,z⟩ | t) | b
  · rcases v with b | s
    · exact ⟨(Nat.size_le_size j.isLt.le).trans hm,(Nat.size_le_size (Nat.le_of_lt_succ z.isLt)).trans hG⟩
    · exact ⟨(Nat.size_le_size i.isLt.le).trans hk,by simp [Expanded.tie]⟩
  · simp [Expanded.tie]
  · simp [Expanded.tie]

end Kintali.QuotaSweep.KeyWidth
