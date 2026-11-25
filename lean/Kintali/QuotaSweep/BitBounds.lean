module

public import Kintali.QuotaSweep.Scale
public import Kintali.QuotaSweep.Contact
import all StochasticGames.Precision
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Positivity

/-!
# Binary lengths for the rational contact

The initial and rate scales are products of denominators of explicit input
lists. The final common denominator has at most the initial number of bits
plus one `factorBound` width for every stage. Feasibility also bounds every
output numerator by that common denominator times the largest quota.
-/

open scoped BigOperators
open StochasticGames.Precision
open Kintali.QuotaSweep.Arithmetic

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

def initialScale (P : Parameters B S) : ℕ :=
  denominator (P.target :: P.upper :: K.records.map (initial P.mass))

def rateScale (rate : S → ℚ) : ℕ :=
  denominator (K.records.map fun r => match r with
    | .inr (.inr s) => rate s
    | _ => 0)

def inputRateBound (P : Parameters B S) : ℕ :=
  Finset.univ.sup fun s => ⌈|((K.rateScale P.rate : ℕ) : ℚ) * P.rate s|⌉₊

omit [Fintype B] [Fintype E] in
theorem input_rate_bounded (P : Parameters B S) (s : S) :
    Bounded (K.rateScale P.rate) (K.inputRateBound P) (P.rate s) := by
  refine ⟨denominator_clears (List.mem_map.mpr ⟨vacancy s, K.complete _, rfl⟩), ?_⟩
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (Finset.le_sup (f := fun s =>
    ⌈|((K.rateScale P.rate : ℕ) : ℚ) * P.rate s|⌉₊) (Finset.mem_univ s)))

omit [Fintype B] [Fintype S] [Fintype E] in
theorem initial_scale (P : Parameters B S) : Scale (E := E) P ⟨0, initial P.mass⟩ (K.initialScale P) := by
  unfold initialScale
  refine ⟨Clears.zero _, ?_, denominator_clears (by simp), denominator_clears (by simp)⟩
  intro e
  exact denominator_clears (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨e, K.complete e, rfl⟩)))

private theorem size_of_power_bound {d B C n : ℕ} (h : d ≤ B*C^n) :
    d.size ≤ B.size + C.size*n := by
  apply Nat.size_le.mpr
  have hb : B < 2^B.size := Nat.size_le.mp le_rfl
  have hc : C ≤ 2^C.size := (Nat.size_le.mp (le_rfl : C.size ≤ C.size)).le
  calc
    d ≤ B*C^n := h
    _ ≤ B*(2^C.size)^n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc _)
    _ < 2^B.size * (2^C.size)^n := Nat.mul_lt_mul_of_pos_right hb (by positivity)
    _ = 2^(B.size + C.size*n) := by rw [pow_add, pow_mul]

/-- Explicit common denominator and binary-length estimate for the result
of the executable contact search. This bound also covers runs that end at
the upper pressure. -/
theorem contact_denominator_bits (P : Parameters B S) :
    ∃ d : ℕ, 0 < d ∧
      d.size ≤ (K.initialScale P).size +
        (factorBound B S (K.rateScale P.rate) (K.inputRateBound P)).size *
        (Fintype.card (Record B S E) + 1) ∧
      (K.firstContact P).pressure.den ∣ d ∧
      ∀ e, ((K.firstContact P).allocation e).den ∣ d := by
  obtain ⟨d, hd, hb, hs⟩ := K.run_scale (denominator_pos _) (K.input_rate_bounded P)
    (Fintype.card (Record B S E) + 1) _ (denominator_pos _) (K.initial_scale P)
  exact ⟨d, hd, size_of_power_bound hb, denominator_dvd hd hs.pressure,
    fun e => denominator_dvd hd (hs.allocation e)⟩

/-- Bounding each incident holding by the full quota at either endpoint
also bounds its reduced integer numerator on the final scale. -/
theorem contact_numerators {P : Parameters B S} (hs : K.Feasible P (K.firstContact P))
    {d H : ℕ} (hd : 0 < d) (hden : ∀ e, ((K.firstContact P).allocation e).den ∣ d)
    (hvalue : ∀ v, quota P.rate P.mass (K.firstContact P).pressure v ≤ H) (e : Record B S E) :
    ((K.firstContact P).allocation e).num.natAbs ≤ d*H := by
  let z := K.firstContact P
  have hinc : (K.market.ends e).Nonempty :=
    Finset.card_pos.mp ((K.market.degree e).elim (fun h => by omega) (fun h => by omega))
  obtain ⟨v, hv⟩ := hinc
  have hle := Finset.single_le_sum (f := fun f => if v ∈ K.market.ends f then z.allocation f else 0)
    (fun f _ => by split; exact hs.nonneg f; exact le_rfl) (Finset.mem_univ e)
  simp only [hv, ↓reduceIte] at hle
  have hmass := (hle.trans_eq (hs.balance v)).trans (hvalue v)
  have hsmall : (z.allocation e).den ≤ d := Nat.le_of_dvd hd (hden e)
  have hnum : |((z.allocation e).num : ℚ)| ≤ (d : ℚ)*(H : ℚ) := by
    rw [← Rat.mul_den_eq_num, abs_of_nonneg (mul_nonneg (hs.nonneg _) (Nat.cast_nonneg _)), mul_comm]
    exact mul_le_mul (by exact_mod_cast hsmall) hmass (hs.nonneg e) (Nat.cast_nonneg _)
  have hint : |(z.allocation e).num| ≤ ((d*H : ℕ) : ℤ) := by exact_mod_cast hnum
  exact Int.ofNat_le.mp (by simpa using hint)

end Kintali.QuotaSweep.Book
