module

public import Kintali.ContactSize.Rational
public import Kintali.QuotaSweep.BitBounds
import all StochasticGames.Precision
import Mathlib.Tactic.Positivity

/-! Size of a grouped sweep in the number of records and the bit width of its parameters. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.ContactSize

open StochasticGames.BinarySize Kintali.QuotaSweep

/-- A uniform bound on the rate, mass, target and upper endpoint fields. -/
structure ParametersFit {B S : Type*} (w : ℕ) (P : Parameters B S) : Prop where
  rate : ∀ s, Fits w (P.rate s)
  mass : ∀ b, Fits w (P.mass b)
  target : Fits w P.target
  upper : Fits w P.upper

private theorem scaleList {w : ℕ} (xs : List ℚ) (all : ∀ x ∈ xs, x.den.size ≤ w) :
    (StochasticGames.Precision.denominator xs).size ≤ 1+xs.length*w := by
  induction xs with
  | nil => simp [StochasticGames.Precision.denominator]
  | cons x xs ih =>
    change (x.den*StochasticGames.Precision.denominator xs).size ≤ 1+(xs.length+1)*w
    have head := all x (List.mem_cons_self ..)
    have tail := ih (fun r hr => all r (List.mem_cons_of_mem _ hr))
    have step := size_mul_le x.den (StochasticGames.Precision.denominator xs)
    rw [Nat.add_mul]
    omega

private theorem maxSize {a b w : ℕ} (ha : a.size ≤ w) (hb : b.size ≤ w) :
    (max a b).size ≤ w := by
  rcases le_total a b with h|h
  · simpa [max_eq_right h] using hb
  · simpa [max_eq_left h] using ha

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable [Fintype B] [Fintype S] [Fintype E] (K : Book B S E)

omit [Fintype B] [Fintype S] [Fintype E] in
private theorem scales {w r : ℕ} {P : Parameters B S} (fit : ParametersFit w P)
    (records : K.records.length ≤ r) :
    (K.initialScale P).size ≤ 1+(r+2)*w ∧
    (K.rateScale P.rate).size ≤ 1+r*w := by
  have zero := Fits.zero.mono fit.upper.pos
  constructor
  · rw [Book.initialScale]
    refine (scaleList _ ?_).trans (Nat.add_le_add_left (Nat.mul_le_mul_right w ?_) _)
    · intro x hx
      rcases List.mem_cons.mp hx with eq | hx
      · exact eq ▸ fit.target.2
      rcases List.mem_cons.mp hx with eq | hx
      · exact eq ▸ fit.upper.2
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      rcases e with e | b | s
      · exact zero.2
      · exact (fit.mass b).2
      · exact zero.2
    · simp only [List.length_cons, List.length_map]; omega
  · rw [Book.rateScale]
    refine (scaleList _ ?_).trans (Nat.add_le_add_left (Nat.mul_le_mul_right w ?_) _)
    · intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      rcases e with e | b | s
      · exact zero.2
      · exact zero.2
      · exact (fit.rate s).2
    · simpa using records

omit [Fintype B] [Fintype E] in
private theorem rateMagnitude {w : ℕ} {P : Parameters B S} (fit : ParametersFit w P) :
    (K.inputRateBound P).size ≤ (K.rateScale P.rate).size + w + 1 := by
  let D := K.rateScale P.rate
  have bound : K.inputRateBound P ≤ D*2^w := by
    apply Finset.sup_le
    intro s _
    apply Nat.ceil_le.mpr
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg D : (0:ℚ) ≤ D), Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (fit.rate s).abs_le (Nat.cast_nonneg _)
  have bits := (Nat.size_le_size bound).trans (size_mul_le ..)
  rw [Nat.size_pow] at bits
  omega

/-- Bit width of one factor by which an event can enlarge the common denominator. -/
def factorWidth (r w : ℕ) := 1+r*w+w+4*r+4

private theorem factor_size {w r : ℕ} {P : Parameters B S} (fit : ParametersFit w P)
    (records : K.records.length ≤ r) (inventory : Fintype.card (Record B S E) ≤ r) :
    (Book.factorBound B S (K.rateScale P.rate) (K.inputRateBound P)).size ≤ factorWidth r w := by
  let D := K.rateScale P.rate
  let A := K.inputRateBound P
  let V := Vertex B S
  let R := Routing.rateBound V D A
  have ds : D.size ≤ 1+r*w := (scales K fit records).2
  have a : A.size ≤ D.size + w+1 := rateMagnitude K fit
  have dim : Fintype.card E + (Fintype.card B + Fintype.card S) ≤ r := by
    simpa only [Record, Fintype.card_sum] using inventory
  have vb : Fintype.card V ≤ r := by dsimp [V, Vertex]; rw [Fintype.card_sum]; omega
  have vs := (size_le_self _).trans vb
  have op : (Fintype.card (Option V)).size ≤ r+1 := by
    rw [Fintype.card_option]
    exact (size_le_self _).trans (by omega)
  have rs : R.size ≤ D.size + w + 2*r + 2 := by
    apply maxSize
    · omega
    · have p := size_mul_le (Fintype.card V) A
      have t := size_mul_le (Fintype.card (Option V)) (Fintype.card V*A)
      omega
  have recs : (Book.recordBound B S D A).size ≤ r+R.size := by
    change (Fintype.card S*R+Fintype.card B*R).size ≤ _
    rw [← Nat.add_mul]
    exact (size_mul_le ..).trans (Nat.add_le_add_right ((size_le_self _).trans (by omega)) _)
  have bs : (Fintype.card B).size ≤ r := (size_le_self _).trans (by omega)
  change (max 1 (max D (max R (Fintype.card B * Book.recordBound B S D A)))).size ≤ _
  dsimp only [factorWidth]
  refine maxSize (by change 1 ≤ _; omega) (maxSize (by omega) (maxSize (by omega) ?_))
  have := size_mul_le (Fintype.card B) (Book.recordBound B S D A)
  omega

def denominatorWidth (r w : ℕ) := 1+(r+2)*w+factorWidth r w*(r+1)

def stateWidth (r w : ℕ) := denominatorWidth r w+2*(w+1)

/-- The denominator certificate for the actual first contact, with polynomial
binary length in the number of grouped records and parameter bit width. -/
theorem contact_scale {w r : ℕ} {P : Parameters B S} (fit : ParametersFit w P)
    (records : K.records.length ≤ r) (inventory : Fintype.card (Record B S E) ≤ r) :
    ∃ d : ℕ, 0 < d ∧ d.size ≤ denominatorWidth r w ∧
      (K.firstContact P).pressure.den ∣ d ∧ ∀ e, ((K.firstContact P).allocation e).den ∣ d := by
  obtain ⟨d, pos, bound, pressure, alloc⟩ := K.contact_denominator_bits P
  exact ⟨d,pos,bound.trans (Nat.add_le_add (scales K fit records).1
    (Nat.mul_le_mul (factor_size K fit records inventory) (Nat.add_le_add_right inventory 1))),
    pressure,alloc⟩

/-- Feasibility bounds the magnitude of every holding by one endpoint's
quota. The common scale then bounds the reduced numerator as well. -/
theorem state_of_scale {w r d : ℕ} {P : Parameters B S} {z : State B S E} (fit : ParametersFit w P)
    (feasible : K.Feasible P z) (nonneg : 0 ≤ z.pressure) (upper : z.pressure ≤ P.upper)
    (pos : 0 < d) (bits : d.size ≤ denominatorWidth r w) (pden : z.pressure.den ∣ d)
    (aden : ∀ e, (z.allocation e).den ∣ d) :
    Fits (stateWidth r w) z.pressure ∧ ∀ e, Fits (stateWidth r w) (z.allocation e) := by
  let M := 2^w
  have M1 : 1 ≤ M := Nat.one_le_pow _ _ (by decide)
  have ms : M.size = w+1 := Nat.size_pow
  have press : |z.pressure| ≤ (M : ℚ) := by
    rw [abs_of_nonneg nonneg]
    exact upper.trans ((le_abs_self _).trans fit.upper.abs_le)
  have lev (v : Vertex B S) : Book.quota P.rate P.mass z.pressure v ≤ ((M*M : ℕ) : ℚ) := by
    rcases v with b|s
    · change P.mass b ≤ _
      exact ((le_abs_self _).trans (fit.mass b).abs_le).trans (by
        exact_mod_cast (Nat.le_mul_of_pos_left M M1))
    · change P.rate s*z.pressure ≤ _
      rw [Nat.cast_mul]
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact mul_le_mul (fit.rate s).abs_le press (abs_nonneg _) (Nat.cast_nonneg _)
  constructor
  · exact (Fits.of_den_of_abs (Nat.le_of_dvd pos pden) press).mono (by dsimp [stateWidth]; omega)
  · intro e
    have incident : (K.market.ends e).Nonempty :=
      Finset.card_pos.mp ((K.market.degree e).elim (fun h => by omega) (fun h => by omega))
    obtain ⟨v,hv⟩ := incident
    have hle := Finset.single_le_sum (f := fun f => if v ∈ K.market.ends f then z.allocation f else 0)
      (fun f _ => by split; exact feasible.nonneg f; exact le_rfl) (Finset.mem_univ e)
    simp only [hv, ↓reduceIte] at hle
    have cap : |z.allocation e| ≤ ((M*M : ℕ) : ℚ) := by
      rw [abs_of_nonneg (feasible.nonneg e)]
      exact (hle.trans_eq (feasible.balance v)).trans (lev v)
    exact (Fits.of_den_of_abs (Nat.le_of_dvd pos (aden e)) cap).mono (by
      have c := size_mul_le M M
      dsimp only [stateWidth]; omega)

/-- Signed numerator magnitudes and denominators of all contact state entries. -/
theorem contact_state {w r : ℕ} {P : Parameters B S} (fit : ParametersFit w P)
    (records : K.records.length ≤ r) (inventory : Fintype.card (Record B S E) ≤ r)
    (feasible : K.Feasible P (K.firstContact P)) (nonneg : 0 ≤ (K.firstContact P).pressure)
    (upper : (K.firstContact P).pressure ≤ P.upper) :
    Fits (stateWidth r w) (K.firstContact P).pressure ∧
      ∀ e, Fits (stateWidth r w) ((K.firstContact P).allocation e) := by
  obtain ⟨d, pos, bits, pden, aden⟩ := contact_scale K fit records inventory
  exact state_of_scale K fit feasible nonneg upper pos bits pden aden
end Kintali.ContactSize
