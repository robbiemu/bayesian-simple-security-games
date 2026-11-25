module

public import Kintali.ContactSize.Sweep
public import Kintali.InputOutput.Grid
public import Kintali.QuotaSweep.SparseContact
import all Kintali.InputOutput.Grid

/-! Binary input lengths of the rational data supplied to a selected grouped trial. -/

@[expose] public section
namespace Kintali.ContactSize

open ExactRecovery MarketTrial InputOutput LinearProgramming StochasticGames.BinarySize

def toleranceWidth (L : ℕ) :=
  let U := Binary.repairBound L
  8+(1+U*(U+3+2*U))+16*(U+2)^3

def scaleWidth (L : ℕ) := toleranceWidth L + (2*L+1)

def parameterWidth (L : ℕ) := scaleWidth L + (2*L+1) + 2*(Binary.gridBitBound L+1)+5

theorem tolerance_fits (a : Input) (valid : a.Valid) :
    Fits (toleranceWidth (Binary.lengthInput a)) (contactTolerance a.game) := by
  let L := Binary.lengthInput a
  let U := Binary.repairBound L
  let g := a.game
  let H := height g
  let D := SlackWindow.divisor (exactRows a.types a.targets) (exactVars a.types a.targets)
    (coefficientHeight g)
  obtain ⟨rows, cols, coeffs, data⟩ := Binary.repair_bounds a valid
  have ds : D.size ≤ 16*(U+2)^3 := SlackWindow.divisor_size_polynomial rows cols coeffs
  have nv : Fintype.card (Variable (Fin a.types) (Fin a.targets)) = exactVars a.types a.targets := by
    simp [exactVars]
  have hs : H.size ≤ 1+U*(U+3+2*U) := by
    have hh := height_size g
    dsimp only at hh
    rw [nv] at hh
    exact hh.trans (Nat.add_le_add_left (Nat.mul_le_mul cols (Nat.add_le_add
      (Nat.add_le_add_right ((size_le_self _).trans cols) 3) (Nat.mul_le_mul_left _ data))) 1)
  have etaFits : Fits (toleranceWidth L) (eta g) := by
    have h₄ : (4*H).size ≤ 3+H.size := size_mul_le 4 H
    have fit := (Fits.natCast (4*H)).inv
    rw [Nat.cast_mul, Nat.cast_ofNat] at fit
    exact (by simpa only [eta, one_div, H] using fit : Fits ((4*H).size+1) (eta g)).mono (by
      change (4*H).size+1 ≤ 8+(1+U*(U+3+2*U))+16*(U+2)^3
      omega)
  have roundFits : Fits (toleranceWidth L) (roundingPrecision g) := by
    change Fits _ (1/(D : ℚ))
    rw [one_div]
    exact (Fits.natCast D).inv.mono (by
      change D.size+1 ≤ 8+(1+U*(U+3+2*U))+16*(U+2)^3
      omega)
  change Fits _ (min (eta g) (roundingPrecision g))
  rcases le_total (eta g) (roundingPrecision g) with h|h
  · simpa only [min_eq_left h] using etaFits
  · simpa only [min_eq_right h] using roundFits

theorem gain_fits (a : Input) (valid : a.Valid) : Fits (2*Binary.lengthInput a+1) (maxGain a.game) := by
  have mem : maxGain a.game ∈ insert 0 (Finset.univ.image a.game.gain) := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp mem with zero | rest
  · rw [zero]
    exact Fits.zero.mono (by omega)
  · obtain ⟨j,_,eq⟩ := Finset.mem_image.mp rest
    rw [← eq]
    exact Binary.datum_parts a valid (gain_mem a.game j)

theorem scale_fits (a : Input) (valid : a.Valid) :
    Fits (scaleWidth (Binary.lengthInput a)) (privateScale a.game) := by
  apply (tolerance_fits a valid).div
  rcases le_total 1 (maxGain a.game) with h|h
  · rw [max_eq_right h]
    exact gain_fits a valid
  · rw [max_eq_left h]
    exact Fits.one.mono (by omega)

theorem parameters_fit (a : Input) (valid : a.Valid) (redirect : Fin a.types → Fin a.targets)
    (s : QuoteSearch.Selection (a.types*a.targets)) :
    ParametersFit (parameterWidth (Binary.lengthInput a)) (Sparse.selectedParameters
      (G := grid a.game) a.game redirect s (privateScale a.game)) := by
  let L := Binary.lengthInput a
  let g := a.game
  let G := grid g
  let D := Sparse.partition (G := G) g redirect s
  let layout := Sparse.selectedLayout (G := G) g redirect s
  let σ := privateScale g
  let W := parameterWidth L
  have sfit : Fits (scaleWidth L) σ := scale_fits a valid
  have gs : G.size ≤ Binary.gridBitBound L := Binary.grid_size a valid
  have small : 2*L+1 ≤ W := by dsimp [W,parameterWidth]; omega
  have zero : Fits W 0 := Fits.zero.mono (by omega)
  constructor
  · intro j
    change Fits W (if 0 < g.gain j then (g.gain j)⁻¹ else 0)
    split
    · exact (Fits.inv (Binary.datum_parts a valid (gain_mem g j))).mono small
    · exact zero
  · rintro (i | h)
    · exact (Fits.mono (Binary.datum_parts a valid (prior_mem g i)) small)
    · change Fits W (if 0 < g.gain (layout.representative h).1 then
        (layout.size h : ℚ)*(σ/G) else 0)
      split
      · have group : layout.size h ≤ G :=
          (Nat.sub_le _ _).trans ((D h.1).hi_le_end h.2)
        have gs' := (Nat.size_le_size group).trans gs
        exact ((Fits.natCast (layout.size h)).mul (sfit.div (Fits.natCast G))).mono (by
          dsimp only [W,parameterWidth]; omega)
      · exact zero
  · change Fits W (σ*(g.resources : ℚ))
    exact (sfit.mul (Binary.datum_parts a valid (budget_mem g))).mono (by
      dsimp only [W,parameterWidth]; omega)
  · change Fits W (1+maxGain g)
    exact (Fits.one.add (gain_fits a valid)).mono (by dsimp only [W,parameterWidth,L]; omega)

end Kintali.ContactSize
