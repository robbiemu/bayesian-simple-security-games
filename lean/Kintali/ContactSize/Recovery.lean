module

public import Kintali.ContactSize.View
public import Kintali.LinearProgramming.OutputSize
import all Kintali.InputOutput.Grid

/-! Length of the dense exact repair input formed from a sparse trial, and
the reduced compact strategy produced by that repair. -/

open scoped BigOperators

@[expose] public section
namespace Kintali.ContactSize

open ExactRecovery MarketTrial InputOutput LinearProgramming

private theorem sum_entries {n b : ℕ} (f : Fin n → ℕ) (h : ∀ j, f j ≤ b) :
    (∑ j, f j) ≤ n*b := by
  simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ => b) (fun j _ => h j)

private theorem rhs_fits {k m : ℕ} (g : Game (Fin k) (Fin m)) (p : Pattern (Fin k) (Fin m))
    (i : Fin (exactRows k m)) : |(exactSystem g p).rhs i| ≤ (coefficientHeight g : ℤ) := by
  rw [coefficientHeight_cast]
  cases hr : (rowIndex k m).symm i with
  | inl r => simpa only [exactSystem,hr] using rhs_bound g p r
  | inr u => simpa [exactSystem,hr] using (mul_nonneg (by decide : (0:ℤ) ≤ 2) (atomBound_pos g).le)

private theorem intSize {z : ℤ} {h : ℕ} (hz : |z| ≤ (h : ℤ)) :
    RationalInput.integerBits z ≤ h.size+1 := by
  have h' : z.natAbs ≤ h := Int.ofNat_le.mp (by simpa using hz)
  exact Nat.add_le_add_right (Nat.size_le_size h') 1

/-- Width of the stored matrix, coordinates, bounds and dimensions together. -/
def repairLength (L : ℕ) :=
  let U := Binary.repairBound L
  let W := viewWidth L+toleranceWidth L
  3*U+3 + U*((U+1)+U*(U+1)) + U*(2*W+2)

theorem recovery_length (a : Input) (valid : a.Valid) (p : Pattern (Fin a.types) (Fin a.targets))
    (v : ContactView a.types a.targets (grid a.game))
    (fits : ViewFits (viewWidth (Binary.lengthInput a)) v) :
    RationalInput.inputLength (recoveryInput a.game p)
      (recoveryPoint v.coverage v.joint v.pressure (contactTolerance a.game))
      (coefficientHeight a.game) ≤ repairLength (Binary.lengthInput a) := by
  let L := Binary.lengthInput a
  let U := Binary.repairBound L
  let W := viewWidth L+toleranceWidth L
  let g := a.game
  let m := exactRows a.types a.targets
  let n := exactVars a.types a.targets
  let P := recoveryInput g p
  let x := recoveryPoint v.coverage v.joint v.pressure (contactTolerance g)
  let h := coefficientHeight g
  obtain ⟨rows,cols,hb,_⟩ := Binary.repair_bounds a valid
  change m ≤ U at rows
  change n ≤ U at cols
  change h.size ≤ U at hb
  have cs (i : Fin m) (j : Fin n) : RationalInput.integerBits (P.system.coeff i j) ≤ U+1 := by
    change RationalInput.integerBits ((recoveryInput g p).system.coeff i j) ≤ U+1
    rw [recoveryInput_system]
    exact (intSize (exactSystem_coeff_bound g p i j)).trans (Nat.add_le_add_right hb 1)
  have bs (i : Fin m) : RationalInput.integerBits (P.system.rhs i) ≤ U+1 := by
    change RationalInput.integerBits ((recoveryInput g p).system.rhs i) ≤ U+1
    rw [recoveryInput_system]
    exact (intSize (rhs_fits g p i)).trans (Nat.add_le_add_right hb 1)
  have xs (j : Fin n) : Fits W x[j.val] := by
    have hv : viewWidth L ≤ W := Nat.le_add_right ..
    change Fits W (recoveryPoint v.coverage v.joint v.pressure (contactTolerance g))[j.val]
    simp only [recoveryPoint,Vector.getElem_ofFn]
    rcases (varIndex a.types a.targets).symm j with ⟨i,t⟩|t|e
    · exact (fits.joint i t).mono hv
    · exact (fits.coverage t).mono hv
    · cases e
      · exact fits.pressure.mono hv
      · exact (tolerance_fits a valid).mono (Nat.le_add_left ..)
  have matrix := sum_entries (fun i : Fin m => RationalInput.integerBits (P.system.rhs i) +
      ∑ j : Fin n, RationalInput.integerBits (P.system.coeff i j))
    (fun i => Nat.add_le_add (bs i) ((sum_entries _ (cs i)).trans (Nat.mul_le_mul_right _ cols)))
  have coords := sum_entries (fun j : Fin n =>
      RationalInput.integerBits x[j.val].num + x[j.val].den.size + 1)
    (b := 2*W+2) (by
      intro j
      have z := xs j
      dsimp only [RationalInput.integerBits]
      obtain ⟨hn,hd⟩ := z
      omega)
  change m+n+3+h.size + _ + _ ≤ 3*U+3+U*((U+1)+U*(U+1))+U*(2*W+2)
  apply Nat.add_le_add (Nat.add_le_add (by omega) (matrix.trans (Nat.mul_le_mul_right _ rows)))
    (coords.trans (Nat.mul_le_mul_right _ cols))

/-- The actual grouped trial feeds this polynomial-size instance to the exact repair. -/
theorem sparse_recovery_length (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (s : QuoteSearch.Selection (a.types*a.targets)) (hSelect : SelectionBound a s)
    (p : Pattern (Fin a.types) (Fin a.targets)) :
    let v := sparseView a.game valid.1 s
    RationalInput.inputLength (recoveryInput a.game p)
      (recoveryPoint v.coverage v.joint v.pressure (contactTolerance a.game))
      (coefficientHeight a.game) ≤ repairLength (Binary.lengthInput a) :=
  recovery_length a valid p _ (sparse_view a valid normal s hSelect)

def strategyWidth (L : ℕ) := 2*RationalInput.widthLimit (repairLength L)+2*L+2

def repairWork (L : ℕ) := RationalInput.binaryLimit (repairLength L)

/-- Charged binary work for the repair subroutine invoked by the grouped
trial, expressed directly in the public payoff-table length. -/
theorem sparse_recovery_work (a : Input) (valid : a.Valid) (normal : ¬a.game.DirectCase)
    (s : QuoteSearch.Selection (a.types*a.targets)) (hSelect : SelectionBound a s)
    (p : Pattern (Fin a.types) (Fin a.targets)) :
    let g := a.game
    let v := sparseView g valid.1 s
    let h := coefficientHeight g
    let P := recoveryInput g p
    let x := recoveryPoint v.coverage v.joint v.pressure (contactTolerance g)
    RecoveryRun.binaryWork (RationalInput.inputLength P x h) (RationalInput.run P x h).work ≤
      repairWork (Binary.lengthInput a) := by
  dsimp only
  have cap := sparse_recovery_length a valid normal s hSelect p
  dsimp only at cap
  apply (RationalInput.run_binary_work _ _ (coefficientHeight_pos a.game) ?_).trans
  · unfold repairWork RationalInput.binaryLimit RationalInput.slotLimit RationalInput.widthLimit
      RecoveryRun.transitionLimit RecoveryRun.operandLimit PivotRun.width RecoveryRun.scale
      PointEncoding.wordLimit
    gcongr
  · intro i j
    rw [recoveryInput_system]
    exact exactSystem_coeff_bound a.game p i j

private theorem width_mono {S T : ℕ} (h : S ≤ T) :
    RationalInput.widthLimit S ≤ RationalInput.widthLimit T := by
  unfold RationalInput.widthLimit RecoveryRun.operandLimit PointEncoding.wordLimit
    PivotRun.width RecoveryRun.scale
  gcongr

/-- Bounds include conditioning the repaired joint flow by each nonzero prior. -/
theorem repair_strategy (a : Input) (valid : a.Valid) (p : Pattern (Fin a.types) (Fin a.targets))
    (v : ContactView a.types a.targets (grid a.game))
    (fits : ViewFits (viewWidth (Binary.lengthInput a)) v) :
    let s := repair a.game p v.coverage v.joint v.pressure (contactTolerance a.game)
    let b := strategyWidth (Binary.lengthInput a)
    (∀ j, Fits b (s.coverage j)) ∧ ∀ i j, Fits b (s.attacks i j) := by
  let L := Binary.lengthInput a
  let g := a.game
  let P := recoveryInput g p
  let x := recoveryPoint v.coverage v.joint v.pressure (contactTolerance g)
  let h := coefficientHeight g
  let z := RationalInput.run P x h
  let W := RationalInput.widthLimit (repairLength L)
  have coeff (i j) : |P.system.coeff i j| ≤ (h : ℤ) := by
    change |(recoveryInput g p).system.coeff i j| ≤ _
    rw [recoveryInput_system]
    exact exactSystem_coeff_bound g p i j
  have bound : z.work.width ≤ W := (RationalInput.run_work P x
    (coefficientHeight_pos g) coeff).2.trans (width_mono (recovery_length a valid p v fits))
  obtain ⟨hd,hn⟩ := OutputSize.rational_fields P x h
  change z.value.den.natAbs.size ≤ 2*z.work.width at hd
  change ∀ j : Fin (exactVars a.types a.targets), z.value.num[j.val].natAbs.size ≤ z.work.width at hn
  have bit (j) : Fits (2*W+1) (z.value.value j) := by
    by_cases zero : z.value.den = 0
    · change Fits _ (Rat.divInt _ z.value.den)
      rw [zero,Rat.divInt_zero]
      exact Fits.zero.mono (by omega)
    · have aux := divInt_parts_le z.value.num[j.val] z.value.den zero
      have nbit := (Nat.size_le_size aux.1).trans ((hn j).trans bound)
      have dbit := (Nat.size_le_size aux.2).trans (hd.trans (Nat.mul_le_mul_left 2 bound))
      exact ⟨by change (Rat.divInt _ _).num.natAbs.size ≤ _; omega,
        by change (Rat.divInt _ _).den.size ≤ _; omega⟩
  have size : 2*W+1 ≤ strategyWidth L := by dsimp only [W,strategyWidth]; omega
  have trivialWidth : 1 ≤ strategyWidth (Binary.lengthInput a) := by unfold strategyWidth; omega
  constructor
  · intro j
    exact (bit (varIndex a.types a.targets (.inr (.inl j)))).mono size
  · intro i j
    change Fits _ (if g.prior i = 0 then (if j = p.reference i then 1 else 0)
      else z.value.value (varIndex a.types a.targets (.inl (i,j)))/g.prior i)
    split
    · split
      · exact Fits.one.mono trivialWidth
      · exact Fits.zero.mono trivialWidth
    · exact ((bit _).div (Binary.datum_parts a valid (prior_mem g i))).mono (by
        change (2*W+1)+(2*L+1) ≤ 2*W+2*L+2; omega)

end Kintali.ContactSize
