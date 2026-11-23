module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Selecting a nonsingular system of active rows -/

public section

namespace StochasticGames.TightRows

variable {K k n : Type*} [Field K] [Fintype n]

private theorem finrank_row_span [Fintype k] (M : Matrix k n K)
    (hinj : Function.Injective M.mulVecLin) :
    Module.finrank K (Submodule.span K (Set.range M.row)) = Fintype.card n := by
  rw [← M.rank_eq_finrank_span_row, Matrix.rank, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_eq_card_basis (Pi.basisFun K n)]

private theorem exists_nonsingular_row_selection [Fintype k] [DecidableEq n] (M : Matrix k n K)
    (hinj : Function.Injective M.mulVecLin) :
    ∃ g : n → k, (M.submatrix g id).det ≠ 0 := by
  classical
  obtain ⟨f, hf, _, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range M.row)
  let e := Fintype.equivFinOfCardEq (finrank_row_span M hinj).symm
  choose g hg using fun i : n => hf (e i)
  refine ⟨g, Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_row ?_)⟩
  have hrows : (M.submatrix g id).row = f ∘ e := by
    funext i
    exact hg i
  rw [hrows]
  exact hli.comp e e.injective

/-- If the active rows have trivial common kernel, some square selection of active rows
has nonzero determinant. The ambient collection of rows may be infinite. -/
theorem exists_active_nonsingular_submatrix [DecidableEq n] (A : Matrix k n K) (S : Finset k)
    (h : ∀ d : n → K, (∀ i ∈ S, A.mulVec d i = 0) → d = 0) :
    ∃ g : n → k, (∀ i, g i ∈ S) ∧ (A.submatrix g id).det ≠ 0 := by
  classical
  let M : Matrix S n K := A.submatrix Subtype.val id
  have hinj : Function.Injective M.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro d hd
    apply h d
    intro i hi
    exact congrFun hd ⟨i, hi⟩
  obtain ⟨g, hg⟩ := exists_nonsingular_row_selection M hinj
  exact ⟨fun i => (g i).val, fun i => (g i).property, hg⟩

end StochasticGames.TightRows
