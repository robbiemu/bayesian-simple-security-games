module

public import Kintali.TrialWork.QuotePredicates

/-! Scan the selected real labels for a buyer or site willing to take one
quote. The site compares its saved coverage to the price, then uses buyer
priority at equal quotes. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun StochasticGames.BinarySize ContactSize ExactRecovery QuotaSweep
variable {k m G : ℕ} {A H : Type}

namespace Access

variable (a : Access k m G A H)

def positive (r : Sparse.R (Fin k) (Fin m) A H) : Run Bool :=
  a.holding r >>= lt 0

@[simp] theorem positive_value (r) : (a.positive r).value = decide (0 < (a.holding r).value) := by
  simp [positive]

theorem positive_work {c w : ℕ} (ok : AccessBound a c w) (r) :
    (a.positive r).Bound (c+4) (blockWidth w) := by
  have h : w ≤ blockWidth w := by unfold blockWidth scalarWidth; omega
  apply bound_bind ((ok.holding _).weaken le_rfl h)
  exact (lt_work (Fits.zero.mono ok.positive) (ok.fits _)).weaken le_rfl (by unfold blockWidth scalarWidth; omega)

def buyerRow (d : Fields k m) (i : Fin k) (j : Fin m) (z : Quote G) (rec : A) : Run Bool := do
  let b ← a.real rec
  land (finEqual b.1 i) (land (a.positive (bid (.inl rec))) (better d i j b.2.1 z b.2.2))

def siteRow (i : Fin k) (j : Fin m) (z : Quote G) (rec : A) : Run Bool := do
  let b ← a.real rec
  land (finEqual b.2.1 j) (land (finEqual b.2.2 z) (land (finLess i b.1) (a.positive (bid (.inl rec)))))

def buyer (d : Fields k m) (reals : List A) (i : Fin k) (j : Fin m) (z : Quote G) : Run Bool :=
  lor (a.positive (outside (.inl i))) (anyM (a.buyerRow d i j z) reals)

def siteTest (v : Point k m) (reals : List A) (i : Fin k) (j : Fin m) (z : Quote G) : Run Bool := do
  let x ← v.readX j
  let t ← priceOf z
  lor (lt x t) (land (eqRat x t)
    (lor (a.positive (vacancy j)) (anyM (a.siteRow i j z) reals)))

theorem buyer_value [DecidableEq A] [Fintype A] (d : Fields k m)
    {layout : Sparse.Layout (Fin k) (Fin m) G A H} {x : Sparse.R (Fin k) (Fin m) A H → ℚ}
    {f : Fin k → Fin m} (rd : Reads a d.game layout x f)
    (reals : List A) (complete : ∀ r, r ∈ reals) (i : Fin k) (j : Fin m) (z : Quote G) :
    (a.buyer d reals i j z).value = Sparse.buyerAcceptsQuote d.game Fin.val Fin.val layout x i j z := by
  apply Bool.eq_iff_iff.mpr
  simp only [buyer,lor_value,positive_value,rd.holding,anyM_value,List.any_eq_true,buyerRow,
    Run.bind_value,rd.real,land_value,finEqual_value,better_value,Bool.or_eq_true,Bool.and_eq_true,
    decide_eq_true_eq,Sparse.buyerAcceptsQuote]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨r,_,h,pos,key⟩
    exact ⟨r,h,pos,by rw [← h] at key ⊢; exact key⟩
  · rintro ⟨r,h,pos,key⟩
    exact ⟨r,complete r,h,pos,by rw [← h] at key ⊢; exact key⟩

theorem siteTest_value [DecidableEq A] [Fintype A] (v : Point k m)
    {g : Game (Fin k) (Fin m)} {layout : Sparse.Layout (Fin k) (Fin m) G A H}
    {x : Sparse.R (Fin k) (Fin m) A H → ℚ} {f : Fin k → Fin m} (rd : Reads a g layout x f)
    (reals : List A) (complete : ∀ r, r ∈ reals) (i : Fin k) (j : Fin m) (z : Quote G) :
    (a.siteTest v reals i j z).value = Sparse.siteAcceptsQuote v.x Fin.val layout x i j z := by
  apply Bool.eq_iff_iff.mpr
  simp only [siteTest,Run.bind_value,Point.readX_value,priceOf_value,lor_value,land_value,lt_value,
    eqRat_value,positive_value,rd.holding,anyM_value,List.any_eq_true,siteRow,rd.real,finEqual_value,
    finLess_value,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,Sparse.siteAcceptsQuote,
    Prod.ext_iff,complete,true_and,and_assoc]

def blockRowSlots (f c w : ℕ) := 2*c+betterSlots f w+24
def blockSlots (n f c w : ℕ) := 24+scalarSlots w+c+n*(blockRowSlots f c w+1)

theorem buyerRow_work (d : Fields k m) {f c w : ℕ} (af : AccessBound a c w)
    (df : FieldBound d f w) (grid : 2*(G.size+1) ≤ w) (i j z rec) :
    (a.buyerRow d i j z rec).Bound (blockRowSlots f c w) (blockWidth w) := by
  have h : w ≤ blockWidth w := by unfold blockWidth scalarWidth; omega
  have one := af.positive.trans h
  unfold buyerRow
  apply Run.Bound.weaken (k := c+(1+((c+4+(betterSlots f w+1))+1))) (w := blockWidth w) ?_
    (by unfold blockRowSlots; omega) le_rfl
  apply bound_bind ((af.real rec).weaken le_rfl h)
  apply land_work (finEqual_work _ _ (af.buyers.trans h)) ?_ one
  exact land_work (a.positive_work af _) (better_work d df grid i j _ z _) one

theorem siteRow_work {f c w : ℕ} (af : AccessBound a c w) (grid : 2*(G.size+1) ≤ w) (i j z rec) :
    (a.siteRow i j z rec).Bound (blockRowSlots f c w) (blockWidth w) := by
  have h : w ≤ blockWidth w := by unfold blockWidth scalarWidth; omega
  have one := af.positive.trans h
  have gs : (G+1).size ≤ blockWidth w := (size_succ_le _).trans (by omega)
  unfold siteRow
  apply Run.Bound.weaken (k := c+(1+((1+((1+((c+4)+1))+1))+1))) (w := blockWidth w) ?_
    (by unfold blockRowSlots; omega) le_rfl
  apply bound_bind ((af.real rec).weaken le_rfl h)
  apply land_work (finEqual_work _ _ (af.sites.trans h)) ?_ one
  apply land_work (finEqual_work _ _ gs) ?_ one
  exact land_work (finLess_work _ _ (af.buyers.trans h)) (a.positive_work af _) one

theorem buyer_work (d : Fields k m) {n f c w : ℕ} (af : AccessBound a c w) (df : FieldBound d f w)
    (grid : 2*(G.size+1) ≤ w) (reals : List A) (len : reals.length ≤ n) (i j z) :
    (a.buyer d reals i j z).Bound (blockSlots n f c w) (blockWidth w) := by
  have any := anyM_work _ reals (a.buyerRow_work d af df grid i j z)
  have b := lor_work (a.positive_work af (outside (.inl i))) any
    (show 1 ≤ blockWidth w by unfold blockWidth scalarWidth; omega)
  have nm := Nat.mul_le_mul_right (blockRowSlots f c w+1) len
  exact b.weaken (by unfold blockSlots; omega) le_rfl

theorem siteTest_work {n f c w : ℕ} {v : Point k m} (af : AccessBound a c w) (vfit : PointBound v w)
    (grid : 2*(G.size+1) ≤ w) (reals : List A) (len : reals.length ≤ n) (i j z) :
    (a.siteTest v reals i j z).Bound (blockSlots n f c w) (blockWidth w) := by
  have h : w ≤ blockWidth w := by unfold blockWidth scalarWidth; omega
  have narrow : scalarWidth w ≤ blockWidth w := by unfold blockWidth scalarWidth; omega
  have one := af.positive.trans h
  have x := vfit.coverage j
  have p := price_fits grid z
  have any := anyM_work _ reals (a.siteRow_work (f := f) af grid i j z)
  have keys := lor_work ((lt_work x p).weaken le_rfl narrow) (land_work
    ((eqRat_work x p).weaken le_rfl narrow) (lor_work (a.positive_work af (vacancy j)) any one) one) one
  have nm := Nat.mul_le_mul_right (blockRowSlots f c w+1) len
  unfold siteTest
  apply Run.Bound.weaken (k := 1+((6+scalarSlots w)+
    (4+((3+(((c+4)+((1+reals.length*(blockRowSlots f c w+1))+1))+1))+1)))) (w := blockWidth w) ?_
    (by unfold blockSlots; omega) le_rfl
  apply bound_bind ((v.readX_bound j af.sites).weaken le_rfl h)
  apply bound_bind ((priceOf_work grid z).weaken le_rfl narrow)
  rw [Point.readX_value,priceOf_value]
  exact keys

end Access
end Kintali.TrialWork
