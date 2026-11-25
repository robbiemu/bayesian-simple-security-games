module

public import Kintali.TrialWork.RowRules

/-! Materialize the reference, mark and status vectors once. The rule
reader and the mathematical branch pattern point to the same arrays. -/

@[expose] public section
namespace Kintali.TrialWork

open StochasticGames.CompilerRun ExactRecovery LinearProgramming.ArithmeticRun

variable {k m : ℕ}

def savedRules (refs : Vector (Fin m) k) (marks : Vector (Vector Bool m) k)
    (states : Vector Status m) : RuleFields k m where
  reference i := step k.size refs[i.val]
  marked i j := do
    let row ← step k.size marks[i.val]
    step m.size row[j.val]
  status j := step m.size states[j.val]

theorem savedRules_bound (refs : Vector (Fin m) k) (marks : Vector (Vector Bool m) k)
    (states : Vector Status m) {w : ℕ} (hk : k.size ≤ w) (hm : m.size ≤ w) :
    RuleBound (savedRules refs marks states) 2 w :=
  ⟨fun _ => ⟨show 1 ≤ 2 by decide,hk⟩,fun _ _ => ⟨le_rfl,max_le hk hm⟩,
    fun _ => ⟨show 1 ≤ 2 by decide,hm⟩⟩

def preparePattern (d : Fields k m) (v : Point k m) (hm : 0 < m) (tol : 0 ≤ v.tolerance) :
    Run (Pattern (Fin k) (Fin m) × RuleFields k m) :=
  let refs := tabulate k (fun i => bestFin m hm (d.pointCost v i))
  let marks := tabulate k (fun i => tabulate m (mark d v refs.value i))
  let states := tabulate m (status v)
  let p : Pattern (Fin k) (Fin m) :=
    ⟨fun i => refs.value[i.val],fun i j => marks.value[i.val][j.val],by
      intro i
      simp only [marks,tabulate_value,Vector.getElem_ofFn,mark_value,decide_eq_true_eq]
      exact le_add_of_nonneg_right tol,fun j => states.value[j.val]⟩
  ⟨(p,savedRules refs.value marks.value states.value),
    refs.work.seq (marks.work.seq (states.work.seq (Work.one 0)))⟩

@[simp] theorem preparePattern_value (d : Fields k m) (v : Point k m) (hm : 0 < m)
    (tol : 0 ≤ v.tolerance) : (preparePattern d v hm tol).value.1 =
    contactPattern d.game v.x (d.game.bestTarget hm v.x) v.tolerance tol :=
  pattern_value ..

theorem preparePattern_reads (d : Fields k m) (v : Point k m) (hm : 0 < m)
    (tol : 0 ≤ v.tolerance) :
    RuleReads (preparePattern d v hm tol).value.2 (preparePattern d v hm tol).value.1 :=
  ⟨fun _ => rfl,fun _ _ => rfl,fun _ => rfl⟩

theorem preparePattern_bound (d : Fields k m) {v : Point k m} {c w : ℕ} (ok : FieldBound d c w)
    (point : PointBound v w) (hm : 0 < m) (tol : 0 ≤ v.tolerance) :
    (preparePattern d v hm tol).Bound (patternSlots k m c w) (patternWidth w) ∧
    RuleBound (preparePattern d v hm tol).value.2 2 w :=
  ⟨pattern_work d ok point hm tol,savedRules_bound _ _ _ ok.kSize ok.mSize⟩

end Kintali.TrialWork
