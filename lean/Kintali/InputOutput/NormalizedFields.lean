module

public import Kintali.InputOutput.NormalizedWork
public import Kintali.InputOutput.Bounds
public import Kintali.TrialWork.Fields

/-! # Charged vector access for the normalized trial game -/

@[expose] public section
namespace Kintali.InputOutput.NormalizedWork

open Binary ContactSize TrialWork ExactRecovery StochasticGames.CompilerRun StochasticGames.BinarySize

def Tables.fields {k m : ℕ} (t : Tables k m) : Fields k m where
  budget := t.resources
  prior i := step k.size t.priors[i.val]
  gain j := step m.size t.gains[j.val]
  intercept i j := do
    let r ← step k.size t.bids[i.val]
    step m.size r[j.val].1
  slope i j := do
    let r ← step k.size t.bids[i.val]
    step m.size r[j.val].2

@[simp] theorem Tables.fields_game {k m : ℕ} (t : Tables k m) : t.fields.game = t.game := rfl

theorem fields_bound (a : Input) (v : a.Valid) (t : Tables a.types a.targets) (ht : t.game = a.game) :
    FieldBound t.fields 2 (2*lengthInput a+1) := by
  let w := 2*lengthInput a+1
  have ks : a.types.size ≤ w := (size_le_self _).trans ((dimensions a).2.1.trans (by dsimp [w]; omega))
  have ms : a.targets.size ≤ w := (size_le_self _).trans ((dimensions a).1.trans (by dsimp [w]; omega))
  have hg : t.fields.game = a.game := ht
  have ft {x : ℚ} (h : x ∈ data t.fields.game) : Fits w x :=
    Binary.datum_parts a v (hg ▸ h)
  exact ⟨fun i => ⟨(bound_step _ _).weaken (by decide) ks, ft (prior_mem t.fields.game i)⟩,
    fun j => ⟨(bound_step _ _).weaken (by decide) ms, ft (gain_mem t.fields.game j)⟩,
    fun i j => ⟨⟨le_rfl,max_le ks ms⟩,ft (intercept_mem t.fields.game i j)⟩,
    fun i j => ⟨⟨le_rfl,max_le ks ms⟩,ft (slope_mem t.fields.game i j)⟩,
    (by
      have eq : t.fields.budget = a.1 := congrArg Game.resources hg
      rw [eq]
      exact (Fits.natCast _).mono (by have := (dimensions a).2.2; omega)),
    ks,ms,by omega⟩

theorem run_fields (a : Input) (v : a.Valid) :
    (run a).value.fields.game = a.game ∧ FieldBound (run a).value.fields 2 (2*lengthInput a+1) :=
  ⟨run_value a,fields_bound a v _ (run_value a)⟩

end Kintali.InputOutput.NormalizedWork
