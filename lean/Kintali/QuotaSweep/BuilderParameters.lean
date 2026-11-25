module

public import Kintali.QuotaSweep.BuilderBook

/-! # Exact quota rates, buyer masses and budget target of a selected run -/

@[expose] public section
namespace Kintali.QuotaSweep.SelectedBuilder

open Kintali.ExactRecovery Kintali.InputOutput Kintali.MarketTrial Kintali.QuoteSearch Kintali.ContactSize
open Kintali.TrialWork.Selected StochasticGames.CompilerRun StochasticGames.BinarySize

variable {a : Input} {toSite : Fin a.types → Fin a.targets} {s : Selection (a.types*a.targets)}

def siteRate (d : TrialWork.Fields a.types a.targets) (j : Fin a.targets) : Run ℚ := do
  let q ← d.gain j
  let live ← TrialWork.lt 0 q
  if live then TrialWork.inverse q else step 0 0

theorem siteRate_value (d : TrialWork.Fields a.types a.targets) (j : Fin a.targets) :
    (siteRate d j).value = BudgetContact.rate d.game j := by
  by_cases h : 0 < (d.gain j).value <;> simp [siteRate,BudgetContact.rate,TrialWork.Fields.game,h]

def buyerMass (l : Lists a toSite s) (d : TrialWork.Fields a.types a.targets) (unit : ℚ) :
    Buyers a toSite s → Run ℚ
  | .inl i => d.prior i
  | .inr h => do
    let live ← active d h.1
    if live then
      let count ← groupSize l h
      let num ← RankRun.scaleIndex count
      TrialWork.times num unit
    else step 0 0

theorem buyerMass_value (l : Lists a toSite s) (d : TrialWork.Fields a.types a.targets) (hd : d.game = a.game)
    (σ : ℚ) (b : Buyers a toSite s) :
    (buyerMass l d (σ/grid a.game) b).value =
      (Sparse.selectedParameters (G := grid a.game) a.game toSite s σ).mass b := by
  rcases b with i|h
  · exact congrArg (fun g : Game (Fin a.types) (Fin a.targets) => g.prior i) hd
  · change _ = (if 0 < a.game.gain h.1 then _ else _)
    by_cases live : 0 < a.game.gain h.1 <;> simp [buyerMass,RankRun.scaleIndex,hd,live]

def rowsOf {T : Type} (xs : List T) (f : T → Run ℚ) : Run (List (T × ℚ)) :=
  StochasticGames.CompilerRun.mapM (fun i => do let x ← f i; step 0 (i,x)) xs

def readRow {T : Type} [Encodable T] (xs : List (T × ℚ)) (t : T) : ℚ :=
  (@Kintali.QuotaSweep.Work.search _ _ Book.encodedEq t 0 xs).1

theorem readRow_rowsOf {T : Type} [Encodable T] (xs : List T) (f : T → Run ℚ) (t : T) (mem : t ∈ xs) :
    readRow (rowsOf xs f).value t = (f t).value := by
  let : DecidableEq T := Book.encodedEq
  have h := @Kintali.QuotaSweep.Work.read_tabulate T ℚ Book.encodedEq (fun i => ((f i).value,0)) xs 0 t mem
  rw [Kintali.QuotaSweep.Work.tabulate_value] at h
  simpa [readRow,rowsOf] using h

theorem rowsOf_work {T : Type} (xs : List T) (f : T → Run ℚ) {k w : ℕ} (cells : ∀ t, (f t).Bound k w) :
    (rowsOf xs f).Bound (xs.length*(k+3)+1) w :=
  mapM_bound _ _ (k+1) w (fun i _ => bound_bind (cells i) ((bound_step 0 _).weaken le_rfl (Nat.zero_le _)))

def quotaData (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets)
    (o : Orders a toSite s) (ok : o.Valid) : Run (Parameters (Buyers a toSite s) (Fin a.targets)) := do
  let scale ← step 0 st.prepared.scales.privateScale
  let grid ← step 0 st.prepared.scales.grid
  let den ← RankRun.scaleIndex grid
  let unit ← TrialWork.divide scale den
  let rates ← rowsOf o.sites (siteRate st.tables.fields)
  let masses ← rowsOf o.buyers (buyerMass l st.tables.fields unit)
  let active ← privateBuyers st.tables.fields o ok
  let gain ← MaximaWork.scan st.tables.fields.gain o.sites
  let upper ← TrialWork.plus 1 gain
  let resources ← RankRun.scaleIndex st.tables.resources
  let target ← TrialWork.times scale resources
  step 0 ⟨readRow rates,readRow masses,active,upper,target⟩

set_option maxHeartbeats 1600000 in
theorem quotaData_value (l : Lists a toSite s) (st : InitializationWork.State a.types a.targets)
    {hm : 0 < a.targets} (correct : InitializationWork.Correct a hm st)
    (o : Orders a toSite s) (ok : o.Valid) (sites : o.sites = List.finRange a.targets) :
    (quotaData l st o ok).value = Sparse.selectedParameters (G := grid a.game) a.game toSite s (privateScale a.game) := by
  let g := a.game
  have gain : (MaximaWork.scan st.tables.fields.gain o.sites).value = maxGain a.game := by
    rw [sites,← MaximaWork.over_value]
    exact (MaximaWork.gain_value st.tables.fields).trans (congrArg maxGain correct.game)
  have res := congrArg Game.resources correct.game
  change st.tables.resources = a.game.resources at res
  have rates : readRow (rowsOf o.sites (siteRate st.tables.fields)).value = BudgetContact.rate a.game := by
    funext j
    rw [readRow_rowsOf _ _ _ (ok.sites_complete j),siteRate_value,NormalizedWork.Tables.fields_game,correct.game]
  have masses : readRow (rowsOf o.buyers
      (buyerMass l st.tables.fields (privateScale a.game/grid a.game))).value =
      (Sparse.selectedParameters (G := grid a.game) a.game toSite s (privateScale a.game)).mass := by
    funext b
    rw [readRow_rowsOf _ _ _ (ok.buyers_complete b)]
    exact buyerMass_value l st.tables.fields correct.game _ b
  have mask := privateBuyers_value st.tables.fields correct.game o ok
  simp only [quotaData,Run.bind_value,step_value,RankRun.scaleIndex,correct.grid,correct.privateScale,
    TrialWork.divide_value,TrialWork.plus_value,TrialWork.times_value,rates,masses,mask,gain,res]
  rfl

end Kintali.QuotaSweep.SelectedBuilder
