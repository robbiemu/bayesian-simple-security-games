module

public import Kintali.QuotaSweep.Routing

/-! # Unit circulation on the single cycle containing a selected vertex -/

open scoped BigOperators
open Function

@[expose] public section
namespace Kintali.QuotaSweep.Routing

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Bounded orbit membership. A periodic seed visits every member of its
cycle within the number of graph vertices, including the terminal. -/
def onCycle (next : V → Option V) (seed v : V) : Bool :=
  decide (∃ k : Fin (Fintype.card (Option V)), (advance next)^[k.val] (some seed) = some v)

theorem onCycle_iff {next : V → Option V} {seed v : V} (hs : cyclic next seed = true) :
    onCycle next seed v = true ↔ ∃ k : ℕ, (advance next)^[k] (some seed) = some v := by
  simp only [onCycle, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, hi⟩
  · rintro ⟨i, hi⟩
    let p := minimalPeriod (advance next) (some seed)
    have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts (cyclic_iff.mp hs)
    refine ⟨⟨i % p, (Nat.mod_lt _ hp).trans_le minimalPeriod_le_card⟩, ?_⟩
    exact iterate_mod_minimalPeriod_eq.trans hi

def around (next : V → Option V) (seed v : V) : ℚ := if onCycle next seed v then 1 else 0

theorem around_seed {next : V → Option V} {seed : V} (hs : cyclic next seed = true) :
    around next seed seed = 1 := by
  simp [around, (onCycle_iff hs).mpr ⟨0, rfl⟩]

theorem around_conservation {next : V → Option V} {seed : V} (hs : cyclic next seed = true)
    (v : V) : incoming next (around next seed) v = around next seed v := by
  let f := advance next
  obtain ⟨n, hn, hp⟩ := mem_periodicPts.mp (cyclic_iff.mp hs)
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hperiod {u : V} (hu : onCycle next seed u = true) : some u ∈ periodicPts f := by
    obtain ⟨k, hk⟩ := (onCycle_iff hs).mp hu
    exact hk ▸ mk_mem_periodicPts hn (hp.apply_iterate k)
  by_cases hv : onCycle next seed v = true
  · obtain ⟨k, hk⟩ := (onCycle_iff hs).mp hv
    have hreach : f^[k+p+1] (some seed) = some v := by
      rw [Nat.add_assoc, iterate_add_apply, hp.eq]
      exact hk
    rw [iterate_succ_apply'] at hreach
    cases hu : f^[k+p] (some seed) with
    | none => rw [hu] at hreach; cases hreach
    | some u =>
      rw [hu] at hreach
      have hnext : next u = some v := hreach
      have hm := (onCycle_iff hs).mpr ⟨k+p, hu⟩
      unfold incoming
      rw [Finset.sum_eq_single u]
      · simp [hnext, around, hm, hv]
      · intro z _ hzu
        by_cases hz : onCycle next seed z = true
        · have hno : next z ≠ some v := fun he =>
            hzu (Option.some.inj ((bijOn_periodicPts f).injOn (hperiod hz) (hperiod hm)
              (he.trans hnext.symm)))
          simp [hno]
        · simp [around, hz]
      · simp
  · unfold incoming
    rw [Finset.sum_eq_zero]
    · simp [around, hv]
    · intro u _
      by_cases hu : onCycle next seed u = true
      · obtain ⟨k,hk⟩ := (onCycle_iff hs).mp hu
        have hno : next u ≠ some v := by
          intro he
          apply hv ((onCycle_iff hs).mpr ⟨k+1, ?_⟩)
          rw [iterate_succ_apply', hk]
          exact he
        simp [hno]
      · simp [around, hu]

end Kintali.QuotaSweep.Routing
