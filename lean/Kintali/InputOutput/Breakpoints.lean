module

public import Kintali.InputOutput.Tables
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.List.Sort
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-! # Rational intervals in the systematic-sampling construction of Kintali §1 -/

@[expose] public section

namespace Kintali.InputOutput.Lottery

/-- A rational offset and its weight. Adjacent equal breakpoints give weight zero. -/
abbrev Sample := ℚ × ℚ

def samples (lo : ℚ) : List ℚ → List Sample
  | [] => [((lo+1)/2, 1-lo)]
  | t :: ts => ((lo+t)/2, t-lo) :: samples t ts

def mean (s : List Sample) (f : ℚ → ℚ) := (s.map fun p => p.2 * f p.1).sum

@[simp] theorem mean_nil (f : ℚ → ℚ) : mean [] f = 0 := rfl
@[simp] theorem mean_cons (p : Sample) (s : List Sample) (f : ℚ → ℚ) :
    mean (p::s) f = p.2 * f p.1 + mean s f := by simp [mean]

theorem mean_congr (s : List Sample) {f g : ℚ → ℚ} (h : ∀ p ∈ s, f p.1 = g p.1) :
    mean s f = mean s g := by
  unfold mean
  congr 1
  exact List.map_congr_left fun p hp => by rw [h p hp]

theorem mean_const (lo c : ℚ) (ts : List ℚ) : mean (samples lo ts) (fun _ => c) = (1-lo)*c := by
  induction ts generalizing lo with
  | nil => simp [samples]
  | cons t ts ih => simp [samples, ih]; ring

theorem mean_add (s : List Sample) (f g : ℚ → ℚ) :
    mean s (fun u => f u + g u) = mean s f + mean s g := by
  simp only [mean, mul_add, List.sum_map_add]

theorem mean_sub (s : List Sample) (f g : ℚ → ℚ) :
    mean s (fun u => f u - g u) = mean s f - mean s g := by
  induction s with
  | nil => simp
  | cons p s ih => simp [ih]; ring

@[simp] theorem length_samples (lo : ℚ) (ts : List ℚ) : (samples lo ts).length = ts.length + 1 := by
  induction ts generalizing lo with
  | nil => rfl
  | cons t ts ih => simp [samples, ih]

/-- Breakpoints are sorted and lie in the remaining half-open interval. -/
structure Ordered (lo : ℚ) (ts : List ℚ) : Prop where
  lower : ∀ t ∈ ts, lo ≤ t
  upper : ∀ t ∈ ts, t < 1
  sorted : ts.Pairwise (· ≤ ·)

theorem Ordered.tail {lo t : ℚ} {ts : List ℚ} (h : Ordered lo (t :: ts)) : Ordered t ts :=
  ⟨(List.pairwise_cons.mp h.sorted).1, fun u hu => h.upper u (List.mem_cons_of_mem _ hu),
    (List.pairwise_cons.mp h.sorted).2⟩

theorem samples_bounds {lo : ℚ} {ts : List ℚ} (hlo : lo < 1) (h : Ordered lo ts)
    (p : Sample) (hp : p ∈ samples lo ts) : lo ≤ p.1 ∧ p.1 < 1 ∧ 0 ≤ p.2 := by
  induction ts generalizing lo with
  | nil =>
    simp [samples] at hp
    subst p
    dsimp
    exact ⟨by linarith, by linarith, by linarith⟩
  | cons t ts ih =>
    have hlt := h.upper t (by simp)
    have hle := h.lower t (by simp)
    rcases List.mem_cons.mp hp with rfl | tail
    · dsimp
      exact ⟨by linarith, by linarith, by linarith⟩
    · obtain ⟨hu, rest⟩ := ih hlt h.tail tail
      exact ⟨hle.trans hu, rest⟩

def step (t u : ℚ) : ℚ := if u < t then 1 else 0

private theorem mean_step_below {lo t : ℚ} {ts : List ℚ} (hlo : lo < 1) (h : Ordered lo ts)
    (ht : t ≤ lo) : mean (samples lo ts) (step t) = 0 := by
  calc
    _ = mean (samples lo ts) (fun _ => 0) := mean_congr _ fun p hp =>
      ite_eq_right (not_lt.mpr (ht.trans (samples_bounds hlo h p hp).1))
    _ = 0 := by simp [mean_const]

theorem mean_step {lo t : ℚ} {ts : List ℚ} (hlo : lo < 1) (h : Ordered lo ts)
    (atCut : t = lo ∨ t ∈ ts) : mean (samples lo ts) (step t) = t-lo := by
  induction ts generalizing lo with
  | nil =>
    have ht : t = lo := by simpa using atCut
    simp [ht, mean_step_below hlo h le_rfl]
  | cons b ts ih =>
    have hb := h.upper b (by simp)
    have hle := h.lower b (by simp)
    rcases atCut with rfl | incl
    · rw [mean_step_below hlo h le_rfl, sub_self]
    · rcases List.mem_cons.mp incl with rfl | later
      · simp only [samples, mean_cons, mean_step_below hb h.tail le_rfl, add_zero, step]
        split <;> rename_i ht <;> linarith
      · have hbt : b ≤ t := h.tail.lower t later
        simp only [samples, mean_cons, ih hb h.tail (Or.inr later), step]
        split <;> rename_i ht <;> linarith

/-- Prefix count at offset u. Points lie at u plus successive integers, and
a point on the right endpoint of a target interval belongs to the next target. -/
def count (v u : ℚ) : ℤ := ⌈v-u⌉

theorem count_eq (v u : ℚ) (hu : 0 ≤ u) (hu' : u < 1) :
    (count v u : ℚ) = (⌊v⌋ : ℤ) + step (Int.fract v) u := by
  have eq := Int.floor_add_fract v
  have hlo := Int.fract_nonneg v
  have hhi := Int.fract_lt_one v
  by_cases h : u < Int.fract v
  · have hc : count v u = ⌊v⌋+1 := by
      apply Int.ceil_eq_iff.mpr
      push_cast
      constructor <;> linarith
    simp [hc, step, h]
  · have hc : count v u = ⌊v⌋ := by
      apply Int.ceil_eq_iff.mpr
      constructor <;> linarith
    simp [hc, step, h]

theorem mean_count (ts : List ℚ) (h : Ordered 0 ts) (v : ℚ) (hcut : Int.fract v = 0 ∨ Int.fract v ∈ ts) :
    mean (samples 0 ts) (fun u => (count v u : ℚ)) = v := by
  calc
    _ = mean (samples 0 ts) (fun u => (⌊v⌋ : ℤ) + step (Int.fract v) u) :=
      mean_congr _ fun p hp =>
        let b := samples_bounds (by decide : (0 : ℚ) < 1) h p hp
        count_eq v p.1 b.1 b.2.1
    _ = _ := by
      rw [mean_add _ (fun _ => (⌊v⌋ : ℚ)) (step _), mean_const, mean_step (by decide) h hcut]
      simp

end Kintali.InputOutput.Lottery
