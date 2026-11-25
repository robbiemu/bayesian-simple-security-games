module

public import Kintali.QuotaSweep.Choices
import Mathlib.Tactic.Linarith

/-!
# Counted scans over the sparse record inventory

All scans return their value and a charge. Visiting a list cell costs one.
A caller supplies charges for the predicate, comparison, or table-entry calculation.
-/

@[expose] public section
namespace Kintali.QuotaSweep.Work

variable {α β : Type*}

def tabulate (f : α → β × ℕ) : List α → List (α × β) × ℕ
  | [] => ([],0)
  | a::as =>
    let h := f a
    let rest := tabulate f as
    ((a,h.1) :: rest.1, h.2+rest.2+1)

theorem tabulate_value (f : α → β × ℕ) (l : List α) :
    (tabulate f l).1 = l.map fun a => (a,(f a).1) := by
  induction l <;> simp_all [tabulate]

theorem tabulate_work (f : α → β × ℕ) (n : ℕ) (h : ∀ a, (f a).2 ≤ n) (l : List α) :
    (tabulate f l).2 ≤ l.length*(n+1) := by
  induction l with
  | nil => simp [tabulate]
  | cons a l ih => simp only [tabulate, List.length_cons, Nat.add_mul, Nat.one_mul]; grind

def select (p : α → Bool × ℕ) : List α → List α × ℕ
  | [] => ([],0)
  | a::as =>
    let h := p a
    let rest := select p as
    (if h.1 then a :: rest.1 else rest.1, h.2+rest.2+1)

theorem select_value (p : α → Bool × ℕ) (l : List α) :
    (select p l).1 = l.filter fun a => (p a).1 := by
  induction l <;> simp_all [select, List.filter_cons]

theorem select_work (p : α → Bool × ℕ) (n : ℕ) (h : ∀ a, (p a).2 ≤ n) (l : List α) :
    (select p l).2 ≤ l.length*(n+1) := by
  induction l with
  | nil => simp [select]
  | cons a l ih => simp only [select, List.length_cons, Nat.add_mul, Nat.one_mul]; grind

def find (p : α → Bool × ℕ) : List α → Option α × ℕ
  | [] => (none,0)
  | a::as =>
    let h := p a
    if h.1 then (some a,h.2+1)
    else
      let rest := find p as
      (rest.1,h.2+rest.2+1)

theorem find_value (p : α → Bool × ℕ) (l : List α) :
    (find p l).1 = l.find? fun a => (p a).1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : (p a).1 = true <;> simp [find, ha, ih]

theorem find_work (p : α → Bool × ℕ) (n : ℕ) (h : ∀ a, (p a).2 ≤ n) (l : List α) :
    (find p l).2 ≤ l.length*(n+1) := by
  induction l with
  | nil => simp [find]
  | cons a l ih =>
    simp only [find, List.length_cons, Nat.add_mul, Nat.one_mul]
    split <;> grind

def extremum (r : α → α → Prop) [DecidableRel r] (compareCharge : ℕ) :
    List α → Option α → Option α × ℕ
  | [], acc => (acc,0)
  | a::as, none =>
    let rest := extremum r compareCharge as (some a)
    (rest.1,rest.2+1)
  | a::as, some b =>
    let rest := extremum r compareCharge as (if r a b then some a else some b)
    (rest.1,rest.2+compareCharge+1)

theorem extremum_value (r : α → α → Prop) [DecidableRel r] (c : ℕ) (l : List α) (acc : Option α) :
    (extremum r c l acc).1 = l.foldl (List.argAux r) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih => cases acc <;> simp [extremum, List.argAux, ih]

theorem extremum_work (r : α → α → Prop) [DecidableRel r] (c : ℕ) (l : List α) (acc : Option α) :
    (extremum r c l acc).2 ≤ l.length*(c+1) := by
  induction l generalizing acc with
  | nil => simp [extremum]
  | cons a l ih =>
    cases acc <;> simp only [extremum, List.length_cons, Nat.add_mul, Nat.one_mul] <;> grind

def search [DecidableEq α] (key : α) (fallback : β) : List (α × β) → β × ℕ
  | [] => (fallback,0)
  | (a,b)::as =>
    if key = a then (b,1)
    else
      let rest := search key fallback as
      (rest.1,rest.2+1)

theorem search_value [DecidableEq α] (key : α) (fallback : β) (l : List (α × β)) :
    (search key fallback l).1 = (l.lookup key).getD fallback := by
  induction l with
  | nil => rfl
  | cons ab l ih =>
    obtain ⟨a,b⟩ := ab
    by_cases ha : key = a
    · simp [search, List.lookup, ha]
    · have ne : (key == a) = false := beq_eq_false_iff_ne.mpr ha
      simp [search, List.lookup, ha, ih, ne]

theorem search_work [DecidableEq α] (key : α) (fallback : β) (l : List (α × β)) :
    (search key fallback l).2 ≤ l.length := by
  induction l with
  | nil => simp [search]
  | cons ab l ih => rcases ab with ⟨a,b⟩; simp only [search, List.length_cons]; split <;> omega

end Kintali.QuotaSweep.Work
