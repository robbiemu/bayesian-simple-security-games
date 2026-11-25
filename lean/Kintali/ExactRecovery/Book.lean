module

public import Kintali.ExactRecovery.Contact
public import Kintali.QuotaSweep.Choices
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith

/-! # The expanded ordinal book

Real buyers and the elementary private buyers have separate outside records;
each site has a vacancy. An ordinary record is either a real grid bid or the
unique bid of an elementary private buyer. Ranking by a finite initial segment
of lexicographic keys realizes the stated deterministic preferences.
-/

open scoped BigOperators
open Kintali.QuotaSweep

@[expose] public section

namespace Kintali.ExactRecovery.Expanded

abbrev Buyer (I J : Type*) (G : ℕ) := I ⊕ (J × Fin G)
abbrev Bid (I J : Type*) (G : ℕ) := (I × (J × Quote G)) ⊕ (J × Fin G)
abbrev V (I J : Type*) (G : ℕ) := Vertex (Buyer I J G) J
abbrev R (I J : Type*) (G : ℕ) := Record (Buyer I J G) J (Bid I J G)

variable {I J : Type*} {G : ℕ}

def buyer : Bid I J G → Buyer I J G
  | .inl (i,_) => .inl i
  | .inr jk => .inr jk

def site : Bid I J G → J
  | .inl (_,j,_) => j
  | .inr (j,_) => j

abbrev realBid (i : I) (j : J) (z : Quote G) : Bid I J G := .inl (i,j,z)
abbrev privateBid (j : J) (k : Fin G) : Bid I J G := .inr (j,k)

variable [DecidableEq I] [DecidableEq J]

def ends : R I J G → Finset (V I J G)
  | .inl e => {.inl (buyer e), .inr (site e)}
  | .inr v => {v}

/-- Smaller values are preferred. At the site a real quote z has level
−2z and private bid k has level −(2k+1); slack has primary key ⊤. -/
def primary (g : Game I J) (v : V I J G) : R I J G → WithTop ℚ
  | .inr _ => ⊤
  | .inl (.inl (i,j,z)) => match v with
    | .inl _ => ↑(Holdings.quoteCost g i j z)
    | .inr _ => ↑(-(2 * (z.val : ℚ)))
  | .inl (.inr (_,k)) => match v with
    | .inl _ => ↑(0 : ℚ)
    | .inr _ => ↑(-(2 * (k.val : ℚ) + 1))

/-- At equal real costs, buyers use site index and quote. At equal real
quotes sites use buyer index. The final record code only orders nonincident
records or resolves equal keys when arbitrary index maps are supplied. -/
def tie (indexI : I → ℕ) (indexJ : J → ℕ) (v : V I J G) : R I J G → ℕ × ℕ
  | .inl (.inl (i,j,z)) => match v with
    | .inl _ => (indexJ j, z.val)
    | .inr _ => (indexI i, 0)
  | _ => (0,0)

abbrev Key := WithTop ℚ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

variable [Encodable I] [Encodable J]

def key (g : Game I J) (indexI : I → ℕ) (indexJ : J → ℕ) (v : V I J G) (e : R I J G) : Key :=
  toLex (primary g v e, toLex ((tie indexI indexJ v e).1,
    toLex ((tie indexI indexJ v e).2, Encodable.encode e)))

variable [Fintype I] [Fintype J]

/-- An ordinal realized by counting the records with smaller keys. -/
def ordinalRank {T K : Type*} [Fintype T] [LinearOrder K] (f : T → K) (e : T) : ℕ :=
  (Finset.univ.filter (fun a => f a < f e)).card

theorem ordinalRank_strict {T K : Type*} [Fintype T] [LinearOrder K] (f : T → K) {e b : T}
    (better : f e < f b) : ordinalRank f e < ordinalRank f b := by
  let cut (x : T) := Finset.univ.filter (fun y => f y < f x)
  apply Finset.card_lt_card (s := cut e) (t := cut b)
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hy).2).trans better⟩
  · intro equal
    have inside : e ∈ cut b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, better⟩
    rw [← equal] at inside
    exact (lt_irrefl _) (Finset.mem_filter.mp inside).2

theorem ordinalRank_lt_iff {T K : Type*} [Fintype T] [LinearOrder K] (f : T → K) (e b : T) :
    ordinalRank f e < ordinalRank f b ↔ f e < f b := by
  refine ⟨fun lt => ?_, ordinalRank_strict f⟩
  rcases lt_trichotomy (f e) (f b) with less | eq | greater
  · exact less
  · have same : ordinalRank f e = ordinalRank f b := by simp [ordinalRank, eq]
    exact (lt.ne same).elim
  · exact (lt_asymm lt (ordinalRank_strict f greater)).elim

def rank (g : Game I J) (indexI : I → ℕ) (indexJ : J → ℕ) (v : V I J G) (e : R I J G) : ℕ :=
  ordinalRank (key g indexI indexJ v) e

omit [DecidableEq I] [DecidableEq J] in
theorem rank_strict (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (v : V I J G)
    {e f : R I J G} (better : key g bi si v e < key g bi si v f) :
    rank g bi si v e < rank g bi si v f := ordinalRank_strict _ better

omit [DecidableEq I] [DecidableEq J] in
theorem rank_lt_of_primary (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (v : V I J G)
    {e f : R I J G} (better : primary g v e < primary g v f) :
    rank g bi si v e < rank g bi si v f :=
  rank_strict g bi si v (Prod.Lex.lt_iff.mpr (Or.inl better))

omit [DecidableEq I] [DecidableEq J] [Fintype I] [Fintype J] in
theorem key_injective (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (v : V I J G) :
    Function.Injective (key g bi si v) := by
  intro e f equal
  exact Encodable.encode_injective <| congrArg
    (fun k : Key => (ofLex (ofLex (ofLex k).2).2).2) equal

omit [DecidableEq I] [DecidableEq J] in
theorem ordinary_before_slack (g : Game I J) (bi : I → ℕ) (si : J → ℕ)
    (v w : V I J G) (e : Bid I J G) : rank g bi si v (bid e) < rank g bi si v (.inr w) := by
  apply rank_lt_of_primary
  rcases e with ⟨i,j,z⟩ | ⟨j,k⟩ <;> cases v <;> exact WithTop.coe_lt_top _

def market (g : Game I J) (bi : I → ℕ) (si : J → ℕ) : Market (V I J G) (R I J G) where
  ends := ends
  rank := rank g bi si
  degree := by rintro (e | v) <;> simp [ends]
  rank_injective := by
    intro v e f _ _ equal
    apply key_injective g bi si v
    rcases lt_trichotomy (key g bi si v e) (key g bi si v f) with less | same | greater
    · exact ((rank_strict g bi si v less).ne equal).elim
    · exact same
    · exact ((rank_strict g bi si v greater).ne equal.symm).elim
  slack_last := by
    rintro (e | u) degree v inc f hf different
    · simp [ends] at degree
    · have vu : v = u := by simpa [ends] using inc
      subst v
      rcases f with f | w
      · exact ordinary_before_slack g bi si u u f
      · exact (different (congrArg Sum.inr (Finset.mem_singleton.mp hf).symm)).elim

def permitted (g : Game I J) (redirect : I → J) (optional : I → J → Quote G → Bool) :
    Bid I J G → Bool
  | .inl (i,j,z) => decide (0 < g.gain j ∧ Holdings.quoteCost g i j z ≤ Holdings.outsideCost g redirect i) &&
      (decide (z = cap G) || optional i j z)
  | .inr (j,_) => decide (0 < g.gain j)

def book (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (redirect : I → J)
    (optional : I → J → Quote G → Bool) : Book (Buyer I J G) J (Bid I J G) := by
  letI : LinearOrder (R I J G) := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  exact
    { market := market g bi si
      buyer := buyer
      site := site
      ends_bid := fun _ => rfl
      ends_outside := fun _ => rfl
      ends_vacancy := fun _ => rfl
      records := Finset.univ.sort
      complete := fun e => by simp
      retained := Finset.univ.filter (fun e => permitted g redirect optional e) }

theorem retained_real (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (redirect : I → J)
    (optional : I → J → Quote G → Bool) (i : I) (j : J) (z : Quote G) :
    realBid i j z ∈ (book g bi si redirect optional).retained ↔
      Holdings.Eligible g redirect i j z ∧ (z = cap G ∨ optional i j z = true) := by
  change realBid i j z ∈ Finset.univ.filter _ ↔ _
  simp [permitted, Holdings.Eligible, and_assoc]

theorem retained_private (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (redirect : I → J)
    (optional : I → J → Quote G → Bool) (j : J) (k : Fin G) :
    privateBid j k ∈ (book g bi si redirect optional).retained ↔ 0 < g.gain j := by
  change privateBid j k ∈ Finset.univ.filter _ ↔ _
  simp [permitted]

end Kintali.ExactRecovery.Expanded
