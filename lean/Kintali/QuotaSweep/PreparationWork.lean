module

public import Kintali.QuotaSweep.KeyTable
public import Kintali.QuotaSweep.KeyWidth

/-! # Exact key-evaluation and comparison counts in ordinal preprocessing -/

@[expose] public section
namespace Kintali.ExactRecovery.Sparse

open Kintali.QuotaSweep

variable {T V X : Type*}

def measureKeys (f : T → X) : List T → List (T × X) × ℕ
  | [] => ([],0)
  | t::ts =>
    let rest := measureKeys f ts
    ((t,f t)::rest.1,rest.2+1)

private theorem measureKeys_spec (f : T → X) (l : List T) :
    measureKeys f l = (keyed l f,l.length) := by
  induction l <;> simp_all [measureKeys,keyed]

def countBelow [LinearOrder X] (q : X) : List (T × X) → ℕ × ℕ
  | [] => (0,0)
  | e::es =>
    let more := countBelow q es
    ((if e.2 < q then 1 else 0)+more.1,more.2+1)

private theorem countBelow_spec [LinearOrder X] (q : X) (l : List (T × X)) :
    countBelow q l = (l.countP (fun e => decide (e.2 < q)),l.length) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases h : e.2 < q <;> simp [countBelow,ih,h,Nat.add_comm]

def countRanks [LinearOrder X] (row : List (T × X)) :
    List (T × X) → List (T × ℕ) × ℕ
  | [] => ([],0)
  | e::es =>
    let q := countBelow e.2 row
    let rest := countRanks row es
    ((e.1,q.1)::rest.1,q.2+rest.2)

private theorem countRanks_spec [LinearOrder X] (row l : List (T × X)) :
    countRanks row l = (l.map (fun a => (a.1,row.countP (fun b => decide (b.2 < a.2)))),
      l.length*row.length) := by
  induction l <;> simp_all [countRanks,countBelow_spec,Nat.add_mul,Nat.add_comm]

/-- The two counters track calls of the key function and comparisons of
stored keys. The table itself contains the same rank naturals used by the sweep. -/
def countedKeyTable [LinearOrder X] (records : List T) (f : V → T → X) :
    List V → List (V × List (T × ℕ)) × (ℕ × ℕ)
  | [] => ([],(0,0))
  | v::vs =>
    let keys := measureKeys (f v) records
    let row := countRanks keys.1 keys.1
    let rest := countedKeyTable records f vs
    ((v,row.1)::rest.1,(keys.2+rest.2.1,row.2+rest.2.2))

theorem countedKeyTable_spec [LinearOrder X] (records : List T) (f : V → T → X) (vs : List V) :
    countedKeyTable records f vs =
      (vs.map (fun v => (v,ordinals (keyed records (f v)))),
        (vs.length*records.length,vs.length*(records.length*records.length))) := by
  induction vs with
  | nil => simp [countedKeyTable]
  | cons v vs ih =>
    simp [countedKeyTable,measureKeys_spec,countRanks_spec,ordinals,keyed,ih,Nat.add_mul,Nat.add_comm]

variable {I J A H : Type*} {G : ℕ}
variable [Fintype I] [Fintype J] [Fintype A] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq H]
variable [Encodable I] [Encodable J] [Encodable A] [Encodable H]

theorem key_preparation (g : Game I J) (bi : I → ℕ) (si : J → ℕ) (L : Layout I J G A H) :
    let K := book g bi si L
    let r := K.records.length
    let v := K.rankVertices.length
    countedKeyTable K.records (fun i e => Expanded.key g bi si (L.embedVertex i) (L.embedRecord e))
      K.rankVertices = (keyedTable g bi si L,(v*r,v*(r*r))) :=
  countedKeyTable_spec ..

end Kintali.ExactRecovery.Sparse
