module

public import Kintali.QuotaSweep.KeyWidth
public import Kintali.TrialWork.Arithmetic

/-! # Addressed computation of the sparse sum and dependent-pair identifiers -/

@[expose] public section
namespace Kintali.QuotaSweep.StoredLookup

open Kintali.ExactRecovery
open StochasticGames.BinarySize StochasticGames.CompilerRun

variable {T U : Type}

structure KeyBound (f : T → Run ℕ) (slots bits : ℕ) : Prop where
  work : ∀ t, (f t).Bound slots bits
  size : ∀ t, (f t).value.size ≤ bits

theorem KeyBound.weaken {f : T → Run ℕ} {a b c d : ℕ} (h : KeyBound f a b)
    (ha : a ≤ c) (hb : b ≤ d) : KeyBound f c d :=
  ⟨fun t => (h.work t).weaken ha hb,fun t => (h.size t).trans hb⟩

def finKey {n : ℕ} (i : Fin n) : Run ℕ := step i.val.size i.val

@[simp] theorem finKey_value {n : ℕ} (i : Fin n) : (finKey i).value = Encodable.encode i := rfl

theorem finKey_bound {n w : ℕ} (h : n.size ≤ w) : KeyBound (@finKey n) 1 w :=
  ⟨fun i => (bound_step _ _).weaken le_rfl ((Nat.size_le_size i.isLt.le).trans h),
    fun i => (Nat.size_le_size i.isLt.le).trans h⟩

def pairKey (a b : ℕ) : Run ℕ := do
  let left ← step (max a.size b.size) (decide (a < b))
  if left then
    let s ← natMul b b
    natAdd s a
  else
    let s ← natMul a a
    let t ← natAdd s a
    natAdd t b

@[simp] theorem pairKey_value (a b : ℕ) : (pairKey a b).value = Nat.pair a b := by
  by_cases h : a < b <;> simp [pairKey,Nat.pair,h,natAdd,natMul]

private theorem plus_size (a b : ℕ) {w : ℕ} (ha : a.size ≤ w) (hb : b.size ≤ w) :
    (a+b).size ≤ w+1 := by
  apply Nat.size_le.mpr
  have := Nat.size_le.mp ha
  have := Nat.size_le.mp hb
  rw [pow_succ]; omega

theorem pairKey_work (a b : ℕ) {w : ℕ} (ha : a.size ≤ w) (hb : b.size ≤ w) :
    (pairKey a b).Bound 4 (2*w+2) := by
  have atwo := (size_mul_le a a).trans (Nat.add_le_add ha ha)
  have btwo := (size_mul_le b b).trans (Nat.add_le_add hb hb)
  have act : (a*a+a).size ≤ 2*w+1 := plus_size _ _ (by omega) (by omega)
  by_cases ag : a < b <;>
    simp [pairKey,ag,Run.Bound,natMul,natAdd] <;> omega

def groupKey {m G : ℕ} (D : Fin m → QuotePartition G) (h : Sparse.IntervalGroup D) : Run ℕ := do
  let j ← finKey h.1
  let i ← finKey h.2
  pairKey j i

@[simp] theorem groupKey_value {m G : ℕ} (D : Fin m → QuotePartition G) (h : Sparse.IntervalGroup D) :
    (groupKey D h).value = Encodable.encode h := by rcases h with ⟨j,i⟩; simp [groupKey]

theorem groupKey_bound {m G w : ℕ} (D : Fin m → QuotePartition G) (hm : m.size ≤ w)
    (hg : ∀ j, (D j).groups.size ≤ w) : KeyBound (groupKey D) 6 (2*w+2) := by
  constructor
  · rintro ⟨j,h⟩
    have a := (finKey_bound hm).work j
    have b := (finKey_bound (hg j)).work h
    have p := pairKey_work _ _ ((finKey_bound hm).size j) ((finKey_bound (hg j)).size h)
    simp only [groupKey,Run.Bound,Run.bind_slots,Run.bind_width] at *
    omega
  · rintro ⟨j,h⟩
    rw [groupKey_value,Encodable.encode_sigma_val]
    apply Nat.size_le.mpr
    have hj := Nat.size_le.mp ((finKey_bound hm).size j)
    have hh := Nat.size_le.mp ((finKey_bound (hg j)).size h)
    have lt : max (Encodable.encode j) (Encodable.encode h) < 2^w := max_lt hj hh
    calc
      Nat.pair (Encodable.encode j) (Encodable.encode h) < (max _ _+1)^2 := Nat.pair_lt_max_add_one_sq ..
      _ ≤ (2^w)^2 := Nat.pow_le_pow_left (by omega) _
      _ = 2^(2*w) := by rw [← pow_mul,Nat.mul_comm w 2]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

def sumKey (f : T → Run ℕ) (g : U → Run ℕ) : T ⊕ U → Run ℕ
  | .inl t => do
    let x ← f t
    natMul 2 x
  | .inr t => do
    let x ← g t
    let y ← natMul 2 x
    natAdd y 1

theorem sumKey_value [Encodable T] [Encodable U] (f : T → Run ℕ) (g : U → Run ℕ)
    (hf : ∀ t, (f t).value = Encodable.encode t) (hg : ∀ t, (g t).value = Encodable.encode t)
    (s : T ⊕ U) : (sumKey f g s).value = Encodable.encode s := by
  rcases s with t|t <;> simp [sumKey,hf,hg,natMul,natAdd]

theorem sumKey_bound {f : T → Run ℕ} {g : U → Run ℕ} {c w : ℕ} (hf : KeyBound f c w)
    (hg : KeyBound g c w) : KeyBound (sumKey f g) (c+2) (w+2) := by
  have two : (2 : ℕ).size = 2 := by decide
  have double (n : ℕ) (hn : n.size ≤ w) : (2*n+1).size ≤ w+1 := by
    apply Nat.size_le.mpr
    have := Nat.size_le.mp hn; rw [pow_succ]; omega
  constructor
  · rintro (t|t)
    · obtain ⟨a,b⟩ := hf.work t
      have s := hf.size t
      simp [sumKey,natMul,Run.Bound]
      omega
    · obtain ⟨a,b⟩ := hg.work t
      have s := hg.size t
      have d := (Nat.size_le_size (Nat.le_succ (2*(g t).value))).trans (double _ s)
      simp [sumKey,natMul,natAdd,Run.Bound]
      omega
  · rintro (t|t)
    · exact ((Nat.size_le_size (Nat.le_succ (2*(f t).value))).trans (double _ (hf.size t))).trans (by omega)
    · exact (double _ (hg.size t)).trans (by omega)

/-- Exact identifier used by `Book.Stored.encodedRead` for a selected record. -/
def recordKey {k m a G : ℕ} (D : Fin m → QuotePartition G) :
    Sparse.R (Fin k) (Fin m) (Fin a) (Sparse.IntervalGroup D) → Run ℕ :=
  let group := groupKey D
  let buyer := sumKey finKey group
  let bid := sumKey finKey group
  sumKey bid (sumKey buyer finKey)

theorem recordKey_value {k m a G : ℕ} (D : Fin m → QuotePartition G)
    (e : Sparse.R (Fin k) (Fin m) (Fin a) (Sparse.IntervalGroup D)) :
    (recordKey D e).value = Encodable.encode e :=
  sumKey_value _ _
    (sumKey_value _ _ finKey_value (groupKey_value D))
    (sumKey_value _ _ (sumKey_value _ _ finKey_value (groupKey_value D)) finKey_value) e

theorem recordKey_bound {k m a G w : ℕ} (D : Fin m → QuotePartition G)
    (hk : k.size ≤ w) (hm : m.size ≤ w) (ha : a.size ≤ w) (hg : ∀ j, (D j).groups.size ≤ w) :
    KeyBound (recordKey (k := k) (a := a) D) 12 (2*w+8) := by
  have g := groupKey_bound D hm hg
  have buyer := sumKey_bound ((finKey_bound hk).weaken (show 1 ≤ 6 by decide) (show w ≤ 2*w+2 by omega)) g
  have bid := sumKey_bound ((finKey_bound ha).weaken (show 1 ≤ 6 by decide) (show w ≤ 2*w+2 by omega)) g
  have v := sumKey_bound buyer ((finKey_bound hm).weaken (show 1 ≤ 6+2 by decide) (show w ≤ 2*w+2+2 by omega))
  exact sumKey_bound (bid.weaken (by omega) (by omega)) v

def leftCode (r : Run ℕ) : Run ℕ := do
  let n ← r
  natMul 2 n

def rightCode (r : Run ℕ) : Run ℕ := do
  let n ← r
  let z ← natMul 2 n
  natAdd z 1

/-- Give the compiler saturated calls for the finite-coordinate projections.
The numeric identifier uses the two coordinates themselves. The enclosing
dimension and partition are needed only as types. -/
@[inline] def recordCode {k m a G : ℕ} (D : Fin m → QuotePartition G) :
    Sparse.R (Fin k) (Fin m) (Fin a) (Sparse.IntervalGroup D) → Run ℕ
  | .inl (.inl e) => leftCode (leftCode (finKey e))
  | .inl (.inr h) => leftCode (rightCode (groupKey D h))
  | .inr (.inl (.inl i)) => rightCode (leftCode (leftCode (finKey i)))
  | .inr (.inl (.inr h)) => rightCode (leftCode (rightCode (groupKey D h)))
  | .inr (.inr j) => rightCode (rightCode (finKey j))

@[csimp] theorem recordKey_compiled : @recordKey = @recordCode := by
  funext k m a G D e
  rcases e with ((e|h)|(i|h)|j) <;> rfl

end Kintali.QuotaSweep.StoredLookup
