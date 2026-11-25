module

public import Kintali.QuotaSweep.EncodedKeyRun

/-! # Addressed encoding of expanded records used by the final ordinal tie -/

@[expose] public section
namespace Kintali.QuotaSweep.StoredLookup

open Kintali.ExactRecovery
open StochasticGames.CompilerRun StochasticGames.BinarySize

variable {T U : Type}

def productKey (f : T → Run ℕ) (g : U → Run ℕ) (p : T × U) : Run ℕ := do
  let x ← f p.1
  let y ← g p.2
  pairKey x y

theorem productKey_value [Encodable T] [Encodable U] (f : T → Run ℕ) (g : U → Run ℕ)
    (hf : ∀ t, (f t).value = Encodable.encode t) (hg : ∀ t, (g t).value = Encodable.encode t)
    (p : T × U) : (productKey f g p).value = Encodable.encode p := by
  obtain ⟨t,u⟩ := p
  simp [productKey,hf,hg]

theorem productKey_bound {f : T → Run ℕ} {g : U → Run ℕ} {c d w : ℕ} (hf : KeyBound f c w)
    (hg : KeyBound g d w) : KeyBound (productKey f g) (c+(d+4)) (2*w+2) := by
  constructor
  · rintro ⟨t,u⟩
    exact bound_bind ((hf.work t).weaken le_rfl (by omega))
      (bound_bind ((hg.work u).weaken le_rfl (by omega)) (pairKey_work _ _ (hf.size t) (hg.size u)))
  · rintro ⟨t,u⟩
    simp only [productKey,Run.bind_value,pairKey_value]
    apply Nat.size_le.mpr
    have ht := Nat.size_le.mp (hf.size t)
    have hu := Nat.size_le.mp (hg.size u)
    have small := max_lt ht hu
    calc
      Nat.pair (f t).value (g u).value < (max _ _+1)^2 := Nat.pair_lt_max_add_one_sq ..
      _ ≤ (2^w)^2 := Nat.pow_le_pow_left (by omega) _
      _ = 2^(2*w) := by rw [← pow_mul,Nat.mul_comm w 2]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

def expandedKey {k m G : ℕ} : Expanded.R (Fin k) (Fin m) G → Run ℕ :=
  let gap := productKey finKey finKey
  let siteQuote := productKey finKey finKey
  let real := productKey finKey siteQuote
  let bid := sumKey real gap
  let buyer := sumKey finKey gap
  sumKey bid (sumKey buyer finKey)

theorem expandedKey_value {k m G : ℕ} (e : Expanded.R (Fin k) (Fin m) G) :
    (expandedKey e).value = Encodable.encode e :=
  sumKey_value _ _
    (sumKey_value _ _ (productKey_value _ _ finKey_value (productKey_value _ _ finKey_value finKey_value))
      (productKey_value _ _ finKey_value finKey_value))
    (sumKey_value _ _ (sumKey_value _ _ finKey_value (productKey_value _ _ finKey_value finKey_value)) finKey_value) e

theorem expandedKey_bound {k m G w : ℕ} (hk : k.size ≤ w) (hm : m.size ≤ w) (hG : G.size ≤ w)
    (hq : (G+1).size ≤ w) : KeyBound (@expandedKey k m G) 15 (4*w+10) := by
  have gap := productKey_bound (finKey_bound hm) (finKey_bound hG)
  have qs := productKey_bound (finKey_bound hm) (finKey_bound hq)
  have i := (finKey_bound hk).weaken (show 1 ≤ 1 by decide) (show w ≤ 2*w+2 by omega)
  have real := productKey_bound i qs
  have bid := sumKey_bound real (gap.weaken (by decide) (by omega))
  have buyer := sumKey_bound (i.weaken (by decide : 1 ≤ 6) le_rfl) gap
  have v := sumKey_bound buyer ((finKey_bound hm).weaken (by decide) (by omega))
  exact (sumKey_bound bid (v.weaken (by decide) (by omega))).weaken (by decide) (by omega)

end Kintali.QuotaSweep.StoredLookup
