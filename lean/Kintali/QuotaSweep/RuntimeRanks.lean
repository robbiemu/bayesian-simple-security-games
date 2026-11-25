module

public import Kintali.QuotaSweep.RankedContact
public import Kintali.QuotaSweep.EncodedKeyRun

/-! Equality of a sparse label uses the stored finite coordinates.
The range appears in the label's type and is never enumerated by comparison. -/

@[expose] public section
namespace Kintali.QuotaSweep.RankRun

open ExactRecovery StochasticGames.CompilerRun

def labelNumber {n m G : ℕ} {D : Fin m → QuotePartition G} : Fin n ⊕ Sparse.IntervalGroup D → ℕ
  | .inl i => 2*i.val
  | .inr h => 2*Nat.pair h.1.val h.2.val+1

theorem labelNumber_eq {n m G : ℕ} {D : Fin m → QuotePartition G} (x : Fin n ⊕ Sparse.IntervalGroup D) :
    labelNumber x = Encodable.encode x := by
  cases x with
  | inl i => rfl
  | inr h => cases h; rfl

@[inline] def labelEq {n m G : ℕ} {D : Fin m → QuotePartition G} (x y : Fin n ⊕ Sparse.IntervalGroup D) :
    Decidable (x=y) :=
  decidable_of_iff (labelNumber x = labelNumber y) (by
    rw [labelNumber_eq,labelNumber_eq]
    exact ⟨fun h => Encodable.encode_injective h,congrArg Encodable.encode⟩)

@[inline] def coordinateEq {n : ℕ} (x y : Fin n) : Decidable (x=y) :=
  decidable_of_iff (x.val=y.val) ⟨Fin.ext,congrArg Fin.val⟩

structure Equality (T : Type) where
  decide : DecidableEq T

variable {B S E : Type} [dB : DecidableEq B] [dS : DecidableEq S] [dE : DecidableEq E]

theorem readRanks_switch (b : DecidableEq B) (s : DecidableEq S) (e : DecidableEq E)
    (table : Book.RankTable B S E) :
    @Book.readRanks B S E b s e table = @Book.readRanks B S E dB dS dE table := by
  have hb : b=dB := Subsingleton.elim ..
  have hs : s=dS := Subsingleton.elim ..
  have he : e=dE := Subsingleton.elim ..
  subst b; subst s; subst e; rfl

/-- Install the completed rank matrix with explicit comparison callbacks for
its row and column lookup. -/
@[noinline,nospecialize] def attachIndexed (K : Book B S E) (t : Run (Book.RankTable B S E))
    (ok : t.value = K.rankTable) (b : Equality B) (s : Equality S) (e : Equality E) : Run (Book B S E) :=
  let read := @Book.readRanks B S E b.decide s.decide e.decide t.value
  let hr : read = K.market.rank := by
    apply (readRanks_switch (dB:=dB) (dS:=dS) (dE:=dE) b.decide s.decide e.decide t.value).trans
    rw [ok]
    exact K.readRanks_eq
  let newBook : Book B S E := { K with market :=
    { K.market with rank := read
                    rank_injective := by rw [hr]; exact K.market.rank_injective
                    slack_last := by rw [hr]; exact K.market.slack_last } }
  ⟨newBook,t.work.seq (StochasticGames.CompilerRun.Work.one 0)⟩

theorem attachIndexed_eq (K : Book B S E) (t : Run (Book.RankTable B S E))
    (ok : t.value = K.rankTable) (b : Equality B) (s : Equality S) (e : Equality E) :
    attachIndexed K t ok b s e = attach K t ok := by
  obtain ⟨bb⟩ := b
  obtain ⟨ss⟩ := s
  obtain ⟨ee⟩ := e
  have hb : bb=dB := Subsingleton.elim ..
  have hs : ss=dS := Subsingleton.elim ..
  have he : ee=dE := Subsingleton.elim ..
  subst bb; subst ss; subst ee; rfl

/-- Pass the finite enumerations and numeric equality functions through to
the live graph and allocation tables. -/
@[noinline,nospecialize] def preparedBy (fb : Fintype B) (fs : Fintype S) (fe : Fintype E)
    (b : Equality B) (s : Equality S) (e : Equality E)
    (K : Book B S E) (P : Parameters B S) (w : ℕ) : Run (Book.Stored B S E) :=
  ContactCharge.price w (@Book.indexedContact B S E dB dS dE K fb fs fe b.decide s.decide e.decide P (8*(K.records.length+1)))

theorem preparedBy_eq [iB : Fintype B] [iS : Fintype S] [iE : Fintype E] [Encodable B] [Encodable S] [Encodable E]
    (fb : Fintype B) (fs : Fintype S) (fe : Fintype E) (b : Equality B) (s : Equality S) (e : Equality E)
    (K : Book B S E) (P : Parameters B S) (w : ℕ) :
    preparedBy fb fs fe b s e K P w = @ContactCharge.prepared B S E dB dS dE iB iS iE _ _ _ K P w := by
  have eb : fb=iB := Subsingleton.elim ..
  have es : fs=iS := Subsingleton.elim ..
  have ee : fe=iE := Subsingleton.elim ..
  subst fb; subst fs; subst fe
  simp only [preparedBy,ContactCharge.prepared,Book.indexedContact_eq]

end Kintali.QuotaSweep.RankRun
