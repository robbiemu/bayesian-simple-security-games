module

public import Kintali.QuotaSweep.WorkRun
public import Mathlib.Logic.Encodable.Basic

/-!
# Equality on the sparse runtime indices

Computing equality of dependent finite indices through the generic sigma
instance may reevaluate their fiber sizes. All sparse indices have a
constructive injective natural encoding. The following adapter passes these
comparison functions once to the graph and holding-table operations.
-/

@[expose] public section
namespace Kintali.QuotaSweep.Book

@[noinline] def encodedEq {T : Type*} [Encodable T] (x y : T) : Decidable (x=y) :=
  decidable_of_iff (Encodable.encode x = Encodable.encode y)
    ⟨fun h => Encodable.encode_injective h,congrArg Encodable.encode⟩

variable {B S E : Type*} [dB : DecidableEq B] [dS : DecidableEq S] [dE : DecidableEq E]
variable (K : Book B S E) [Fintype B] [Fintype S] [Fintype E]

def sameBook (b : DecidableEq B) (s : DecidableEq S) (e : DecidableEq E) :
    @Book B S E b s e := by
  have hb : dB = b := Subsingleton.elim ..
  have hs : dS = s := Subsingleton.elim ..
  have he : dE = e := Subsingleton.elim ..
  exact hb ▸ hs ▸ he ▸ K

@[noinline, nospecialize] def indexedContact (b : DecidableEq B) (s : DecidableEq S) (e : DecidableEq E)
    (P : Parameters B S) (u : ℕ) : Stored B S E × ℕ :=
  @contactWork B S E b s e (@sameBook B S E dB dS dE K b s e) _ _ P _ u

theorem indexedContact_eq (b : DecidableEq B) (s : DecidableEq S) (e : DecidableEq E)
    (P : Parameters B S) (u : ℕ) : @indexedContact B S E dB dS dE K _ _ _ b s e P u =
      @contactWork B S E dB dS dE K _ _ P _ u := by
  have hb : b = dB := Subsingleton.elim ..
  have hs : s = dS := Subsingleton.elim ..
  have he : e = dE := Subsingleton.elim ..
  subst b; subst s; subst e
  rfl

namespace Stored

@[noinline] def encodedRead {B S E : Type*} [Encodable B] [Encodable S] [Encodable E]
    (z : Stored B S E) (r : Record B S E) : ℚ × ℕ :=
  @Work.search _ ℚ encodedEq r 0 z.entries

def encodedView {B S E : Type*} [Encodable B] [Encodable S] [Encodable E]
    (z : Stored B S E) : State B S E := ⟨z.pressure,fun r => (z.encodedRead r).1⟩

omit [Fintype B] [Fintype S] [Fintype E] in
theorem encodedRead_eq [Encodable B] [Encodable S] [Encodable E] (z : Stored B S E) (r : Record B S E) :
    z.encodedRead r = z.read r := by
  unfold encodedRead read
  rw [Subsingleton.elim (@encodedEq (Record B S E) _) (inferInstance : DecidableEq (Record B S E))]

omit [Fintype B] [Fintype S] [Fintype E] in
theorem encodedView_eq [Encodable B] [Encodable S] [Encodable E] (z : Stored B S E) :
    z.encodedView = z.view := by simp [encodedView,view,encodedRead_eq]

end Stored

end Kintali.QuotaSweep.Book
