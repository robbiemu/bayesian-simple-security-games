module

public import Kintali.Theorem1
import Mathlib.Tactic.Ring

/-!
# Explicit payoff tables and compact equilibrium outputs

The external types, table access conventions, validity conditions and compact
best-response predicate follow the Formal Conjectures Authors' Apache-2.0
statement for arXiv:2610.08796, at commit
[9bd16c57](https://github.com/google-deepmind/formal-conjectures/blob/9bd16c570aed942e00ae000c7522dd42ebbb25eb/FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean).
The conversion and its correctness proof implement §1 of Kintali's short proof.
-/

open scoped BigOperators

@[expose] public section

namespace Kintali.InputOutput

abbrev Payoffs := ℚ × ℚ
abbrev Input := ℕ × List Payoffs × List (ℚ × List Payoffs)
abbrev Output := List ℚ × List (List ℚ)

namespace Input

def targets (a : Input) := a.2.1.length
def types (a : Input) := a.2.2.length

def defense (a : Input) (j : Fin a.targets) := a.2.1.get j
def prior (a : Input) (i : Fin a.types) := (a.2.2.get i).1
def offers (a : Input) (i : Fin a.types) := (a.2.2.get i).2
def attack (a : Input) (i : Fin a.types) (j : Fin a.targets) : Payoffs :=
  (a.offers i)[j.val]?.getD (0, 0)

def Valid (a : Input) : Prop :=
  0 < a.targets ∧ a.1 ≤ a.targets ∧ (∑ i, a.prior i) = 1 ∧
    (∀ j, (a.defense j).1 ≤ (a.defense j).2) ∧
    ∀ i, 0 ≤ a.prior i ∧ (a.offers i).length = a.targets ∧
      ∀ j, (a.attack i j).2 ≤ (a.attack i j).1

/-- Pass from payoffs to Kintali's cost intercepts, slopes and defense gains. -/
def game (a : Input) : Game (Fin a.types) (Fin a.targets) where
  resources := a.1
  prior := a.prior
  intercept i j := -(a.attack i j).1
  slope i j := (a.attack i j).1 - (a.attack i j).2
  gain j := (a.defense j).2 - (a.defense j).1

theorem valid_iff (a : Input) : a.Valid ↔
    a.game.Valid ∧ ∀ i, (a.offers i).length = a.targets := by
  constructor
  · rintro ⟨ht, hb, hp, hd, ha⟩
    exact ⟨⟨ht, hb, fun i => (ha i).1, hp, fun j => sub_nonneg.mpr (hd j),
      fun i j => sub_nonneg.mpr ((ha i).2.2 j)⟩, fun i => (ha i).2.1⟩
  · rintro ⟨h, shape⟩
    exact ⟨h.targets, h.budget, h.prior_sum, fun j => sub_nonneg.mp (h.gain_nonneg j),
      fun i => ⟨h.prior_nonneg i, shape i, fun j => sub_nonneg.mp (h.slope_nonneg i j)⟩⟩

end Input

def readRow (e : Output) (i : ℕ) := e.2[i]?.getD []

def readStrategy (e : Output) (k m : ℕ) : Strategy k m where
  coverage j := e.1[j.val]?.getD 0
  attacks i j := (readRow e i.val)[j.val]?.getD 0

def writeStrategy {k m : ℕ} (s : Strategy k m) : Output :=
  (List.ofFn s.coverage, List.ofFn fun i => List.ofFn (s.attacks i))

@[simp] theorem read_write {k m : ℕ} (s : Strategy k m) :
    readStrategy (writeStrategy s) k m = s := by
  cases s
  simp [writeStrategy, readStrategy, readRow]

def Input.utility (a : Input) (i : Fin a.types) (j : Fin a.targets) (x : ℚ) :=
  (1 - x) * (a.attack i j).1 + x * (a.attack i j).2

def Input.coverageGain (a : Input) (s : Strategy a.types a.targets) (j : Fin a.targets) :=
  (∑ i, a.prior i * s.attacks i j) * ((a.defense j).2 - (a.defense j).1)

/-- The public compact predicate, expressed using named accessors. -/
def Input.IsBayesNash (a : Input) (e : Output) : Prop :=
  let s := readStrategy e a.types a.targets
  e.1.length = a.targets ∧ e.2.length = a.types ∧
    (∑ j, s.coverage j) = (a.1 : ℚ) ∧
    (∀ j, 0 ≤ s.coverage j ∧ s.coverage j ≤ 1) ∧
    (∀ i, (readRow e i.val).length = a.targets ∧ (∑ j, s.attacks i j) = 1 ∧
      ∀ j, 0 ≤ s.attacks i j) ∧
    (∀ i j t, 0 < s.attacks i j → a.utility i t (s.coverage t) ≤ a.utility i j (s.coverage j)) ∧
    (∀ j t, 0 < s.coverage j → s.coverage t < 1 → a.coverageGain s t ≤ a.coverageGain s j)

def Shape (e : Output) (k m : ℕ) : Prop :=
  e.1.length = m ∧ e.2.length = k ∧ ∀ i : Fin k, (readRow e i.val).length = m

@[simp] theorem shape_write {k m : ℕ} (s : Strategy k m) : Shape (writeStrategy s) k m := by
  simp [Shape, writeStrategy, readRow]

theorem Input.cost_eq (a : Input) (i : Fin a.types) (j : Fin a.targets) (x : ℚ) :
    a.game.cost i j x = -a.utility i j x := by
  simp only [Game.cost, Input.game, Input.utility]
  ring

theorem Input.equilibrium_iff (a : Input) (e : Output) :
    let s := readStrategy e a.types a.targets
    a.IsBayesNash e ↔ Shape e a.types a.targets ∧ a.game.IsBayesNash s.coverage s.attacks := by
  dsimp only
  constructor
  · rintro ⟨hx, hr, hs, hb, hd, ha, hf⟩
    refine ⟨⟨hx, hr, fun i => (hd i).1⟩, ⟨hs, hb, fun i => (hd i).2, ?_, hf⟩⟩
    intro i j t h
    simpa only [a.cost_eq, neg_le_neg_iff] using ha i j t h
  · rintro ⟨⟨hx, hr, hrow⟩, h⟩
    refine ⟨hx, hr, h.coverage_sum, h.coverage_bounds, fun i => ⟨hrow i, h.distribution i⟩, ?_, h.defender⟩
    intro i j t hp
    simpa only [a.cost_eq, neg_le_neg_iff] using h.attacker i j t hp

/-- The raw wrapper is total, including for malformed tables. Its guarantee is for valid inputs. -/
def solveWith (solve : ∀ {k m}, Game (Fin k) (Fin m) → Strategy k m) (a : Input) : Output :=
  writeStrategy (solve a.game)

theorem solveWith_correct (solve : ∀ {k m}, Game (Fin k) (Fin m) → Strategy k m)
    (correct : ∀ {k m} (g : Game (Fin k) (Fin m)), g.Valid →
      g.IsBayesNash (solve g).coverage (solve g).attacks) (a : Input) (valid : a.Valid) :
    a.IsBayesNash (solveWith solve a) := by
  apply (a.equilibrium_iff _).2
  simpa only [solveWith, shape_write, true_and, read_write] using
    correct a.game ((a.valid_iff).1 valid).1


/-- The affine game forgets the defender's additive baseline, so choose zero
for the uncovered defender payoff when serializing a typed game. -/
def writeGame {k m : ℕ} (g : Game (Fin k) (Fin m)) : Input :=
  (g.resources, List.ofFn (fun j => (0, g.gain j)), List.ofFn (fun i =>
    (g.prior i, List.ofFn (fun j => (-g.intercept i j, -g.intercept i j - g.slope i j)))))

@[simp] theorem writeGame_targets {k m : ℕ} (g : Game (Fin k) (Fin m)) :
    (writeGame g).targets = m := by simp [writeGame, Input.targets]

@[simp] theorem writeGame_types {k m : ℕ} (g : Game (Fin k) (Fin m)) :
    (writeGame g).types = k := by simp [writeGame, Input.types]

/-- Reread a table whose physical dimensions are given by the caller. -/
def Input.gameAs (a : Input) {k m : ℕ} (hk : a.types = k) (hm : a.targets = m) :
    Game (Fin k) (Fin m) where
  resources := a.game.resources
  prior i := a.game.prior (Fin.cast hk.symm i)
  intercept i j := a.game.intercept (Fin.cast hk.symm i) (Fin.cast hm.symm j)
  slope i j := a.game.slope (Fin.cast hk.symm i) (Fin.cast hm.symm j)
  gain j := a.game.gain (Fin.cast hm.symm j)

@[simp] theorem gameAs_write {k m : ℕ} (g : Game (Fin k) (Fin m)) :
    (writeGame g).gameAs (writeGame_types g) (writeGame_targets g) = g := by
  cases g
  simp [Input.gameAs, Input.game, Input.prior, Input.defense, Input.attack, Input.offers,
    writeGame, Input.types, Input.targets, Fin.cast]

theorem Input.valid_gameAs_iff (a : Input) {k m : ℕ} (hk : a.types = k) (hm : a.targets = m) :
    (a.gameAs hk hm).Valid ↔ a.game.Valid := by
  subst k m
  rfl

theorem valid_writeGame_iff {k m : ℕ} (g : Game (Fin k) (Fin m)) :
    (writeGame g).Valid ↔ g.Valid := by
  have core := (writeGame g).valid_gameAs_iff (writeGame_types g) (writeGame_targets g)
  rw [gameAs_write] at core
  rw [Input.valid_iff, ← core]
  have rows (i : Fin (writeGame g).types) : ((writeGame g).offers i).length = (writeGame g).targets := by
    let cols := fun i : Fin k => (g.prior i, List.ofFn fun j => (-g.intercept i j, -g.intercept i j - g.slope i j))
    have hmem := (List.ofFn cols).get_mem i
    obtain ⟨t, eq⟩ := List.mem_ofFn.mp hmem
    change ((List.ofFn cols).get i).2.length = _
    rw [← eq, writeGame_targets]
    simp [cols]
  exact and_iff_left rows

/-- A correctly shaped compact output is recovered exactly by serialization. -/
theorem write_read (e : Output) {k m : ℕ} (shape : Shape e k m) :
    writeStrategy (readStrategy e k m) = e := by
  rcases shape with ⟨hx, hr, hrow⟩
  apply Prod.ext
  · apply List.ext_getElem
    · simpa [writeStrategy] using hx.symm
    · intro j hj he
      simp [writeStrategy, readStrategy, he]
  · apply List.ext_getElem
    · simpa [writeStrategy] using hr.symm
    · intro i hi he
      have hrow' := hrow ⟨i, by simpa [writeStrategy] using hi⟩
      have rowlen : e.2[i].length = m := by simpa [readRow, he] using hrow'
      simp only [writeStrategy, List.getElem_ofFn]
      apply List.ext_getElem
      · simpa using rowlen.symm
      · intro j hj hj'
        simp [readStrategy, readRow, he, hj']

end Kintali.InputOutput
