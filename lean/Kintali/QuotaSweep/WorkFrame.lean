module

public import Kintali.QuotaSweep.WorkEvent
import Mathlib.Tactic.Linarith

/-! # A materialized rational holding table and its complete affine stage -/

@[expose] public section
namespace Kintali.QuotaSweep.Book

variable {B S E : Type*} [DecidableEq B] [DecidableEq S] [DecidableEq E]
variable (K : Book B S E)

structure Stored (B S E : Type*) where
  pressure : ℚ
  entries : List (Record B S E × ℚ)

namespace Stored

def read (z : Stored B S E) (e : Record B S E) : ℚ × ℕ := Work.search e 0 z.entries

def view (z : Stored B S E) : State B S E := ⟨z.pressure, fun e => (z.read e).1⟩

theorem read_work (z : Stored B S E) (e : Record B S E) : (z.read e).2 ≤ z.entries.length :=
  Work.search_work ..

end Stored

structure Frame (B S E : Type*) where
  speed : ℚ
  duration : ℚ
  slopes : List (Record B S E × ℚ)

variable [Fintype B] [Fintype S]

def frame (unit : ℕ) (P : Parameters B S) (z : Stored B S E) : Frame B S E × ℕ :=
  let g := K.graph unit z.read P.rate
  let t := K.measuredDuration g.1 z.read z.pressure P.upper
  let m := Work.tabulate (derivative g.1) K.records
  (⟨if g.1.source.isSome then 0 else 1,t.1,m.1⟩,g.2+t.2+m.2+1)

theorem frame_speed (unit : ℕ) (P : Parameters B S) (z : Stored B S E) :
    (K.frame unit P z).1.speed = K.speed z.view.allocation := by
  simp [frame,K.graph_source,speed,hasCycle,Stored.view]
  rfl

theorem frame_time (unit : ℕ) (P : Parameters B S) (z : Stored B S E) :
    (K.frame unit P z).1.duration = K.duration z.view.allocation P.rate z.pressure P.upper :=
  K.measuredDuration_value ..

theorem frame_slope (unit : ℕ) (P : Parameters B S) (z : Stored B S E) (e : Record B S E) :
    (Work.search e 0 (K.frame unit P z).1.slopes).1 =
      K.direction z.view.allocation (K.through z.view.allocation P.rate) e :=
  (Work.read_tabulate _ _ _ (K.complete e)).trans (K.derivative_value ..)

theorem frame_length (unit : ℕ) (P : Parameters B S) (z : Stored B S E) :
    (K.frame unit P z).1.slopes.length = K.records.length := by simp [frame]

def frameLimit (n r u : ℕ) :=
  graphLimit n r u + (r*(r+r+u+4)+3*r+5) + r*(n*(r+r+4)+2)+1

theorem frame_work (unit : ℕ) (P : Parameters B S) (z : Stored B S E) (hz : z.entries.length ≤ unit) :
    (K.frame unit P z).2 ≤ frameLimit (Fintype.card (Vertex B S)) K.records.length unit := by
  let r := K.records.length
  let n := Fintype.card (Vertex B S)
  let g := K.graph unit z.read P.rate
  have hx (e) := (z.read_work e).trans hz
  have hg := K.graph_work unit z.read hx P.rate
  have hsize := K.graph_table_lengths unit z.read P.rate
  have hm : g.1.markers.length ≤ r := hsize.1.le.trans K.vertexOrder_length
  have hq : g.1.rates.length ≤ r := hsize.2.le.trans K.vertexOrder_length
  have hel := K.measuredDuration_work g.1 z.read unit hx z.pressure P.upper
  have he : (K.measuredDuration g.1 z.read z.pressure P.upper).2 ≤ r*(r+r+unit+4)+3*r+5 := by
    apply hel.trans; gcongr
  have hd (e) : (derivative g.1 e).2 ≤ n*(r+r+4)+1 := by
    apply (derivative_work g.1 e).trans; gcongr
  have hs := Work.tabulate_work _ _ hd K.records
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hg he) hs) 1

def applyFrame (f : Frame B S E) (z : Stored B S E) (δ : ℚ) : Stored B S E × ℕ :=
  let t := Work.tabulate (fun e =>
    let a := z.read e
    let b := Work.search e 0 f.slopes
    (a.1+δ*b.1,a.2+b.2+2)) K.records
  (⟨z.pressure+δ*f.speed,t.1⟩,t.2+2)

omit [DecidableEq B] [DecidableEq S] [DecidableEq E] [Fintype B] [Fintype S] in
private theorem state_eq (a b : State B S E) (hp : a.pressure = b.pressure)
    (ha : a.allocation = b.allocation) : a = b := by cases a; cases b; simp_all

theorem applyFrame_value (unit : ℕ) (P : Parameters B S) (z : Stored B S E) (δ : ℚ) :
    (K.applyFrame (K.frame unit P z).1 z δ).1.view = K.segment P z.view δ := by
  cases z with
  | mk pressure entries =>
    apply state_eq
    · simp [applyFrame,Stored.view,K.frame_speed,segment]
    · funext e
      simp only [Stored.view,applyFrame,Stored.read]
      rw [Work.read_tabulate _ _ _ (K.complete e)]
      simp [segment,move,K.frame_slope,Stored.view,Stored.read]

omit [Fintype B] [Fintype S] in
theorem applyFrame_length (f : Frame B S E) (z : Stored B S E) (δ : ℚ) :
    (K.applyFrame f z δ).1.entries.length = K.records.length := by simp [applyFrame]

omit [Fintype B] [Fintype S] in
theorem applyFrame_work (f : Frame B S E) (z : Stored B S E) (δ : ℚ) :
    (K.applyFrame f z δ).2 ≤ K.records.length*(z.entries.length+f.slopes.length+3)+2 := by
  apply Nat.add_le_add_right (Work.tabulate_work _ (z.entries.length+f.slopes.length+2) _ K.records) 2
  intro e
  exact Nat.add_le_add_right (Nat.add_le_add (z.read_work e) (Work.search_work ..)) 2

def outsideRead (buyers : Finset B) (t : List (Record B S E × ℚ)) : ℚ × ℕ :=
  Work.sum buyers fun b => Work.search (outside b) 0 t

omit [Fintype B] [Fintype S] in
theorem outsideRead_value (buyers : Finset B) (z : Stored B S E) :
    (outsideRead buyers z.entries).1 = privateOutside buyers z.view.allocation :=
  Work.sum_value _ _

theorem outsideRead_slope (unit : ℕ) (P : Parameters B S) (z : Stored B S E) :
    (outsideRead P.privateBuyers (K.frame unit P z).1.slopes).1 = K.budgetSlope P z.view := by
  simp [outsideRead,Work.sum_value,K.frame_slope,budgetSlope,privateOutside]

omit [Fintype B] [Fintype S] in
theorem outsideRead_work (buyers : Finset B) (t : List (Record B S E × ℚ)) :
    (outsideRead buyers t).2 ≤ buyers.card*(t.length+2) :=
  Work.sum_work buyers _ t.length (fun b => Work.search_work (outside b) 0 t)

end Kintali.QuotaSweep.Book
