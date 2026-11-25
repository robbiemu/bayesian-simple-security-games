module

public import Kintali.LinearProgramming.StoredSystem
public import Kintali.LinearProgramming.AnswerStream

/-!
# Exact recovery for integer inequalities

* `System.recover_feasible` proves that a supplied sufficiently near-feasible
  rational point rounds to an exact point.
* `RationalInput.run_feasible` and `RationalInput.run_binary_work` apply to
  the same stored algorithm and count its binary word work from dense integer
  coefficients and ordinary rational coordinates.
* `RationalInput.run_coordinate_size` bounds the reduced binary numerator and
  denominator, and `AnswerStream.correct` covers the optional binary writer.
* `PivotRun.Input.read_work` prices the materialization of an input matrix
  whose field computations have supplied work bounds.
* `System.solve` provides a separate exact bounded feasibility algorithm by
  exhaustive basis search.

The charged determinant uses Richard S. Bird's division-free recurrence and
its correctness theorem in Mathlib. The rounding algorithm uses the
slack-window and bordered-minor derivation from the local Kintali comparison.
-/
