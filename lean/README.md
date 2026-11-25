# Lean workspace

This Lake package contains library checks for the fixed-flow investigation and an end-to-end proof and executable binary compiler for the stochastic-game reduction. It pins Lean and mathlib to v4.36.0. The Lake manifest records the exact revision of each dependency.

## Bayesian security-game algorithm

The `Kintali` library verifies executable exact Bayes–Nash equilibrium search using Shiva Kintali’s grouped quota sweep and weighted quote selection. Run `lake --wfail build Kintali`. The proof notes record correspondence with the paper and the status of the binary runtime theorem. [Kintali’s short proof](https://shivakintali.github.io/papers/SecurityGames-short.pdf) · [Lean development](Kintali/README.md)

## Running the checks

Open this directory as the project folder in your Lean editor. From the repository root, run

```sh
cd lean
lake build
lake test
```

On a fresh checkout with Elan on your path, run `lake exe cache get` in this directory to fetch the pinned packages and precompiled mathlib. `lake build` checks both libraries. `lake test` runs the `LibraryChecks` target. To check one library example, use `lake build +LibraryChecks.Assignments`.

## What the examples check

- Directed paths compose, and their rational affine edge costs add as affine maps. [WeightedPaths.lean](LibraryChecks/WeightedPaths.lean)
- A score on finite permutations attains a maximum. The examples check permutation cycles, reindexing a sum, and the row convention for permutation matrices. They verify an explicit rational two-by-two decomposition and apply Birkhoff–von Neumann to a real matrix given its entry and marginal conditions. [Assignments.lean](LibraryChecks/Assignments.lean)
- Simplex weights give convex combinations and scale to a specified total. The examples also check linear half-spaces and the equality condition for a sum of nonnegative terms. [FiniteWeights.lean](LibraryChecks/FiniteWeights.lean)
- Rational arithmetic exposes the reduced numerator and denominator, their binary sizes, and the ceiling. Rational affine expressions retain their values when cast to the reals. [ExactArithmetic.lean](LibraryChecks/ExactArithmetic.lean)
- An open interval contains a point outside any finite set of endpoints. Further examples check counting by injections, the floor of the base-two logarithm, asymptotic comparison, and a logarithmic remainder estimate. [IntervalsAndGrowth.lean](LibraryChecks/IntervalsAndGrowth.lean)

The current sketch also uses the Gajjar–Radhakrishnan parametric shortest-path construction, finite mixed Nash existence, and polynomial bit-time bounds for assignment and rational linear programming. A search of the pinned mathlib sources found no ready-to-import statements for those results.

## Stochastic game reduction

Start with `ThresholdReduction.compileBinary_polynomial_time`. Its proof puts together the emitted bit string, the decoded valid table, the exact threshold equivalence, and the work bound. [BinaryReduction.lean](StochasticGames/BinaryReduction.lean)

Follow `ThresholdReduction.compile_correct` for the mathematical argument. In the nonterminal case its calculation follows the manuscript from the strict reachability certificate through tightening, elimination of averages, integer rows, the intermediate arena, and sign reversal. Each step calls a theorem in the corresponding layer. The correspondence table identifies those declarations and points to the proof of the explicitly pinned arena. [ThresholdReduction.lean](StochasticGames/ThresholdReduction.lean) · [Manuscript correspondence](H4-correspondence.md)

Follow `CompilerExecution.run` and `.bitWork_le` for the executable argument. The decoder and serializer live in `CostedBinary`, the precision and row construction in `CostedRows`, and the numeric graph emitter in `CostedArena`. The shared word and address bounds live with the counted primitives in `CompilerRun`. [CompilerExecution.lean](StochasticGames/CompilerExecution.lean) · [CompilerRun.lean](StochasticGames/CompilerRun.lean)

`compileBits_le` bounds the serialized output length. The older size-based estimates are grouped below it as a separate reference for the earlier replay. [ReductionComplexity.lean](StochasticGames/ReductionComplexity.lean)

Run `lake build StochasticGames.BinaryReduction` for the main theorem and `lake build StochasticGames` for the full development.

The correctness theorem applies to the Lean compiler. The separate Python compiler is checked against exact source answers by replay. The original proof note records the state of the verification at the PR #10 checkpoint. [Original proof and Python replay (PR #10)](../notes/H4-ssg-to-mean-payoff.md)

To inspect the theorems' axiom dependencies and replay the Lean compiler against exact source answers, run from the repository root with Z3 on your path.

```sh
(cd lean && lake build StochasticGames && lake env lean Replay/H4Axioms.lean)
python3 -B experiments/h4_lean_replay.py --systematic 2
```

The replay encodes each source instance, calls `compileBinary`, and decodes the resulting graph. Z3 gets only the graph and its start vertex. The harness compares its answer with a rational computation on the source. The full corpus covers 3,635 game and threshold pairs. With no flag, the harness runs the named fixtures, including one that starts at state 1 and needs Max's third listed move to meet threshold 1.

On the closed-loop equality fixture, the Lean compiler emits 185 vertices and 330 arcs. The original Python compiler uses explicit terminal vertices with pinning rows and emits 193 vertices. [Lean replay](../experiments/h4_lean_replay.py) · [Python compiler replay](../experiments/h4_ssg_to_mpg_replay.py)
