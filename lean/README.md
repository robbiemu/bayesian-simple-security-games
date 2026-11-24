# Lean workspace

This Lake package contains library checks for the fixed-flow investigation and an end-to-end proof and executable binary compiler for the stochastic-game reduction. It pins Lean and mathlib to v4.36.0. The Lake manifest records the exact revision of each dependency.

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

The top-level decision theorem `StochasticGames.ThresholdReduction.compile_correct` says that the source reachability value meets a rational threshold if and only if the emitted graph has nonnegative mean-payoff value at its designated start. It covers equality, nonterminating plays, terminal starts, and thresholds outside the unit interval. [Top-level proof](StochasticGames/ThresholdReduction.lean) · [Written proof](../notes/H4-ssg-to-mean-payoff.md)

- The source value is the probability of eventually reaching Win under optimal play with history-dependent randomized strategies. The least Bellman fixed point counts Win at time zero and yields a strict dual certificate. Each player row can have any nonempty list of moves. [Reachability semantics](StochasticGames/ReachabilitySemantics.lean)
- A strict real witness yields a rational certificate. The compiler uses a uniform violation gap to eliminate averages exactly and build integer max-atom rows. [Strict witness and precision](StochasticGames/SourcePrecision.lean) · [Compiler](StochasticGames/ThresholdCompiler.lean)
- The intermediate graph encodes the strict failure of the source threshold. The owner and weight reversal makes nonnegative lower limiting mean payoff accept the weak source threshold. A separate theorem establishes positional optimal strategies for both players. The graph uses contiguous vertex indices and preserves parallel arcs. [Arena encoding](StochasticGames/ArenaEncoding.lean) · [Threshold reversal](StochasticGames/MeanPayoffSemantics.lean) · [Positional saddle](StochasticGames/PositionalMeanPayoff.lean)
- The binary entry point `ThresholdReduction.compileBinary` maps source bits to target bits. Lean checks both decoding round trips, the graph's threshold answer, a cubic bound on output length, and a polynomial work bound in the stated list-scan and schoolbook-arithmetic model. [Binary entry point](StochasticGames/BinaryReduction.lean) · [Size and reduction bounds](StochasticGames/ReductionComplexity.lean) · [Cost model](StochasticGames/CompilationCost.lean)

To check the theorems' axiom dependencies and check the Lean compiler against exact source answers, run from the repository root with Z3 on your path.

```sh
(cd lean && lake build StochasticGames && lake env lean Replay/H4Axioms.lean)
python3 -B experiments/h4_lean_replay.py --systematic 2
```

The replay encodes each source instance, calls `compileBinary`, and decodes the resulting graph. Z3 gets only the graph and its start vertex. The harness compares its answer with a rational computation on the source. The corpus includes 3,634 game and threshold pairs. With no flag, the harness runs just the named fixtures. The closed-loop equality fixture emits 185 vertices and 330 arcs through the Lean compiler. The separate Python compiler uses explicit terminal vertices with pinning rows and emits a different table for that fixture. [Lean replay](../experiments/h4_lean_replay.py) · [Python compiler replay](../experiments/h4_ssg_to_mpg_replay.py)
