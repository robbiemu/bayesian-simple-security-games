# Lean workspace

This Lake package contains small library checks for the fixed-flow investigation. It pins Lean and mathlib to v4.36.0. The Lake manifest records the exact revision of each dependency.

## Running the checks

Open this directory as the project folder in your Lean editor. From the repository root, run

```sh
cd lean
lake test
```

On a fresh checkout with Elan on your path, run `lake exe cache get` in this directory to fetch the pinned packages and precompiled mathlib. Both `lake test` and `lake build` check every file under `LibraryChecks/`. To check one file, use `lake build LibraryChecks/Assignments.lean`.

## What the examples check

- Directed paths compose, and their rational affine edge costs add as affine maps. [WeightedPaths.lean](LibraryChecks/WeightedPaths.lean)
- A score on finite permutations attains a maximum. The examples check permutation cycles, reindexing a sum, and the row convention for permutation matrices. They verify an explicit rational two-by-two decomposition and apply Birkhoff–von Neumann to a real matrix given its entry and marginal conditions. [Assignments.lean](LibraryChecks/Assignments.lean)
- Simplex weights give convex combinations and scale to a specified total. The examples also check linear half-spaces and the equality condition for a sum of nonnegative terms. [FiniteWeights.lean](LibraryChecks/FiniteWeights.lean)
- Rational arithmetic exposes the reduced numerator and denominator, their binary sizes, and the ceiling. Rational affine expressions retain their values when cast to the reals. [ExactArithmetic.lean](LibraryChecks/ExactArithmetic.lean)
- An open interval contains a point outside any finite set of endpoints. Further examples check counting by injections, the floor of the base-two logarithm, asymptotic comparison, and a logarithmic remainder estimate. [IntervalsAndGrowth.lean](LibraryChecks/IntervalsAndGrowth.lean)

The current sketch also uses the Gajjar–Radhakrishnan parametric shortest-path construction, finite mixed Nash existence, and polynomial bit-time bounds for assignment and rational linear programming. A search of the pinned mathlib sources found no ready-to-import statements for those results.
