# Lean workspace

This Lake package contains library checks for the fixed-flow investigation and a partial formalization of the stochastic-game reduction. It pins Lean and mathlib to v4.36.0. The Lake manifest records the exact revision of each dependency.

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

Run `lake build StochasticGames` to check the modules accompanying the [threshold proof](../notes/H4-ssg-to-mean-payoff.md).

- `StochasticGames.Reachability.horizon_value_lt_iff_fixed_terminals` gives the strict dual certificate for the supremum of finite-horizon Bellman iterates, with both terminal values. [ReachabilityThreshold.lean](StochasticGames/ReachabilityThreshold.lean)
- `StochasticGames.Reduction.exact_iff_selected_graph` handles finite rational row systems with bounded average-operand widths and bounded hard rows. The compiler derives a uniform violation gap and constructs the integer max-atom rows. The theorem proves that exact feasibility is equivalent to a row selection with nonnegative closed walks. [Reduction.lean](StochasticGames/Reduction.lean)
- `StochasticGames.MeanPayoffGraph.max_atoms_iff_arena_certificate` connects binary integer max-atoms to graph potentials and closed walks in the fresh-start arena. [MeanPayoffGraph.lean](StochasticGames/MeanPayoffGraph.lean)
- `StochasticGames.MeanPayoffThreshold.cycleMean_swap_nonneg_iff` gives the equality-preserving sign comparison for nonempty integer cycles of length at most $N$. `positional_saddle_swap` maps a supplied positional saddle to a saddle after swapping the players and transforming the weights. [MeanPayoffThreshold.lean](StochasticGames/MeanPayoffThreshold.lean)

The Lean compiler uses a general determinant-based precision bound for bounded systems. The Python replay implements the specialized simple stochastic game construction with the sharper bounds in the written proof. A formal correspondence between the two implementations remains open. [Python replay](../experiments/h4_ssg_to_mpg_replay.py)

The written proof supplies the stochastic interpretation of the Bellman iterates, the strict real-to-rational bridge, positional determinacy, and the bit-time bounds.
