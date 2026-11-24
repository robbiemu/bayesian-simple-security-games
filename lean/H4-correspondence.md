# H4 manuscript correspondence

The manuscript edition is the November 24, 2026 working draft of
*Reducing simple stochastic reachability games to deterministic mean-payoff games*.
The review used a separately supplied TeX copy with SHA-256
`49b62015c805a746d543a579148d47a74d2eb810491e275853fcf73fa48a376c`.
The theorem numbers and page references below follow that edition.

The Lean comparison starts at PR #11 revision `224d0be`. The follow-up
review checked the real-witness statements of Proposition 4, the arena
representation bridges, and the executable bit-time theorem at
`9d7499e`. [Lean baseline](https://github.com/robbiemu/bayesian-simple-security-games/tree/224d0bed03458b5a03ae7043728b80b86083bc55/lean/StochasticGames) · [Reviewed Lean revision](https://github.com/robbiemu/bayesian-simple-security-games/tree/9d7499ea6904da11b6c89f20b5c442832d26dd51/lean/StochasticGames) · [Original proof and Python replay (PR #10)](../notes/H4-ssg-to-mean-payoff.md)

| Manuscript | Quantifiers and conclusion | Lean and representation |
| --- | --- | --- |
| Theorem 1, pp. 1–2 | One encoder for every finite simple stochastic game, starting state, and binary rational threshold. It emits one deterministic integer-weight arena whose weak threshold agrees with the source weak threshold. | `ThresholdReduction.compileBinary_polynomial_time` gives the valid emitted table, the decision equivalence, and the executed cost bound for every accepted bit string. `PaperArena.table_correct` gives the decision equivalence for the paper's explicitly pinned arena in the nontrivial case. [Binary theorem](StochasticGames/BinaryReduction.lean) · [Paper arena](StochasticGames/PaperArena.lean) |
| Lemma 2, §2 | For each fixed game, the value of eventual reachability is the least Bellman fixed point. For any real threshold, a strict failure has a real dual witness. | `Source.value_eq_lfp`, `Source.value_eq_upperValue`, and `Source.value_lt_iff_dualFeasible`. `Source.hasSum_firstHit` and `Source.positionalMin_eventual_le` justify the value even when play can run forever. [Reachability](StochasticGames/ReachabilitySemantics.lean) · [First hits](StochasticGames/SourcePlay.lean) · [Threshold certificate](StochasticGames/ReachabilityThreshold.lean) |
| Lemma 3, §3 | In a nonempty bounded real polyhedron with integral coefficient rows of length at most $A$, a positive coordinate optimum at either extremum is at least $1/(BA^d)$ when a positive integer $B$ clears every right-hand side. | `RealStrictWitness.exists_rational_extremal_coordinate` gives a rational point on the same optimal face and the positive-coordinate bound. Tight rows and Cramer's rule also cover polyhedra of smaller affine dimension. [Determinant bound](StochasticGames/RealStrictWitness.lean) |
| §§3.1–3.2 | On the selected branch a strict margin can be tightened by $\delta=1/D$. Every feasible relaxed branch has an attained minimum slack equal to zero or at least $\gamma=1/(D4^{n+1})$. Here $D=b3^{n+1}$ uses the supplied denominator $b$. | `SourcePrecision.strengthen_selected` gives a rational witness on the chosen branch with the larger margin. `.tightened_minimum_slack` applies compactness and Lemma 3 to give a rational minimizer among all admissible real assignments of that branch. `.tightened_real_gap` uses this result to remove any slack below $\gamma$. [Precision](StochasticGames/SourcePrecision.lean) · [Branch matrices](StochasticGames/SourceLinearization.lean) |
| Proposition 4, §4 | Every real exact witness extends by evaluation with identical source labels. Every real compiled witness gives a rational exact witness on its attaining original branch. | `RealCompilation.exact_extends_by_evaluation` and `.compiled_selects_attaining_branch` give the two statements for the actual weighted rows. `.compiled_repairs_same_branch` works for any supporting selection. The gate comparison applies to arbitrary real auxiliary values. `SourcePrecision.error_lt_gap` proves $2^{-r-1}<\gamma$ for the computed $r$. [Real compilation](StochasticGames/RealCompilation.lean) · [Gate bounds](StochasticGames/ShiftedComparisons.lean) |
| §5 scaling and terminal pins | Scale by $Q=D2^{r+1}$, preserve feasibility when flooring, and pin terminal variables relative to the origin. | `RealCompilation.real_compiled_iff_integer` uses coordinatewise flooring. `PaperArena.weightedBody_eliminates` substitutes the pins in the actual named body, including the origin-based box and threshold rows. `.weighted_body_feasible` preserves the original coordinates in both directions. `ArenaRepresentation.encode_eliminate` proves that the substitution commutes with scaling. [Real scaling](StochasticGames/RealCompilation.lean) · [Paper rows](StochasticGames/PaperArena.lean) · [Pin substitution](StochasticGames/ArenaRepresentation.lean) |
| Lemma 5, §5 | For a finite nonempty variable set and integer rows with nonempty terms, one fresh start tests all variables. The origin supplies a variable even in the degenerate case. Feasibility is equivalent to a nonnegative value in the intermediate game. | `AtomArena.rows_iff_certificate` and `MeanPayoff.Game.nonnegative_iff_certificate` give the equivalence. Minimum path weight to an arbitrary endpoint is the sink-distance construction. `ArenaRepresentation.explicit_table_checked` handles the two conventions for missing left sides. `PaperArena.table_checked` verifies validity and the threshold comparison before and after the owner swap. [Arena proof](StochasticGames/AtomArena.lean) · [Potential](StochasticGames/MeanPayoffGraph.lean) · [Paper table](StochasticGames/PaperArena.lean) |
| §6 reversal | With $N$ the size of the particular intermediate arena, swapping the owners and replacing each $w$ with $-Nw-1$ gives the affine value identity and reverses the strict threshold. | `MeanPayoff.Game.swap_value` proves the identity for game values defined from liminf payoffs using positional certificates and prefix bounds. The top-level proof uses `.swap_nonnegative_iff` for the sign. `.Swap` uses each arena's own vertex count. [Affine identity](StochasticGames/PositionalMeanPayoff.lean) · [Threshold sign](StochasticGames/MeanPayoffSemantics.lean) |
| §6 size and execution | One input-computable depth and scale, polynomially many entries and polynomial bit time to produce the arena. | `CompilationCounts.tightened_graph_size`, `ThresholdCompiler.final_weight_le`, and `ThresholdReduction.compileBits_le` bound the graph, weights, and actual output bits. `CompilerExecution.run_bound` composes the executed stages and `.bitWork_le` bills their observed operations and widths. The fixed work polynomial has degree 24. The output length has its own cubic bound. [Counts](StochasticGames/CompilationCounts.lean) · [Weights](StochasticGames/ThresholdCompiler.lean) · [Output bits](StochasticGames/ReductionComplexity.lean) · [Execution](StochasticGames/CompilerExecution.lean) |

Equality is a YES because the intermediate system tests strict failure.
Player rows have a head and a tail, so any finite nonempty list is supported.
Repeated moves remain listed occurrences and may give parallel arcs.
Terminal starts and thresholds $t\le 0$ or $t>1$ use the single-loop cases.
The parser recovers the supplied numerator and positive denominator, so a
threshold written as $2/6$ retains $b=6$ for the precision calculation.
[Source input](StochasticGames/ThresholdInput.lean) · [Binary input](StochasticGames/CostedBinary.lean) · [Threshold dispatch](StochasticGames/ThresholdReduction.lean)

## Executed bit cost

The costed run sequences the reader, parameter and gate construction, arena
emission, and writer. The decoder proves that every accepted bit string
re-encodes identically. The arena explicitly scans its variable and row lists.
The row and arena stages use binary integers for the threshold, shifts and
weights. The arithmetic bounds use the widths of the operands in those
operations. The serializer accounts for list traversal, headers, and output
digits. Erasing the counts preserves the original output bit string.
[Decoder and writer](StochasticGames/CostedBinary.lean) · [Rows](StochasticGames/CostedRows.lean) · [Arena](StochasticGames/CostedArena.lean)

The model uses binary words and indexed memory. A cell transition handles a
fixed number of fields and links. Schoolbook arithmetic uses polynomial
scratch space in the operand width. The decoder reserves its array only
after the rows have parsed, so its capacity is at most the input length.
The bill uses a common width for operands, counters, and binary addresses.
`CompilerRun.memory_address_fits` bounds the width required for the model's space
allowance. The polynomial covers the emitted arena on well-formed inputs
under the operation charges of this model.
[Transition and address accounting](StochasticGames/CompilerRun.lean) · [Time bound](StochasticGames/CompilerExecution.lean)

## Manuscript record

The November 24 manuscript describes the Lean snapshot bundled with the
original Python replay.

> The probabilistic identification of the Bellman limit, the passage from real strict witnesses to rational certificates, positional determinacy for game payoffs, and the full encoding and bit-time argument are supplied in the written proof.
>
> The Lean compiler uses a general determinant bound and the Python compiler uses the game-specific precision above. Their formal correspondence remains open.

At `224d0be`, PR #11 verifies the probabilistic semantics, real strict-witness
bridge, and positional determinacy. Its compiler uses the game-specific
precision. This update adds the witness-level compiler statements, the
representation bridges, and the executable bit-time theorem.
The representation theorem compares the two Lean constructions. The Python
encoder is covered by the replay.
[PR #11 baseline](https://github.com/robbiemu/bayesian-simple-security-games/tree/224d0bed03458b5a03ae7043728b80b86083bc55/lean/StochasticGames)

The manuscript can describe the updated artifact as follows.

> The companion Lean development checks the reachability and mean-payoff semantics, both real-witness directions of Proposition 4, and the exact decision result for one executable binary encoder. The encoder uses the game-specific precision of the proof. Lean bounds the work of its parser, graph construction, and writer by a fixed polynomial in the input length under the stated binary cost model. The Lean and Python encoders may emit different arenas because they represent terminal literals differently.
