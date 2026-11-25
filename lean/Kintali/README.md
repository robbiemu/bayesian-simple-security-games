# Formalizing Kintali’s exact equilibrium algorithm

Shiva Kintali’s November 24, 2026 preprint gives a deterministic
polynomial-bit-time algorithm for Vincent Conitzer’s Bayesian simple
security games problem. The paper uses Baïou and Balinski’s ordinal
transportation framework. [Short preprint](https://shivakintali.github.io/papers/SecurityGames-short.pdf) · [PDF at the author’s Git revision](https://github.com/shivakintali/shivakintali.github.io/blob/b28db0428e4cdcef7e9048a386b05d942d1eb57e/papers/SecurityGames-short.pdf)

**Lean checks an executable exact solver for every valid rational input.**
The solver uses the paper’s grouped sweep and weighted quote search. It
augments the witness and rounds a relaxed contact by integer linear
algebra. The correctness proof covers the exact public bit encoding,
zero priors and nonnegative slopes and defender gains. The complete
machine-level polynomial-time theorem remains a separate obligation.
[Solver](Solver.lean) · [Public bitstring theorem](InputOutput/Solver.lean)

## Proof in paper order

| Paper step | Checked result |
| --- | --- |
| §1, game and direct cases | The compact best-response predicate follows from the equilibrium certificate. The dispatcher handles zero budget, full budget, and enough resources to cover every positive-gain target. [Equilibrium](Equilibrium.lean) · [Preprocessing](Preprocessing.lean) |
| §1, Lemma 2 | Clearing denominators gives an integer pattern system. A determinant bound separates zero residual from any positive minimum. [Exact pattern system](ExactRecovery/Matrix.lean) · [Determinant bound](ExactRecovery/Determinant.lean) |
| §2, Lemma 3 | The deterministic quota sweep preserves feasibility and stability through acyclic and cyclic stages. The contact is the first feasible pressure at the supplied budget. The computation stores grouped private intervals, with a proved expansion to the elementary market. [Sweep](QuotaSweep/Run.lean) · [Sparse contact](QuotaSweep/SparseContact.lean) |
| §2, Lemmas 4–6 | The full-grid contact induces an exact-feasible pattern. Stable allocations preserve outside and vacancy balances at fixed quotas. Comparing two contacts at the same budget gives equal coverage or an omitted blocking bid. [Full-grid pattern](ExactRecovery/FullMarket.lean) · [Quota comparison](StableAllocation.lean) · [Contact comparison](ContactComparison.lean) |
| §3, weighted quote search | Each blocked trial doubles an interval that misses selected quantiles and contains a member of one fixed witness. The search finishes within `2 * h * (G.log2 + 1)` trials. [Executable search](QuoteSearch/Algorithm.lean) · [Witness certificate](TrialCorrectness.lean) |
| §3, exact recovery | A successful trial supplies its own relaxed point. A nonsingular integer minor repairs that point and returns an exact equilibrium. There is an addressed binary work bound for the implemented repair on its materialized inputs. [Recovery](Recovery.lean) · [Charged repair](LinearProgramming/RationalInput.lean) |
| §1, explicit strategy output | A sparse defender lottery has at most as many outcomes as there are targets. Every emitted defense uses exactly the supplied budget and reproduces the compact coverage marginals. Constructing the weighted membership masks takes polynomial addressed work in the binary length of the coverage. [Lottery](InputOutput/Lottery.lean) · [Lottery work](InputOutput/LotteryWork.lean) · [Public solver](InputOutput/Solver.lean) |

[Theorem1.lean](Theorem1.lean) gives the paper-order composition. The
concrete trial and sweep discharge its premises in [Solver.lean](Solver.lean).
`Game.solve_correct` and `InputOutput.solveBits_correct` establish total
exact recovery on valid inputs.

## Constructive recovery

Kintali’s witness includes the real bids that have positive flow at the
full-grid contact. The formalization adds the first eligible quote above
the contact coverage for each buyer and active target, when that quote
exists below the permanent cap. The witness therefore has size at most
`k + m₊ + k * m₊`. If its added bids do not block the restricted contact,
the restricted allocation itself satisfies the relaxed pattern rows.
[Witness](ExactRecovery/Witness.lean) · [Relaxed restricted contact](TrialCorrectness.lean)

The recovery routine appends the inequality requiring zero residual.
Among consecutive multiplicative windows for the row slacks, it finds an
empty one. A maximal independent set of rows below that window determines
a small projection via a nonsingular integer minor. The projection makes
the nearby rows exact, and the slack above the window absorbs the
movement. The program computes the minor by bordered tests and uses
integer determinants to recover all coordinates. This implements a
variant of the preprint’s LP recovery. Kintali’s original
full-contact pattern-feasibility result is also checked.
[Slack windows](LinearProgramming/SlackWindow.lean) · [Projection proof](LinearProgramming/Recovery.lean) · [Stored determinant](LinearProgramming/BirdRun.lean)

## Binary work and public statement

- Initialization computes the quote grid, private slope scale, outside
  options and eligible prefixes from the binary payoff tables. The search
  uses polynomially many trials and polynomial-width lists of compressed
  quote weights. Each trial builds a sparse inventory from selected quotes.
  [Initialization](InputOutput/InitializationWork.lean) · [Search bounds](SearchBounds.lean) · [Selected inventory](TrialWork/BuiltInventory.lean)
- The sweep counts scalar and indexed operations. Lean bounds the sizes
  of the stored states, coverage, joint masses, rounding inputs and compact
  output. The same work interface includes both blocker searches and exact
  recovery. [Sweep work](QuotaSweep/ContactCharge.lean) · [State widths](ContactSize/Prefix.lean) · [Trial work](TrialWork/SelectedExecute.lean) · [Output width](ContactSize/Output.lean)
- The public codec and market validity test cover all bitstreams,
  including malformed encodings and invalid tables. The assembled solver
  has one polynomial binary word-cost bound across all of those inputs.
  The sweep’s operation counter and rational arithmetic tariffs supply
  its part of the bound. [Public codec](InputOutput/PublicWork.lean) · [Measured solver](InputOutput/MeasuredSolver.lean)

The work bounds use the project’s indexed binary word-cost model.
The public Formal Conjectures proposition `exists_isPolyTime_bayesNash`
asks for one Mathlib `FinTM2` machine and a polynomial step bound on all
canonically encoded typed games. Lean checks the finite bit-stack
embedding, an executable public delimiter and the theorem that derives
the public proposition from actual runs of one solver program.
Refining the full solver to those runs remains open.
[Machine refinement](Machine/README.md) · [Formal Conjectures PR #8174](https://github.com/google-deepmind/formal-conjectures/pull/8174) · [Pinned public statement](https://github.com/google-deepmind/formal-conjectures/blob/9bd16c570aed942e00ae000c7522dd42ebbb25eb/FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean)

## Replay

Run from `lean/` with the pinned Lean 4.36.0 toolchain and Mathlib.

```sh
lake --wfail build Kintali
lake env lean Replay/KintaliAxioms.lean
lake env lean Replay/KintaliSearch.lean
```

The upstream compatibility check replays the public compact predicate
and the binary encoders against the pinned Formal Conjectures source.
[Compatibility replay](InputOutput/check_upstream.py)

The algorithm and original quota comparison come from Kintali’s
preprint. The witness extension, constructive recovery, and Lean
development were prepared with OpenAI Codex. The external table
and bit conventions follow the Formal Conjectures Authors’ public
statement.
