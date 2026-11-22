# Bayesian simple security games

The research question is whether an exact Bayes–Nash equilibrium can be computed in polynomial time when targets, attacker types, payoffs, and the type distribution are explicitly given. [Conitzer, arXiv:2610.08796](https://arxiv.org/pdf/2610.08796)

**The general polynomial-time question is open.** This is a public working investigation of algorithms, restricted cases, and obstacles. Computational examples and model-assisted proof sketches are available for independent checking.

[**Choose an open question**](investigation/README.md) · [**How to contribute**](CONTRIBUTING.md) · [Who proposed each direction](DIRECTIONS.md) · [Proof map](PROOF-MAP.md)

A few places to start:

- **Try a new idea.** Can one supplied set of capacities yield a short, complete list of candidate prices for a general market? The node shows what already works and why the difficulty of counting a full price table has a narrower scope. [A4h5](investigation/A4h5.md)
- **Analyze an algorithm.** Each reweighted covering step costs polynomial work. Can one bound the number of steps, or force a long run for that particular rule? [A4e](investigation/A4e.md)
- **Check a concrete result.** Replay the small rational edge-revisit examples or examine the fixed-flow lower bound, including exactly which algorithms it rules out. [Reproduction record](records/b550a724-e9aa-4fb3-9668-c0ca5c9e8142.md) · [Audit](notes/B3g-lower-bound-audit.md)

Open the contribution form on any node to ask a child question, post a competing approach or share a negative result. The repository records individual contributions and the tools or models used. [Investigation notes and resume points](TREE.md) · [Publication and source information](PUBLICATION.md) · [CC BY 4.0 writing and MIT code](LICENSE.md)

## Results at a glance

- **Superpolynomial continuation lower bound.** For certain games with $n$ targets and $n$ uniformly likely types, varying the defender budget to one forces $n^{\Omega(\log n)}$ distinct attack flows in a single fixed-threshold, fixed-total phase. The bound applies to the published continuation and to jumps that maximize coverage while holding one attack flow fixed. At budget one those same games can be solved directly by an assignment problem and a feasibility LP. [Lower bound and scope](notes/B3f-forced-flow-switches.md)

- **General upper bound.** With $n$ targets, $k$ positive-prior types and binary input length $L$, an exact implementation of the resource-augmentation algorithm takes $2^{O(\min(n,k)\log(nk+1))}\cdot \mathrm{poly}(L)$ bit time. The proof covers weak payoff inequalities through rational perturbation and exact repair. Direct enumeration of payoff patterns gives an independent bound of the same order. [Iteration count](notes/B1-classify-run-lengths.md) · [Exact arithmetic and non-repetition proof](notes/L2-exact-arithmetic-audit.md)
- **Tractable structure.** Polynomial time suffices when each connected component of the graph of potentially optimal choices has a bounded number of types. There may be arbitrarily many components sharing one defender budget. A different polynomial-time case allows arbitrary attacker-loss slopes when the uncovered utilities can be written $a_{it}=A_i+d_{it}c_t$ for type offsets $A_i$ and target offsets $c_t$. [Component composition](notes/B2-component-composition.md) · [Exact log-price algorithm](notes/A3-mixed-offsets.md)
- **Prior partials.** The supplied collection already gives the fixed-type arrangement, the rank-one algorithm, the threshold ordering used in component composition, and the affine rent-division correspondence. The review records the evidence for its approximation argument and a zero-threshold endpoint correction for its rank-one algorithm. [Prior research collection](sources/prior-collection.md) · [Partial-results review](notes/L3-prior-partials.md)

The unrestricted polynomial-time question remains open. Exact equilibrium search is in **UniqueEOPL** by a direct reduction to one P-matrix linear complementarity problem. An independent market approach reduces the game to clearing fractional assignment markets with pair-specific affine utilities and binary-encoded masses and capacities. [P-matrix reduction](notes/A4d-p-matrix-complementarity.md) · [Market oracle reduction](notes/L3-prior-partials.md#conditional-exact-reduction-to-a-minimum-price-oracle) · [Supply perturbation](notes/A4c-any-clearing-equilibrium.md)

The two Oki–Sato directional auctions can take superpolynomially many steps even with two units of every good. A direct solver finds the minimum prices on that hard family in polynomial time because its slopes are nearly factorized. Other exact polynomial-time algorithms cover markets whose interaction graphs have bounded elimination depth or become forests after deleting a fixed number of goods. [A4 certificate and auction lower bound](notes/A4-minimum-price-markets.md) · [Near-factorized solver](notes/A4a-near-factorized-slopes.md) · [Hall search and elimination](notes/A4b-direct-hall-search.md)

Reweighted covering LPs with a slope-based tie-break reach an exact equilibrium with polynomial work per iteration. The iteration bound is exponential in general. If the intercepts admit common buyer and good offsets, a signed-root transformation gives polynomial time even for arbitrary slopes. [Covering LP and unweighted flow](notes/A4e-covering-lp.md)

The November 2026 sufficient-LCP preprint improves the handicap dependence of the Newton solve-count bound. A4d’s regularization can still have exponential handicap, even after positive diagonal scaling. Separately, clearing calls at slightly raised and lowered supplies find both endpoints of a fixed defender threshold and allow exact budget search without tracing the internal flow switches. [Newton bound and threshold endpoints](notes/L4-newton-and-continuation.md) · [Bounded-handicap formulation](notes/A4f-handicap-formulation.md)

## Worst-case run length by class

Fix an exact implementation $A$, including how it resolves ties. For a class $C$ of game instances, define $W_A(C)=\sup_{I\in C}\mathrm{iterations}(A,I)$. A finite upper bound makes this supremum a maximum for every nonempty class. Enumerating games with a fixed encoding length can compute such a maximum for a terminating implementation. A bound for games of arbitrary size needs a proof about how that maximum grows.

The published resource-augmentation algorithm partitions a run into $O(n)$ phases and counts payoff comparison signatures between phase changes. Its general catcher–evader bound is $2n+4n\cdot 3^{kn}$ outer iterations. In the one-target-per-type model, the number of feasible signatures is much smaller. One arrangement records comparisons among targets in $n$ coverage variables. The other records comparisons among types in $k$ payoff variables when the defender threshold is positive. The smaller arrangement yields a subexponential bound in $nk$. At a successful increase the defender threshold is a weighted Hall ratio fixed by the signature and phase. This fact lets the non-repetition proof handle threshold changes as well as flow ties. [Published bound, §6.2, Lemmas 6–8 and Theorem 5](https://arxiv.org/pdf/1602.01896) · [Proof for the one-target model](notes/L2-exact-arithmetic-audit.md)

A family with $m$ independent two-target blocks has $2^m$ reachable signatures across source choices. Every run takes exactly $m$ iterations. Counting completed blocks proves this maximum. For fixed dimensions, the full maximum over a semialgebraic class of strictly signed real inputs can also be computed in principle by quantifier elimination on the exact transitions. This keeps each entire candidate run on a single input. Finite rational encodings permit a separate exhaustive computation. [Exact worst-case example and decidability argument](notes/B1-classify-run-lengths.md)

The overlapping-types investigation gives polynomial continuation bounds when independent cycles are sparse or when the number of local cost levels can be bounded by a few slope generators and mass values. A separate solver handles components coupled by a fixed number of shared targets. The dense-slope construction forces many distinct states on a single run. [Progress measures and their limits](notes/B3-overlapping-types.md)

## Exact search by payoff patterns

The same dimensions give a direct exact algorithm that skips resource augmentation. In coverage space, arrange the $k\binom n2$ pairwise payoff equality hyperplanes and the $2n$ box boundaries. On each relatively open face, all best-response sets and coverage classes are fixed. The permitted $q$ and $\lambda$ satisfy linear constraints. Add those constraints and the resource budget to the face's defining inequalities, using one positive slack variable to certify every strict inequality. This handles all weak signs in the original model.

When $k<n$, use the type-value arrangement. Make the slopes and gains strictly positive with a small rational perturbation, retaining the option of exact repair by LP at the end. Check $\lambda=0$ directly for the perturbed game. For $\lambda>0$, each target's coverage is the maximum of its normalized demands and zero. Comparisons among those demands and with the boundaries 0 and 1 determine faces in $k$ dimensions, each again tested by LP. [Threshold and transport proof](notes/A1-threshold-transport.md)

## Compact model

Let $x_t$ be the defender’s coverage marginal, with $0\le x_t\le1$ and $\sum_t x_t=r$. For each type $i$ with prior $p_i>0$, let $q_{it}$ be the prior-weighted probability of choosing target $t$, so $q_{it}\ge0$ and $\sum_t q_{it}=p_i$.

Write $a_{it}=u_2^0(i,t)$, $d_{it}=u_2^0(i,t)-u_2^1(i,t)\ge0$, and $\beta_t=u_1^1(t)-u_1^0(t)\ge0$. A positive $q_{it}$ requires $a_{it}-d_{it}x_t$ to be maximal in row $i$. Given $q$, the defender maximizes $\sum_t x_t\beta_t\sum_i q_{it}$ over its coverage polytope. A scalar threshold $\lambda$ expresses the defender’s optimality through the following inequalities for $s_t=\beta_t\sum_i q_{it}$.

| Coverage | Required marginal reward |
| --- | --- |
| $x_t=0$ | $s_t\le\lambda$ |
| $0<x_t<1$ | $s_t=\lambda$ |
| $x_t=1$ | $s_t\ge\lambda$ |

Every feasible $x$ is a convex combination of incidence vectors of $r$-element subsets. The defender’s uncovered utility contributes a term constant in $x$. The assumptions allow zero payoff slopes and zero priors. A zero-prior type can be assigned any best response when reporting conditional strategies.
