# Bayesian simple security games

Vincent Conitzer asked whether an exact Bayes–Nash equilibrium can be computed in polynomial time when targets, attacker types, payoffs, and the type distribution are explicitly given. [Conitzer’s open problem](https://arxiv.org/abs/2610.08796)

## Kintali’s polynomial-time algorithm

**Shiva Kintali’s November 24, 2026 preprint presents a deterministic polynomial-bit-time algorithm for Conitzer’s full problem.** It uses a stable-allocation sweep at the supplied budget, weighted quantile selection of market quotes, and exact recovery by rational linear programming. The nine-page proof is the source for this repository’s Lean formalization. [Short proof](https://shivakintali.github.io/papers/SecurityGames-short.pdf) · [Kintali’s papers and other versions](https://shivakintali.github.io/)

**Lean verifies that the executable solver returns an exact equilibrium for every valid rational input**, including the public bitstring encoding. It verifies polynomial work in the project’s binary word-cost model. The remaining formalization is the step bound for the public finite-machine statement. Applying the A4i reduction to Kintali’s theorem also gives polynomial-time exact affine-market clearing and minimum-price recovery. [Lean proof status](lean/Kintali/README.md) · [A4i reverse reduction](notes/A4i-market-to-game.md)

Kintali’s result and the checked Lean development conclude this repository’s main investigation.

The companion manuscript presents the stability argument, exact recovery, and verification of the constructive Lean variant. [Read the manuscript (PDF)](papers/kintali-lean/kintali-lean.pdf) · [TeX source](papers/kintali-lean/kintali-lean.tex) · [Verification record](papers/kintali-lean/verification.txt)

The standalone Python implementation reads rational game data and emits an exact equilibrium and a sparse defender lottery. Its replay checks the Python and Lean outputs against the same equilibrium conditions. [Python solver and replay](lean/Kintali/README.md#python-implementation)

## Other accomplishments

### From stochastic reachability to deterministic mean payoff

While looking for a hardness reduction for affine-market clearing, we found a way to turn a simple stochastic reachability game and a rational threshold into one deterministic mean-payoff game in polynomial time. The reduction preserves the threshold answer at equality and for games with nonterminating plays. Lean proves that the binary compiler preserves that answer and that its execution has polynomial bit cost under the stated model. This is the reverse reduction described as open in the October 2026 seminar. [Manuscript (PDF)](papers/H4-stochastic-to-mean-payoff.pdf) · [Original proof and Python replay (PR #10)](notes/H4-ssg-to-mean-payoff.md) · [Current Lean theorem and replay](lean/README.md#stochastic-game-reduction) · [October seminar](https://mimuw.edu.pl/en/seminars/talk/quasipolynomial-algorithms-for-mean-payoff-and-simple-stochastic-games/)

### Fixed-flow continuation lower bound

The November 21 paper constructs Bayesian simple security games in which following the defender's budget with a fixed attack flow per step requires superpolynomially many steps. An assignment and a feasibility LP compute an exact equilibrium at the final budget on the same family. Lean checks supporting lemmas, and exact Python replays check the small witnesses. [Paper (PDF)](papers/fixed-flow-continuation-lower-bound.pdf) · [TeX source](papers/fixed-flow-continuation-lower-bound.tex) · [Verification record](papers/fixed-flow-continuation-lower-bound-verification.md)

## State of the investigation when Kintali solved the problem

The sections below record where our investigation stood when Shiva Kintali solved the general equilibrium problem on November 24, 2026. They preserve the bounds and methods we had reached, with links to later checks and write-ups for the individual results.

**L1/L2** studies how equilibrium changes as the defender’s budget increases and which steps can be skipped. **A4** studies direct algorithms for exact market clearing and lower bounds for specific methods.

[**L1/L2 · Continuation complexity and shortcuts**](#open-l1l2-continuation-questions) · [**A4 · Direct market algorithms**](#open-a4-market-questions) · [Investigation archive](investigation/README.md) · [How to contribute](CONTRIBUTING.md)

### Open L1/L2 continuation questions

L1 describes the published continuation. L2 gives an exact implementation. Some games force superpolynomially many changes of attack flow, even when each step takes the largest possible jump at fixed flow. A general polynomial-time algorithm along this line would have to skip those changes. The questions below measure the cost of following the original path. [Lower bound and its scope](investigation/B3f.md) · [Exact upper bound](investigation/L2.md)

| Question | What would advance it | Join |
| --- | --- | --- |
| [L1a · Threshold drops](investigation/L1a.md) | Bound how often the threshold drops in one fixed-boundary phase for arbitrary binary priors and gains, or construct a run forcing many distinct thresholds. | [Issue #3](https://github.com/robbiemu/bayesian-simple-security-games/issues/3) |
| [L2a · Tight worst-case run length](investigation/L2a.md) | Narrow the gap between the superpolynomial number of steps forced on one run and the general upper bound. | [Issue #4](https://github.com/robbiemu/bayesian-simple-security-games/issues/4) |
| [L2b · Intermediate bit lengths](investigation/L2b.md) | Prove an input-only polynomial bit bound for the reduced fractions representing intermediate coverages and flows, or give a family requiring more. | [Issue #5](https://github.com/robbiemu/bayesian-simple-security-games/issues/5) |

### Open A4 market questions

Each buyer’s utility for a good is a decreasing affine function of its price, with a slope specific to that buyer and good. Exact clearing with binary rational data and exact security-game equilibrium are polynomial-time Turing equivalent. A4i recovers the minimum prices from one equilibrium of a game with one defender resource. Applying Kintali’s algorithm to that game settles the polynomial-time existence question. [A4i reverse reduction](investigation/A4i.md) · [Kintali’s short proof](https://shivakintali.github.io/papers/SecurityGames-short.pdf)

For one supplied market, the recovered minimum-price vector is the complete singleton candidate list requested in A4h5. [Supplied-capacity result](notes/A4h-supplied-capacity.md#one-exact-candidate-at-the-supplied-capacities) · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)

The A4 branches below study direct market algorithms. A4c recovers the original minimum from any clearing of an enlarged market. L4b recovers an exact game equilibrium at the requested budget with polynomially many clearing calls. [A4 question and certificate](investigation/A4.md) · [A4c supply perturbation](investigation/A4c.md) · [L4b budget recovery](investigation/L4b.md)

Unit-market search is also equivalent to exact equilibrium search in games with uniform priors and equal defender gains. A4i1 studies direct solvers for arbitrary affine slopes at unit quantities. [Unit-market equivalence](notes/A4i-market-to-game.md#jointly-uniform-games-and-unit-markets) · [Direct search question](investigation/A4i1.md)

**Conditional November bounds.** Under the pinned OpenAI fixed-point preprint, A4m takes polynomial bit time on markets passing an alternating-path LP or with a logarithmic-size vertex cover. The latter also covers explicitly supplied games with logarithmically many targets or positive-prior types. The written proof audit found support for these two transfers. The public Lean comparator covers rational LP, with distinct hypotheses for its related fixed-point material. An inverse-polynomial strict gap in the frozen-map certificate also suffices by ordinary iteration. [Source audit and exact dependencies](notes/A4m-november-source-audit.md)

The October route can search a smaller set when deleting it leaves balanced slopes. Its lattice transfers also give a feasible allocation, which an LP makes demand-optimal at repaired prices. [Structural fixed-point results](notes/A4m-structural-elimination.md) · [Integer transfer recovery](notes/A4m-discrete-contraction.md#recover-a-clearing-from-the-integer-transfers)

A4h9's projected Hall cut excludes a region of boundary quotes after a failed joint flow test, even as private prices and demand change. A4i1b's deletion-matching ascent is polynomial on cactus graphs and under logarithmic cycle rank per allowed-edge component of each deletion graph in the visited phases. A degree-three family forces superpolynomially many internal updates for that ascent in every buyer insertion order. Stable-flow scaling and a cutoff-separation test give further polynomial classes with binary quantities. [Projected Hall cuts](notes/A4h-two-port-hall-cuts.md) · [Unit-market methods](investigation/A4i1.md) · [Degree-three lower bound](notes/A4j-forced-deletion-switches.md#every-insertion-order-on-a-degree-three-subfamily) · [Stable-flow scaling](investigation/A4f3.md) · [Ordinal allocation](investigation/A4l.md)

| Question | What would advance it | Join |
| --- | --- | --- |
| [A4i1 · Direct unit-market solver](investigation/A4i1.md) | Give a direct market algorithm that computes minimum prices and a clearing assignment for one supplied unit market with arbitrary affine slopes in polynomial bit time. | [A4i1 node](investigation/A4i1.md) |
| [A4h · Direct candidate-price search](investigation/A4h.md) | Find a polynomial-bit-time direct rule for choosing which affine region to query next. | [Candidate generation](investigation/A4h.md) |
| [A4e · Reweighted covering LP](investigation/A4e.md) | Each iteration costs polynomial work. Prove a polynomial bound on the number of iterations or construct a family forcing a superpolynomial run for this rule. | [Issue #2](https://github.com/robbiemu/bayesian-simple-security-games/issues/2) |
| [A4f · Complementarity formulation](investigation/A4f.md) | Find an equivalent formulation with polynomially bounded handicap, the parameter controlling the Newton iteration bound. Show that solving it and recovering an exact equilibrium take polynomial bit time. | [Contribute to A4f](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BA4f%5D+) |

A4d also reduces the game directly to one P-matrix linear complementarity problem, placing exact equilibrium search in **UniqueEOPL**. A polynomial-time solver for the instances produced by that reduction would settle the game question directly. [Direct game reduction](notes/A4d-p-matrix-complementarity.md)

Open the contribution form on any node to propose a question, post a competing approach, or share a negative result. Each record credits the people and tools involved. To check an existing result, replay the rational edge-revisit examples or audit the model-assisted fixed-flow proof. [Reproduction record](records/b550a724-e9aa-4fb3-9668-c0ca5c9e8142.md) · [Lower-bound audit](notes/B3g-lower-bound-audit.md)

[Who proposed each direction](DIRECTIONS.md) · [Proof map](PROOF-MAP.md) · [Investigation notes and resume points](TREE.md) · [Publication and source information](PUBLICATION.md) · [CC BY 4.0 writing and MIT code](LICENSE.md)

## Results at a glance

- **Superpolynomial continuation lower bound.** For certain games with $n$ targets and $n$ uniformly likely types, varying the defender budget to one forces $n^{\Omega(\log n)}$ distinct attack flows in a single fixed-threshold, fixed-total phase. The bound applies to the published continuation and to jumps that maximize coverage while holding one attack flow fixed. At budget one those same games can be solved directly by an assignment problem and a feasibility LP. [Lower bound and scope](notes/B3f-forced-flow-switches.md)

- **Earlier subexponential upper bound.** The October ARRIVAL preprint's Theorem 1.2 and A4m's vertex-cover elimination give an exact Bayes–Nash equilibrium in $2^{O(\sqrt{\min(n,k)}\log(2+L))}\mathrm{poly}(L)$ bit time, with $n$ targets, $k$ positive-prior types and binary input length $L$. For explicitly tabulated games this is at most $2^{O(L^{1/4}\log(2+L))}\mathrm{poly}(L)$. The proof covers weak payoff inequalities by rational perturbation and repair. [October block solver](https://arxiv.org/html/2610.28241v1#S1.Thmtheorem1.2) · [Market elimination and game bound](notes/A4m-discrete-contraction.md)
- **Continuation and enumeration bounds.** Each of these methods gives a $2^{O(\min(n,k)\log(nk+1))}\mathrm{poly}(L)$ bit bound. [Arrangement count](notes/B1-classify-run-lengths.md) · [Exact continuation](notes/L2-exact-arithmetic-audit.md)
- **Tractable structure.** Polynomial time suffices when each connected component of the graph of potentially optimal choices has a bounded number of types. There may be arbitrarily many components sharing one defender budget. A different polynomial-time case allows arbitrary attacker-loss slopes when the uncovered utilities can be written $a_{it}=A_i+d_{it}c_t$ for type offsets $A_i$ and target offsets $c_t$. [Component composition](notes/B2-component-composition.md) · [Exact log-price algorithm](notes/A3-mixed-offsets.md)
- **Prior partials.** The supplied collection already gives the fixed-type arrangement, the rank-one algorithm, the threshold ordering used in component composition, and the affine rent-division correspondence. The review records the evidence for its approximation argument and a zero-threshold endpoint correction for its rank-one algorithm. [Prior research collection](sources/prior-collection.md) · [Partial-results review](notes/L3-prior-partials.md)

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
