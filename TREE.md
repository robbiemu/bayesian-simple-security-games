# Investigation tree for Bayesian simple security games

**Root question.** Given rational utilities and type probabilities in the explicitly enumerated model, is there a polynomial-time algorithm for an exact Bayes–Nash equilibrium? [Conitzer, arXiv:2610.08796](https://arxiv.org/pdf/2610.08796)

[Color-coded proof map](PROOF-MAP.md)

```text
R    Exact equilibrium in polynomial time
├── L    Published results and algorithm
│   ├── L1   Locate the exact algorithm and its worst-case bottleneck
│   │   └── L1a  Count strict threshold drops within one fixed-boundary phase
│   ├── L2   Account for exact arithmetic along a run
│   │   ├── L2a  Tighten the worst-case outer-call count on a single run
│   │   └── L2b  Bound intermediate rational bit lengths by the original input size
│   ├── L3   Check the prior partial results and reconcile overlap
│   └── L4   Compare the Newton bound with the continuation landscape
│       ├── L4a  Apply the handicap-dependent theorem to A4d
│       ├── L4b  Transfer market endpoints and exact threshold search to L1/L2
│       └── L4c  Use structure at one answer endpoint and test reusable price lists
├── B    Worst-case run length by instance class
│   ├── B1   Define a restricted Busy Beaver and test a state classification
│   ├── B2   Combine independent preference components at one threshold
│   └── B3   Bound progress with overlapping types
│       ├── B3a  Jump across steps that preserve an attack flow
│       ├── B3b  Count progress in closed reachable groups
│       ├── B3c  Search for long runs with exact arithmetic
│       ├── B3d  Compose groups that share targets
│       ├── B3e  Embed a parametric path in one unchanged flow
│       ├── B3f  Force many flow switches at uniform margins
│       └── B3g  Independently check the forced-switch proof
├── A    Alternative exact algorithms
│   ├── A1   Use payoff thresholds and capacitated transport
│   ├── A2   Solve the common-intercept class by logarithmic price changes
│   ├── A3   Extend the log-price algorithm to arbitrary common offsets
│   └── A4   Solve the binary-mass minimum-price market with arbitrary slopes
│       ├── A4a  Test contraction near factorized slopes
│       ├── A4b  Seek direct search through Hall inequalities
│       ├── A4c  Reduce minimum-price search to any clearing equilibrium
│       ├── A4d  Reduce market and game equilibrium to P-matrix complementarity
│       ├── A4e  Test covering LPs with reweighting and Hall cuts
│       │   ├── A4e1  Identify when one weighted cover gives an unweighted flow
│       │   ├── A4e2  Test cuts across changing demand graphs
│       │   └── A4e3  Prove strict descent and solve common-offset markets
│       ├── A4f  Seek a polynomial-handicap formulation for A4d
│       │   ├── A4f1  Test scaling, regularization and active-set conditioning
│       │   ├── A4f2  Construct equivalent buyer–good formulations
│       │   └── A4f3  Scale price tolerances through stable price contracts
│       ├── A4g  Test bounded search and shortcuts in the implicit basis graph
│       │   ├── A4g1  Solve selected affine regions and bracket their signs
│       │   ├── A4g2  Bound breadth-first and all-ones Lemke searches
│       │   └── A4g3  Generate and search price lists from anchored paths
│       ├── A4h  Generate complete candidate lists before the Hall search
│       │   ├── A4h1  Compose exact price breakpoints across one-good separators
│       │   ├── A4h2  Test fixed libraries and complete parametric tables
│       │   ├── A4h3  Use contraction queries, load corrections, and price transforms
│       │   ├── A4h4  Count capacity-price intervals and boundary-load drops
│       │   ├── A4h5  Generate complete candidates using the supplied capacities
│       │   ├── A4h6  Jump to new demand ties using alternating forests
│       │   ├── A4h7  Find and contract forced price relations
│       │   ├── A4h8  Preserve completions when discarding partial solutions
│       │   ├── A4h9  Combine price jumps, certified ties, and boundary load queries
│       │   ├── A4h10  Search synchronized boundary quotes and test persistent ties
│       │   ├── A4h11  Combine common-offset cores and heterogeneous conditional solvers
│       │   └── A4h12  Use one-good block solvers for shared buyers and goods
│       ├── A4i  Reduce affine market clearing to a one-resource game
│       │   └── A4i1  Find minimum prices in one supplied unit market
│       │       ├── A4i1a  Solve degree-two unit markets by conditional Hall tests
│       │       ├── A4i1b  Bound exact ascent by deletion-matching products
│       │       ├── A4i1c  Reduce arbitrary unit markets to degree three
│       │       └── A4i1d  Find support through multiplier lists and price boxes
│       ├── A4l  Find exact clearing through ordinal stable allocation
│       └── A4m  Apply fixed-point solvers and eliminate a vertex cover
│           ├── Certify frozen price maps by alternating-path LP bounds
│           └── Solve general affine markets by exact lattice block search
└── H    Complexity and counterexamples
    ├── H1   Pin down compact complexity and certificate bounds
    └── H2   Test a structural conjecture or a candidate hardness reduction
```

L1, A1, and B1 established the source baseline, exact certificate and classification. B2 uses the viable-choice graph from B1 and the threshold–flow formulation from A1. L2 supplies the non-repetition proof and exact arithmetic for the smaller count. L3 checks the [recovered collection of earlier drafts](sources/prior-collection.md) against those results. A2 and A3 use threshold ordering and exact log-flow comparisons to close a different payoff class.

| Node | Status | Evidence or test |
| --- | --- | --- |
| L1 | Complete | [Published phase bound and a fixed-phase edge revisit](notes/L1-published-algorithm.md) |
| A1 | Complete | [Exact flow test, fixed-type solver, and weak-sign repair](notes/A1-threshold-transport.md) |
| B1 | Complete | [Smaller sign arrangements and exact run lengths on independent blocks](notes/B1-classify-run-lengths.md) |
| B2 | Complete | [Compose component solvers at one shared threshold](notes/B2-component-composition.md) |
| L2 | Complete | [Prove non-repetition and subexponential exact bit time](notes/L2-exact-arithmetic-audit.md) |
| L3 | Complete | [Check prior partials and reduce the open question to a market oracle](notes/L3-prior-partials.md) |
| L4 | Exact oracle reduction and runtime comparison | [Newton solve counts, two-sided market endpoints, and continuation seed criterion](notes/L4-newton-and-continuation.md) |
| L4c | Polynomial search under either endpoint promise | [Threshold cuts, reciprocal endpoint, and exact library tests](notes/L4-structured-endpoints.md) |
| A2 | Complete | [Exact log-price solver for common intercepts](notes/A2-log-price-subclass.md) |
| A3 | Complete | [Exact solver for common affine offsets with weak signs](notes/A3-mixed-offsets.md) |
| B3 | Lower bound proved | [Superpolynomial fixed-flow continuation and tractable subclasses](notes/B3-overlapping-types.md) |
| B3a | Complete | [Fixed-flow jumps and a count by alternating cycles](notes/B3a-fixed-flow-jump.md) |
| B3b | Complete | [Closed reachable groups and finite cost levels](notes/B3b-closed-group-rank.md) |
| B3c | Complete | [Exact cost drops that reuse prior edges](notes/B3c-exact-path-search.md) |
| B3d | Complete | [Exact solver for groups with a small shared target set](notes/B3d-shared-target-separator.md) |
| B3e | Complete | [Long path with no attack-flow switch](notes/B3e-parametric-path-lower-bound.md) |
| B3f | Complete | [Superpolynomial number of forced flow switches](notes/B3f-forced-flow-switches.md) |
| B3g | Complete | [Independent checks of the forced-switch proof](notes/B3g-lower-bound-audit.md) |
| A4 | General polynomial time open | [Minimum-price certificate, subclasses, and auction lower bounds](notes/A4-minimum-price-markets.md) |
| A4a | Polynomial subclass | [Exact search for nearly factorized slope matrices](notes/A4a-near-factorized-slopes.md) |
| A4b | Polynomial subclasses | [Good elimination, bounded-depth graphs, and arbitrary forests](notes/A4b-direct-hall-search.md) |
| A4c | Reduction and upper bound proved | [One enlarged clearing market suffices; market and game search are in CLS](notes/A4c-any-clearing-equilibrium.md) |
| A4d | Upper bound proved | [One P-matrix LCP suffices; exact market and game search are in UniqueEOPL](notes/A4d-p-matrix-complementarity.md) |
| A4e | Exact descent and polynomial subclasses | [Covering LP counterexamples, Hall disjunctions, and a common-offset solver](notes/A4e-covering-lp.md) |
| A4f | General polynomial handicap open | [Scaling obstruction, exact reformulations, and binary recovery](notes/A4f-handicap-formulation.md) |
| A4f3 | Polynomial for bounded products of slope ratios | [Stable-flow scaling with binary quotas](investigation/A4f3.md) |
| A4g | Exact bounded searches and path lower bounds | [Anchor price lists, region solves, and a long Lemke line](notes/A4g-budgeted-support-search.md) |
| A4h | Polynomial subclasses and a query bound | [Complete candidate generation and limits on explicit lists](notes/A4h-complete-candidate-generation.md) |
| A4h4 | NP-hard count | [Corollary 1.8 audit and price-table reduction](notes/A4h-table-count-hardness.md) |
| A4h5 | Polynomial capacity-specific subclasses | [Hall counterexample, clipped loads, and core price queries](notes/A4h-supplied-capacity.md) |
| A4h6 | Finite ascent, polynomial subclasses, and step lower bounds | [Safe jumps, rational directions, and restricted Hall solves](notes/A4h-alternating-tree.md) |
| A4h7 | Exact contraction after certification | [Forced demand and trade, price groups, and disjunction limits](notes/A4h-forced-price-relations.md) |
| A4h8 | One representative at fixed quotes | [Shared goods and buyers, joint loads, and antichains](notes/A4h-boundary-dominance.md) |
| A4h9 | Exact relation tests and a polynomial subclass | [Grouped comparisons and safe restarts](notes/A4h-hybrid-jumps.md) · [Branches at shared buyers and goods](notes/A4h-mixed-port-composition.md) · [Projected Hall cuts](notes/A4h-two-port-hall-cuts.md) |
| A4h10 | Polynomial search with certified synchronized quotes | [Signed loads and persistent ties](notes/A4h-synchronized-ports.md) |
| A4h11 | Polynomial subclass and weak-sign transfer | [Offset cores and heterogeneous conditional solvers](notes/A4h-core-composition-closures.md) |
| A4h12 | Polynomial on bounded incidence blocks | [Buyer proxies, mixed articulations, and margin counts](notes/A4h-buyer-proxy.md) |
| A4i | Reverse reduction and unit-market equivalence proved | [One-resource reduction and jointly uniform games](notes/A4i-market-to-game.md) |
| A4i1 | General unit-market polynomial time open | [Supplied unit market with arbitrary affine slopes](investigation/A4i1.md) |
| A4i1a–b | Polynomial in degree two and additional graph or slope classes. Superpolynomial ascent lower bound at degree three. | [Conditional Hall search](investigation/A4i1a.md) · [Deletion components and cycle bounds](notes/A4j-deletion-matching-components.md) · [Forced switches](notes/A4j-forced-deletion-switches.md) |
| A4i1c | General unit market reduces to degree three | [Degree-three reduction](investigation/A4i1c.md) |
| A4i1d | Polynomial with a small multiplier-list product or fixed cycle-gain rank | [Representatives and price-box tests](investigation/A4i1d.md) |
| A4l | Polynomial with separated cutoffs at binary quotas | [Ordinal stable allocation](investigation/A4l.md) |
| A4m | October subexponential general bound and exact integer flow recovery. Conditional November polynomial bounds on certified classes. | [Fixed-point results](investigation/A4m.md) · [Source audit](notes/A4m-november-source-audit.md) |
| H1, H2 | Open | Analyze full complexity beyond threshold-zero selection and the matching and rent reductions |

## Resume points

The open continuation questions concern [strict threshold drops (L1a)](investigation/L1a.md), [tight single-run bounds (L2a)](investigation/L2a.md) and [input-only intermediate bit lengths (L2b)](investigation/L2b.md). Each node links to its discussion and the precise existing bound.

1. **A4.** Extend [A4h's capacity-specific queries](notes/A4h-supplied-capacity.md#query-branch-loads-at-selected-prices) beyond a near-factorized core, or find a polynomial-time selection rule for [general candidate regions](notes/A4h-complete-candidate-generation.md#polynomially-many-queries-are-possible). A global formulation from [A4f’s zero-handicap cells](notes/A4f-handicap-formulation.md#eliminating-flow-variables) or a polynomial iteration bound for [A4e’s reweighted covers](notes/A4e-covering-lp.md#an-exact-descent-rule) would also suffice. Exact clearing and game equilibrium now reduce to each other. At unit quantities, a polynomial algorithm would settle the jointly uniform game. [L4b budget decoder](notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle) · [A4i reverse reduction](investigation/A4i.md) · [Open unit-market search](investigation/A4i1.md)
2. **Structural composition.** The [shared-target solver](notes/B3d-shared-target-separator.md) composes arbitrarily many small groups across one common parameter vector. Test which budget and flow relations can be retained across a tree of small separators. The construction in [B3f](notes/B3f-forced-flow-switches.md) rules out a general polynomial count of fixed-flow segments even at uniform margins and a constant threshold.
