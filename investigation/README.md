<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# Investigation index

Choose an open question to see its evidence, the reason for each connection, work already tried, and how to contribute.

## Open questions

- [L1a · Count strict threshold drops within one fixed-boundary phase](L1a.md) — For arbitrary binary priors and gains, bound the number of strict Algorithm 4 threshold drops while the open boundary is fixed, or construct one run forcing many distinct successful thresholds. · [Issue #3](https://github.com/robbiemu/bayesian-simple-security-games/issues/3)
- [L2a · Tighten the worst-case outer-call count on a single run](L2a.md) — Improve either bound using comparable dimensions, binary input sizes and tie rules. For a restricted class, identify the additional hypothesis. · [Issue #4](https://github.com/robbiemu/bayesian-simple-security-games/issues/4)
- [L2b · Bound intermediate rational bit lengths by the original input size](L2b.md) — Bound the bit lengths of the reduced numerators and denominators of every retained coverage and flow by a polynomial in the original input length, or exhibit a family exceeding every such bound under specified optimizer choices. · [Issue #5](https://github.com/robbiemu/bayesian-simple-security-games/issues/5)
- [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md) — Find a polynomial-bit-time algorithm returning any clearing equilibrium for arbitrary positive pair-specific slopes. Apply the [supply perturbation in A4c](A4c.md) to recover the minimum prices.
- [A4e · Test covering LPs with reweighting and Hall cuts](A4e.md) — Bound the number of iterations polynomially or construct a family forcing superpolynomially many for the stated rule. · [Issue #2](https://github.com/robbiemu/bayesian-simple-security-games/issues/2)
- [A4f · Seek a polynomial-handicap formulation for A4d](A4f.md) — Construct an equivalent bounded-handicap formulation with exact polynomial-time recovery.
- [A4h · Generate complete candidate lists before the Hall search](A4h.md) — Give a polynomial-bit-time rule to choose the next region on an unrestricted supplied market.
- [A4h5 · Generate complete candidates using the supplied capacities](A4h5.md) — Generate a polynomial-size list guaranteed to contain the minimum price in every coordinate of one supplied market, in time polynomial in its binary input length. · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [H1 · Pin down compact complexity and certificate bounds](H1.md) — Strengthen a general upper or lower bound under the explicit rational encoding.
- [H2 · Test a structural conjecture or a candidate hardness reduction](H2.md) — State a precise conjecture or reduction and show which exact equilibrium problem it addresses.
- [2cda0f31-ecad-4bb0-b12e-b040dafa66cd · Independently check the projected-price argument for the October auction](2cda0f31-ecad-4bb0-b12e-b040dafa66cd.md) — Check whether projection from transaction prices to good prices preserves the required Hall inequality throughout every auction step, and whether the piece count implies the stated iteration lower bound. Give a proof or identify a failing step.

## Partial results with open work

- [L4 · Compare the Newton bound with the continuation landscape](L4.md) — Use a general polynomial-time clearing method to make the threshold recovery unconditional.
- [B3 · Bound progress with overlapping types](B3.md) — Find a tighter worst-case bound or a broader tractable class with a stated structural assumption.
- [B3d · Compose groups that share targets](B3d.md) — Determine which budget and flow relations compose over a tree of small separators.
- [A4f2 · Construct equivalent buyer–good formulations](A4f2.md) — Find the right support or a global formulation in polynomial time.
- [A4g · Test bounded search and shortcuts in the implicit basis graph](A4g.md) — Give a complete polynomial-time choice of guesses or prove tractability for a wider class.
- [A4g3 · Generate and search price lists from anchored paths](A4g3.md) — Generate complete short lists without enumerating all anchored paths in a general market.
- [A4h3 · Use contraction queries, load corrections, and price transforms](A4h3.md) — Remove or weaken the normalization assumptions while retaining completeness.
- [A4h6 · Jump to new demand ties using alternating forests](A4h6.md) — Bound a stronger shortcut on general inputs, or identify another class with polynomially many jumps. · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h7 · Find and contract forced price relations](A4h7.md) — Find enough forced relations in polynomial time without enumerating a large disjunction. · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h8 · Preserve completions when discarding partial solutions](A4h8.md) — Find the boundary prices and buyer utilities efficiently for broader separator classes. · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)

## Full tree

- [R · Exact equilibrium in polynomial time](R.md) · 🟦 Open
  - [L · Published results and algorithm](L.md) · Background
    - [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md) · 🟩 Result for the stated scope
      - [L1a · Count strict threshold drops within one fixed-boundary phase](L1a.md) · 🟦 Open
    - [L2 · Account for exact arithmetic along a run](L2.md) · 🟩 Result for the stated scope
      - [L2a · Tighten the worst-case outer-call count on a single run](L2a.md) · 🟦 Open
      - [L2b · Bound intermediate rational bit lengths by the original input size](L2b.md) · 🟦 Open
    - [L3 · Check the prior partial results and reconcile overlap](L3.md) · Background
    - [L4 · Compare the Newton bound with the continuation landscape](L4.md) · 🟨 Partial result
      - [L4a · Apply the handicap-dependent theorem to A4d](L4a.md) · 🟩 Result for the stated scope
      - [L4b · Transfer market endpoints and exact threshold search to L1/L2](L4b.md) · 🟩 Result for the stated scope
  - [B · Worst-case run length by instance class](B.md) · Background
    - [B1 · Define a restricted Busy Beaver and test a state classification](B1.md) · 🟩 Result for the stated scope
    - [B2 · Combine independent preference components at one threshold](B2.md) · 🟩 Result for the stated scope
    - [B3 · Bound progress with overlapping types](B3.md) · 🟨 Partial result
      - [B3a · Jump across steps that preserve an attack flow](B3a.md) · 🟩 Result for the stated scope
      - [B3b · Count progress in closed reachable groups](B3b.md) · 🟩 Result for the stated scope
      - [B3c · Search for long runs with exact arithmetic](B3c.md) · 🟩 Result for the stated scope
      - [B3d · Compose groups that share targets](B3d.md) · 🟨 Partial result
      - [B3e · Embed a parametric path in one unchanged flow](B3e.md) · 🟩 Result for the stated scope
      - [B3f · Force many flow switches at uniform margins](B3f.md) · 🟩 Result for the stated scope
      - [B3g · Independently check the forced-switch proof](B3g.md) · 🟩 Result for the stated scope
  - [A · Alternative exact algorithms](A.md) · Background
    - [A1 · Use payoff thresholds and capacitated transport](A1.md) · 🟩 Result for the stated scope
    - [A2 · Solve the common-intercept class by logarithmic price changes](A2.md) · 🟩 Result for the stated scope
    - [A3 · Extend the log-price algorithm to arbitrary common offsets](A3.md) · 🟩 Result for the stated scope
    - [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md) · 🟦 Open
      - [A4a · Test contraction near factorized slopes](A4a.md) · 🟩 Result for the stated scope
      - [A4b · Seek direct search through Hall inequalities](A4b.md) · 🟩 Result for the stated scope
      - [A4c · Reduce minimum-price search to any clearing equilibrium](A4c.md) · 🟩 Result for the stated scope
      - [A4d · Reduce market and game equilibrium to P-matrix complementarity](A4d.md) · 🟩 Result for the stated scope
      - [A4e · Test covering LPs with reweighting and Hall cuts](A4e.md) · 🟦 Open
        - [A4e1 · Identify when one weighted cover gives an unweighted flow](A4e1.md) · 🟩 Result for the stated scope
        - [A4e2 · Test cuts across changing demand graphs](A4e2.md) · 🟩 Result for the stated scope
        - [A4e3 · Prove strict descent and solve common-offset markets](A4e3.md) · 🟩 Result for the stated scope
      - [A4f · Seek a polynomial-handicap formulation for A4d](A4f.md) · 🟦 Open
        - [A4f1 · Test scaling, regularization and active-set conditioning](A4f1.md) · 🟩 Result for the stated scope
        - [A4f2 · Construct equivalent buyer–good formulations](A4f2.md) · 🟨 Partial result
      - [A4g · Test bounded search and shortcuts in the implicit basis graph](A4g.md) · 🟨 Partial result
        - [A4g1 · Solve selected affine regions and bracket their signs](A4g1.md) · 🟩 Result for the stated scope
        - [A4g2 · Bound breadth-first and all-ones Lemke searches](A4g2.md) · 🟩 Result for the stated scope
        - [A4g3 · Generate and search price lists from anchored paths](A4g3.md) · 🟨 Partial result
      - [A4h · Generate complete candidate lists before the Hall search](A4h.md) · 🟦 Open
        - [A4h1 · Compose exact price breakpoints across one-good separators](A4h1.md) · 🟩 Result for the stated scope
        - [A4h2 · Test fixed libraries and complete parametric tables](A4h2.md) · 🟩 Result for the stated scope
        - [A4h3 · Use contraction queries, load corrections, and price transforms](A4h3.md) · 🟨 Partial result
        - [A4h4 · Count capacity-price intervals and boundary-load drops](A4h4.md) · 🟩 Result for the stated scope
        - [A4h5 · Generate complete candidates using the supplied capacities](A4h5.md) · 🟦 Open
        - [A4h6 · Jump to new demand ties using alternating forests](A4h6.md) · 🟨 Partial result
        - [A4h7 · Find and contract forced price relations](A4h7.md) · 🟨 Partial result
        - [A4h8 · Preserve completions when discarding partial solutions](A4h8.md) · 🟨 Partial result
      - [2cda0f31-ecad-4bb0-b12e-b040dafa66cd · Independently check the projected-price argument for the October auction](2cda0f31-ecad-4bb0-b12e-b040dafa66cd.md) · 🟦 Open
  - [H · Complexity and counterexamples](H.md) · Background
    - [H1 · Pin down compact complexity and certificate bounds](H1.md) · 🟦 Open
    - [H2 · Test a structural conjecture or a candidate hardness reduction](H2.md) · 🟦 Open

[Diagram of the tree](DIAGRAM.md) · [Mathematical proof map](../PROOF-MAP.md) · [Direction and credit catalog](../DIRECTIONS.md)
