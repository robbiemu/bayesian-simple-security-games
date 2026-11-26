<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# Investigation index

Choose an open question to see its evidence, the reason for each connection, work already tried, and how to contribute.

## Open questions

- [L2a · Tighten the worst-case outer-call count on a single run](L2a.md) — Improve either bound using comparable dimensions, binary input sizes and tie rules. For a restricted class, identify the additional hypothesis. · [Issue #4](https://github.com/robbiemu/bayesian-simple-security-games/issues/4)
- [A4f · Seek a polynomial-handicap formulation for A4d](A4f.md) — Construct an equivalent bounded-handicap formulation with exact polynomial-time recovery.
- [A4h · Generate complete candidate lists before the Hall search](A4h.md) — Give a polynomial-bit-time direct rule to choose the next affine region on an unrestricted supplied market.
- [A4i1 · Find the exact minimum prices of one supplied unit market](A4i1.md) — Find a direct polynomial-bit-time market solver with arbitrary affine slopes and recover a clearing assignment. The degree-three reduction gives a sufficient restricted problem.
- [H1 · Pin down compact complexity and certificate bounds](H1.md) — Strengthen a general upper or lower bound under the explicit rational encoding.
- [H2 · Test a structural conjecture or a candidate hardness reduction](H2.md) — State a precise conjecture or reduction and show which exact equilibrium problem it addresses.
- [2cda0f31-ecad-4bb0-b12e-b040dafa66cd · Independently check the projected-price argument for the October auction](2cda0f31-ecad-4bb0-b12e-b040dafa66cd.md) — Check whether projection from transaction prices to good prices preserves the required Hall inequality throughout every auction step, and whether the piece count implies the stated iteration lower bound. Give a proof or identify a failing step.
- [3244b26a-6160-43e2-9b81-1650d78dd4cb · Reduce simple stochastic games to deterministic mean-payoff games](3244b26a-6160-43e2-9b81-1650d78dd4cb.md) — Give a single-instance polynomial-bit-time reduction preserving the weak threshold comparison from explicitly encoded fair-coin reachability games to deterministic integer-weighted mean-payoff games, including nonabsorbing plays.

## Partial results with open work

- [R · Exact equilibrium in polynomial time](R.md) — Complete the runtime refinement to the finite machine required by the public Lean statement.
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
- [A4h9 · Combine price jumps, certified ties, and boundary load queries](A4h9.md) — Find a polynomial-bit-time rule that combines projected Hall cuts and price-relation certificates to search independently quoted ports. · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4m · Transfer max-norm and lattice fixed-point algorithms to affine markets](A4m.md) — Find a polynomial-time block search for the resulting integer maps or a polynomial-size max-norm formulation for general markets.

## Full tree

- [R · Exact equilibrium in polynomial time](R.md) · 🟨 Partial result
  - [L · Published results and algorithm](L.md) · Background
    - [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md) · 🟩 Result for the stated scope
      - [L1a · Count strict threshold drops within one fixed-boundary phase](L1a.md) · 🟩 Result for the stated scope
    - [L2 · Account for exact arithmetic along a run](L2.md) · 🟩 Result for the stated scope
      - [L2a · Tighten the worst-case outer-call count on a single run](L2a.md) · 🟦 Open
      - [L2b · Bound intermediate rational bit lengths by the original input size](L2b.md) · 🟩 Result for the stated scope
    - [L3 · Check the prior partial results and reconcile overlap](L3.md) · Background
    - [L4 · Compare the Newton bound with the continuation landscape](L4.md) · 🟨 Partial result
      - [L4a · Apply the handicap-dependent theorem to A4d](L4a.md) · 🟩 Result for the stated scope
      - [L4b · Transfer market endpoints and exact threshold search to L1/L2](L4b.md) · 🟩 Result for the stated scope
      - [L4c · Use structure at one answer endpoint and test reusable price lists](L4c.md) · 🟩 Result for the stated scope
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
    - [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md) · 🟩 Result for the stated scope
      - [A4a · Test contraction near factorized slopes](A4a.md) · 🟩 Result for the stated scope
      - [A4b · Seek direct search through Hall inequalities](A4b.md) · 🟩 Result for the stated scope
      - [A4c · Reduce minimum-price search to any clearing equilibrium](A4c.md) · 🟩 Result for the stated scope
      - [A4d · Reduce market and game equilibrium to P-matrix complementarity](A4d.md) · 🟩 Result for the stated scope
      - [A4e · Test covering LPs with reweighting and Hall cuts](A4e.md) · 🟩 Result for the stated scope
        - [A4e1 · Identify when one weighted cover gives an unweighted flow](A4e1.md) · 🟩 Result for the stated scope
        - [A4e2 · Test cuts across changing demand graphs](A4e2.md) · 🟩 Result for the stated scope
        - [A4e3 · Prove strict descent and solve common-offset markets](A4e3.md) · 🟩 Result for the stated scope
      - [A4f · Seek a polynomial-handicap formulation for A4d](A4f.md) · 🟦 Open
        - [A4f1 · Test scaling, regularization and active-set conditioning](A4f1.md) · 🟩 Result for the stated scope
        - [A4f2 · Construct equivalent buyer–good formulations](A4f2.md) · 🟨 Partial result
        - [A4f3 · Scale price precision with stable flows at physical quotas](A4f3.md) · 🟩 Result for the stated scope
      - [A4g · Test bounded search and shortcuts in the implicit basis graph](A4g.md) · 🟨 Partial result
        - [A4g1 · Solve selected affine regions and bracket their signs](A4g1.md) · 🟩 Result for the stated scope
        - [A4g2 · Bound breadth-first and all-ones Lemke searches](A4g2.md) · 🟩 Result for the stated scope
        - [A4g3 · Generate and search price lists from anchored paths](A4g3.md) · 🟨 Partial result
      - [A4h · Generate complete candidate lists before the Hall search](A4h.md) · 🟦 Open
        - [A4h1 · Compose exact price breakpoints across one-good separators](A4h1.md) · 🟩 Result for the stated scope
        - [A4h2 · Test fixed libraries and complete parametric tables](A4h2.md) · 🟩 Result for the stated scope
        - [A4h3 · Use contraction queries, load corrections, and price transforms](A4h3.md) · 🟨 Partial result
        - [A4h4 · Count capacity-price intervals and boundary-load drops](A4h4.md) · 🟩 Result for the stated scope
        - [A4h5 · Generate complete candidates using the supplied capacities](A4h5.md) · 🟩 Result for the stated scope
        - [A4h6 · Jump to new demand ties using alternating forests](A4h6.md) · 🟨 Partial result
        - [A4h7 · Find and contract forced price relations](A4h7.md) · 🟨 Partial result
        - [A4h8 · Preserve completions when discarding partial solutions](A4h8.md) · 🟨 Partial result
        - [A4h9 · Combine price jumps, certified ties, and boundary load queries](A4h9.md) · 🟨 Partial result
        - [A4h10 · Search synchronized boundary quotes and test persistent ties](A4h10.md) · 🟩 Result for the stated scope
        - [A4h11 · Combine common-offset cores and heterogeneous conditional solvers](A4h11.md) · 🟩 Result for the stated scope
        - [A4h12 · Use one-good block solvers for shared buyers and goods](A4h12.md) · 🟩 Result for the stated scope
      - [A4i · Reduce affine market clearing to one-resource security games](A4i.md) · 🟩 Result for the stated scope
        - [A4i1 · Find the exact minimum prices of one supplied unit market](A4i1.md) · 🟦 Open
          - [A4i1a · Solve degree-two unit markets by conditional Hall tests](A4i1a.md) · 🟩 Result for the stated scope
          - [A4i1b · Bound exact ascent by deletion-matching products](A4i1b.md) · 🟩 Result for the stated scope
          - [A4i1c · Reduce arbitrary unit markets to degree three](A4i1c.md) · 🟩 Result for the stated scope
          - [A4i1d · Find support through multiplier lists and price boxes](A4i1d.md) · 🟩 Result for the stated scope
      - [A4l · Find exact clearing through ordinal stable allocation](A4l.md) · 🟩 Result for the stated scope
      - [A4m · Transfer max-norm and lattice fixed-point algorithms to affine markets](A4m.md) · 🟨 Partial result
      - [2cda0f31-ecad-4bb0-b12e-b040dafa66cd · Independently check the projected-price argument for the October auction](2cda0f31-ecad-4bb0-b12e-b040dafa66cd.md) · 🟦 Open
  - [H · Complexity and counterexamples](H.md) · Background
    - [H1 · Pin down compact complexity and certificate bounds](H1.md) · 🟦 Open
    - [H2 · Test a structural conjecture or a candidate hardness reduction](H2.md) · 🟦 Open
    - [3244b26a-6160-43e2-9b81-1650d78dd4cb · Reduce simple stochastic games to deterministic mean-payoff games](3244b26a-6160-43e2-9b81-1650d78dd4cb.md) · 🟦 Open

[Diagram of the tree](DIAGRAM.md) · [Mathematical proof map](../PROOF-MAP.md) · [Direction and credit catalog](../DIRECTIONS.md)
