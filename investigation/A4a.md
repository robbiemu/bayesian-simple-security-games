<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# A4a · Test contraction near factorized slopes

**🟩 Result for the stated scope**

Uses contraction to recover exact minimum prices when slopes are sufficiently near factorized.

[Read the evidence](../notes/A4a-near-factorized-slopes.md) · [Investigation index](README.md)

Parent question · [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md)

## Relevant work

- A4a **answers part of** [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md). Near-factorized slopes admit direct contraction. [Evidence](../notes/A4a-near-factorized-slopes.md)
- [L4b · Transfer market endpoints and exact threshold search to L1/L2](L4b.md) **uses** A4a. The embedded hard trajectory has near-factorized slopes at a fixed budget. [Evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)
- [A4h3 · Use contraction queries, load corrections, and price transforms](A4h3.md) **uses** A4a. A near-factorized contraction recovers an exact candidate. [Evidence](../notes/A4h-complete-candidate-generation.md#guess-aggregate-slope-corrections)
- [A4h5 · Generate complete candidates using the supplied capacities](A4h5.md) **uses** A4a. Contraction solves the near-factorized core at the supplied capacity. [Evidence](../notes/A4h-supplied-capacity.md#query-branch-loads-at-selected-prices)
- [A4h11 · Combine common-offset cores and heterogeneous conditional solvers](A4h11.md) **uses** A4a. Column sensitivity controls the frozen map after the transformation. [Evidence](../notes/A4h-core-composition-closures.md#exact-surrogate-and-exact-repair)
- [A4m · Transfer max-norm and lattice fixed-point algorithms to affine markets](A4m.md) **extends** A4a. The path-based factor LP certifies additional frozen assignment maps, and the original tie repair returns the minimum. [Evidence](../notes/A4m-path-sensitive-freezing.md)

## Where the direction came from

- Robert Thomas Collins · [Switch from tracing the path to the market oracle](../DIRECTIONS.md#direction-pivot) · Selection of direction

## Contributions elsewhere that cite this work

- [Clear a common-offset core with heterogeneous single-vertex branches](../records/050f6342-7cce-48ec-b308-036810d0c200.md)
- [Clip branch loads and query just the supplied capacity](../records/6857a320-2a84-432c-ae71-c8322042dbcf.md)
- [Clear a common-offset core with heterogeneous single-vertex branches](../records/e1fcfa01-8d57-4849-b50f-d8773258ea1e.md)
- [Certify exact polynomial-time clearing with a path bound on frozen prices](../records/e3aa26cd-1de3-424f-97c3-82db725e63cf.md)

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BA4a%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BA4a%5D+) · [Contributor guide](../CONTRIBUTING.md)
