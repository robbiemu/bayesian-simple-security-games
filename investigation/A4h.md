<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# A4h · Generate complete candidate lists before the Hall search

**🟦 Open**

A4h5 obtains a singleton list via A4i and Kintali's algorithm. For direct affine-region search, polynomially many adaptive queries suffice in the abstract and selecting them efficiently remains open.

**Open task** — Give a polynomial-bit-time direct rule to choose the next affine region on an unrestricted supplied market.

[Read the evidence](../notes/A4h-complete-candidate-generation.md#polynomially-many-queries-are-possible) · [Investigation index](README.md)

Parent question · [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md)

## Subquestions

- [A4h1 · Compose exact price breakpoints across one-good separators](A4h1.md) · 🟩 Result for the stated scope
- [A4h2 · Test fixed libraries and complete parametric tables](A4h2.md) · 🟩 Result for the stated scope
- [A4h3 · Use contraction queries, load corrections, and price transforms](A4h3.md) · 🟨 Partial result
- [A4h4 · Count capacity-price intervals and boundary-load drops](A4h4.md) · 🟩 Result for the stated scope
- [A4h5 · Generate complete candidates using the supplied capacities](A4h5.md) · 🟩 Result for the stated scope · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h6 · Jump to new demand ties using alternating forests](A4h6.md) · 🟨 Partial result · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h7 · Find and contract forced price relations](A4h7.md) · 🟨 Partial result · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h8 · Preserve completions when discarding partial solutions](A4h8.md) · 🟨 Partial result · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h9 · Combine price jumps, certified ties, and boundary load queries](A4h9.md) · 🟨 Partial result · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h10 · Search synchronized boundary quotes and test persistent ties](A4h10.md) · 🟩 Result for the stated scope · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h11 · Combine common-offset cores and heterogeneous conditional solvers](A4h11.md) · 🟩 Result for the stated scope · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)
- [A4h12 · Use one-good block solvers for shared buyers and goods](A4h12.md) · 🟩 Result for the stated scope · [Issue #1](https://github.com/robbiemu/bayesian-simple-security-games/issues/1)

## Relevant work

- A4h **uses** [A4g3 · Generate and search price lists from anchored paths](A4g3.md). The Hall search finishes once each supplied list contains its true price. [Evidence](../notes/A4h-complete-candidate-generation.md#polynomially-many-queries-are-possible)
- [A4h2 · Test fixed libraries and complete parametric tables](A4h2.md) **limits** A4h. A fixed input-independent library can miss a required formula. [Evidence](../notes/A4h-complete-candidate-generation.md#limits-on-complete-tables-and-fixed-formulas)
- [A4m · Transfer max-norm and lattice fixed-point algorithms to affine markets](A4m.md) **tests the search interface of** A4h. Identical local formulas can require opposite labels and different solution regions, so a single local evaluation cannot select the correct region. [Evidence](../notes/A4m-extremal-price-interface.md#identical-local-formulas-and-opposite-required-signs)

## Where the direction came from

- Robert Thomas Collins · [Require a short list that contains a solution](../DIRECTIONS.md#direction-shortlist) · Research direction

## Contributions elsewhere that cite this work

- [Certify exact polynomial-time clearing with a path bound on frozen prices](../records/e3aa26cd-1de3-424f-97c3-82db725e63cf.md)

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BA4h%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BA4h%5D+) · [Contributor guide](../CONTRIBUTING.md)
