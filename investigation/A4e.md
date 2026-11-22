<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# A4e · Test covering LPs with reweighting and Hall cuts

**🟦 Open**

Reweighted cover LPs descend exactly. Each iteration costs polynomial work. The known general iteration bound is exponential.

**Open task** — Bound the number of iterations polynomially or construct a family forcing superpolynomially many for the stated rule.

[Read the evidence](../notes/A4e-covering-lp.md) · [Investigation index](README.md)

Parent question · [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md)

## Subquestions

- [A4e1 · Identify when one weighted cover gives an unweighted flow](A4e1.md) · 🟩 Result for the stated scope
- [A4e2 · Test cuts across changing demand graphs](A4e2.md) · 🟩 Result for the stated scope
- [A4e3 · Prove strict descent and solve common-offset markets](A4e3.md) · 🟩 Result for the stated scope

## Relevant work

- [A4e1 · Identify when one weighted cover gives an unweighted flow](A4e1.md) **limits** A4e. Weighted capacity use in the LP dual differs from the physical flow requirement. [Evidence](../notes/A4e-covering-lp.md#the-weighted-dual-can-miss-clearance)
- [A4e2 · Test cuts across changing demand graphs](A4e2.md) **limits** A4e. Changing the tight graph can invalidate a proposed global cut. [Evidence](../notes/A4e-covering-lp.md#failed-hall-tests-and-linear-cuts)
- [A4e3 · Prove strict descent and solve common-offset markets](A4e3.md) **answers part of** A4e. Strict descent establishes termination with polynomial work at each step. [Evidence](../notes/A4e-covering-lp.md#an-exact-descent-rule)

## Where the direction came from

- Robert Thomas Collins · [Try fractional bipartite covering](../DIRECTIONS.md#direction-cover) · Stated intuition and research brief

## Contribution log

- [Test a fractional-cover LP against unweighted clearance](../records/d995764c-0859-4256-adfa-f89596cc04ab.md) · attempt · started · Robert Thomas Collins

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BA4e%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BA4e%5D+) · [Contributor guide](../CONTRIBUTING.md)
