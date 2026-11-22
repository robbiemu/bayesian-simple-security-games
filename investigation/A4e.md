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
- [A4h11 · Combine common-offset cores and heterogeneous conditional solvers](A4h11.md) **uses** A4e. Common offsets allow a monotone transformation before near-factorized core solves. [Evidence](../notes/A4h-core-composition-closures.md#transform-only-the-core)

## Where the direction came from

- Robert Thomas Collins · [Try fractional bipartite covering](../DIRECTIONS.md#direction-cover) · Stated intuition and research brief

## Contributions elsewhere that cite this work

- [Clear a common-offset core with heterogeneous single-vertex branches](../records/050f6342-7cce-48ec-b308-036810d0c200.md)
- [Clear a common-offset core with heterogeneous single-vertex branches](../records/e1fcfa01-8d57-4849-b50f-d8773258ea1e.md)

## Contribution log

- [Test a fractional-cover LP against unweighted clearance](../records/d995764c-0859-4256-adfa-f89596cc04ab.md) · attempt · started · Robert Thomas Collins
- [Finish the covering-LP research pass](../records/89dc2dfb-d879-4c18-9103-191dd80ef0ed.md) · attempt · finished · OpenAI Codex · GPT-6.2 Sol
- [Reweight the covering LP and test strict descent](../records/bdb46275-3976-4076-b365-431d7784b1bc.md) · result · partial · Robert Thomas Collins, OpenAI Codex · GPT-6.2 Astra, GPT-6.2 Sol, Python

[Join the discussion in issue #2](https://github.com/robbiemu/bayesian-simple-security-games/issues/2) · [Find other discussions](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BA4e%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BA4e%5D+) · [Contributor guide](../CONTRIBUTING.md)
