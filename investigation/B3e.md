<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# B3e · Embed a parametric path in one unchanged flow

**🟩 Result for the stated scope**

A parametric path gives many continuation changes even while one attack flow stays fixed.

[Read the evidence](../notes/B3e-parametric-path-lower-bound.md) · [Investigation index](README.md)

Parent question · [B3 · Bound progress with overlapping types](B3.md)

## Relevant work

- B3e **limits** [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md). Long runs can occur under a fixed-order continuation even with an unchanged flow. [Evidence](../notes/B3e-parametric-path-lower-bound.md)
- [B3f · Force many flow switches at uniform margins](B3f.md) **extends** B3e. The assignment construction forces changes of the flow itself. [Evidence](../notes/B3f-forced-flow-switches.md)
- [L1a · Count strict threshold drops within one fixed-boundary phase](L1a.md) **compares with** B3e. The tight Hall families can change while the source’s witness spans the entire boundary and Algorithm 4 never runs. [Evidence](../notes/B3e-parametric-path-lower-bound.md#hall-witnesses-at-the-same-threshold)
- [L2a · Tighten the worst-case outer-call count on a single run](L2a.md) **uses** B3e. A fixed source order can force a long path even though the attack assignment never changes. [Evidence](../notes/B3e-parametric-path-lower-bound.md#count-and-scope)

## Where the direction came from

- Robert Thomas Collins · [Classify the longest single continuation run](../DIRECTIONS.md#direction-busy) · Independently proposed framing
- Robert Thomas Collins · [Pursue the unresolved continuation case](../DIRECTIONS.md#direction-single) · Research direction

## Contributions elsewhere that cite this work

- [Fixed-flow continuation lower bound](../records/21a3ca77-54c5-4e22-8493-9926749662d4.md)

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BB3e%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BB3e%5D+) · [Contributor guide](../CONTRIBUTING.md)
