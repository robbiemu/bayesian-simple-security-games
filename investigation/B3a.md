<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# B3a · Jump across steps that preserve an attack flow

**🟩 Result for the stated scope**

Extends coverage as far as possible at one attack flow and identifies a consumed cycle.

[Read the evidence](../notes/B3a-fixed-flow-jump.md) · [Investigation index](README.md)

Parent question · [B3 · Bound progress with overlapping types](B3.md)

## Relevant work

- B3a **extends** [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md). The jump holds one optimal attack flow fixed. [Evidence](../notes/B3a-fixed-flow-jump.md)
- [B3f · Force many flow switches at uniform margins](B3f.md) **limits** B3a. A fixed-flow jump cannot cross two witness intervals requiring different assignments. [Evidence](../notes/B3f-forced-flow-switches.md)
- [L2b · Bound intermediate rational bit lengths by the original input size](L2b.md) **compares with** B3a. The greatest-extension variant obtains an input-only bit bound for its LPs. Its update differs from the published continuation. [Evidence](../notes/B3a-fixed-flow-jump.md)

## Where the direction came from

- Robert Thomas Collins · [Classify the longest single continuation run](../DIRECTIONS.md#direction-busy) · Independently proposed framing

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BB3a%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BB3a%5D+) · [Contributor guide](../CONTRIBUTING.md)
