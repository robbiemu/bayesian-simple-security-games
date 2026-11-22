<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# L2a · Tighten the worst-case outer-call count on a single run

**🟦 Open**

The published continuation can require superpolynomially many steps. A gap remains between the forced-switch lower bound and the arrangement upper bound for its exact implementation.

**Open task** — Improve either bound using comparable dimensions, binary input sizes and tie rules. For a restricted class, identify the additional hypothesis.

[Read the evidence](../notes/L2-exact-arithmetic-audit.md#non-repetition-with-exact-flow-ties) · [Investigation index](README.md)

Parent question · [L2 · Account for exact arithmetic along a run](L2.md)

## Relevant work

- L2a **refines** [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md). The run being counted is the original resource-augmentation route. Fix its tie rules and follow one input. [Evidence](../notes/B1-classify-run-lengths.md#computing-a-worst-case)
- L2a **uses** [B1 · Define a restricted Busy Beaver and test a state classification](B1.md). A fixed implementation and a realizable run give the classwise maximum its meaning. B1 also proposes summing local ranks across components. [Evidence](../notes/B1-classify-run-lengths.md#computing-a-worst-case)
- L2a **uses** [B3f · Force many flow switches at uniform margins](B3f.md). Many distinct assignments are forced on one trajectory. This supplies the lower side of the remaining gap. [Evidence](../notes/B3f-forced-flow-switches.md)
- L2a **is related to** [B3 · Bound progress with overlapping types](B3.md). B3 records restricted progress bounds for overlapping types and asks for sharper classes or worst-case bounds. [Evidence](../notes/B3-overlapping-types.md#what-the-progress-measures-still-give)

## Where the direction came from

- Robert Thomas Collins · [Classify the longest single continuation run](../DIRECTIONS.md#direction-busy) · Independently proposed framing

[Join the discussion in issue #4](https://github.com/robbiemu/bayesian-simple-security-games/issues/4) · [Find other discussions](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BL2a%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BL2a%5D+) · [Contributor guide](../CONTRIBUTING.md)
