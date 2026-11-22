<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# B3f · Force many flow switches at uniform margins

**🟩 Result for the stated scope**

A second construction forces many different assignments on one run. The final budget of this family still admits a direct solver.

[Read the evidence](../notes/B3f-forced-flow-switches.md) · [Investigation index](README.md)

Parent question · [B3 · Bound progress with overlapping types](B3.md)

## Relevant work

- B3f **limits** [B3a · Jump across steps that preserve an attack flow](B3a.md). A fixed-flow jump cannot cross two witness intervals requiring different assignments. [Evidence](../notes/B3f-forced-flow-switches.md)
- B3f **extends** [B3e · Embed a parametric path in one unchanged flow](B3e.md). The assignment construction forces changes of the flow itself. [Evidence](../notes/B3f-forced-flow-switches.md)
- [B3g · Independently check the forced-switch proof](B3g.md) **checks** B3f. The audit checks assignment encoding, separation, input size and the final-budget exception. [Evidence](../notes/B3g-lower-bound-audit.md)
- [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md) **uses** B3f. The forced assignments also yield a lower-bound family for directional auctions. [Evidence](../notes/A4-minimum-price-markets.md)

## Where the direction came from

- Robert Thomas Collins · [Classify the longest single continuation run](../DIRECTIONS.md#direction-busy) · Independently proposed framing
- Robert Thomas Collins · [Pursue the unresolved continuation case](../DIRECTIONS.md#direction-single) · Research direction
- Robert Thomas Collins · [Expose the scope of the counterexample](../DIRECTIONS.md#direction-sketch) · Manuscript direction
- Robert Thomas Collins · [Check the library pieces for a constructive proof](../DIRECTIONS.md#direction-lean) · Verification direction

## Contribution log

- [Fixed-flow continuation lower bound](../records/21a3ca77-54c5-4e22-8493-9926749662d4.md) · result · proof · Robert Thomas Collins · GPT-6.2 Sol, GPT-6.2 Astra

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BB3f%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BB3f%5D+) · [Contributor guide](../CONTRIBUTING.md)
