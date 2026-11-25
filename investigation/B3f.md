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
- [L4b · Transfer market endpoints and exact threshold search to L1/L2](L4b.md) **applies to** B3f. Endpoint search can skip B3f’s forced flow switches. On that family the near-factorized solver makes the clearing calls polynomial-time. [Evidence](../notes/L4-newton-and-continuation.md#limits-on-following-the-entire-path)
- [L1a · Count strict threshold drops within one fixed-boundary phase](L1a.md) **is constrained by** B3f. Flow switches occur even at a fixed threshold and fixed target totals. Any certificate-based shortcut must account for these internal changes. [Evidence](../notes/B3f-forced-flow-switches.md)
- [L2a · Tighten the worst-case outer-call count on a single run](L2a.md) **uses** B3f. Many distinct assignments are forced on one trajectory. This supplies the lower side of the remaining gap. [Evidence](../notes/B3f-forced-flow-switches.md)
- [A4i1b · Bound exact ascent by deletion-matching products](A4i1b.md) **uses** B3f. The forced-flow family gives a fixed reached phase with superpolynomially many strictly decreasing deletion products even after degree-three splitting. [Evidence](../notes/A4j-forced-deletion-switches.md#transfer-the-forced-assignments-to-a-unit-market)

## Where the direction came from

- Robert Thomas Collins · [Classify the longest single continuation run](../DIRECTIONS.md#direction-busy) · Independently proposed framing
- Robert Thomas Collins · [Pursue the unresolved continuation case](../DIRECTIONS.md#direction-single) · Research direction
- Robert Thomas Collins · [Expose the scope of the counterexample](../DIRECTIONS.md#direction-sketch) · Manuscript direction
- Robert Thomas Collins · [Check the library pieces for a constructive proof](../DIRECTIONS.md#direction-lean) · Verification direction

## Contributions elsewhere that cite this work

- [Force superpolynomially many deletion-minimum changes in a degree-three unit market](../records/1365920b-13dc-4169-8862-ce19b0f9c445.md)
- [Certify minimum prices and bound two directional auctions](../records/f9e2da42-7475-4d20-a172-557b2a852ea3.md)

## Contribution log

- [Fixed-flow continuation lower bound](../records/21a3ca77-54c5-4e22-8493-9926749662d4.md) · result · proof · Robert Thomas Collins · GPT-6.2 Sol, GPT-6.2 Astra

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BB3f%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BB3f%5D+) · [Contributor guide](../CONTRIBUTING.md)
