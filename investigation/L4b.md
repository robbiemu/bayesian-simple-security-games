<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# L4b · Transfer market endpoints and exact threshold search to L1/L2

**🟩 Result for the stated scope**

An exact any-clearing oracle yields both threshold endpoints and permits budget search without tracing every flow change.

[Read the evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle) · [Investigation index](README.md)

Parent question · [L4 · Compare the Newton bound with the continuation landscape](L4.md)

## Relevant work

- L4b **gives an alternative derivation for** [L3 · Check the prior partial results and reconcile overlap](L3.md). At a fixed threshold, a continuous reserve path and rational reconstruction recover the requested budget via a clearing oracle. The proof is available in the public note. [Evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)
- L4b **applies to** [B3f · Force many flow switches at uniform margins](B3f.md). Endpoint search can skip B3f’s forced flow switches. On that family the near-factorized solver makes the clearing calls polynomial-time. [Evidence](../notes/L4-newton-and-continuation.md#limits-on-following-the-entire-path)
- L4b **uses** [A4c · Reduce minimum-price search to any clearing equilibrium](A4c.md). Clearing calls at perturbed supplies bracket both threshold endpoints. [Evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)
- L4b **uses** [A4a · Test contraction near factorized slopes](A4a.md). The embedded hard trajectory has near-factorized slopes at a fixed budget. [Evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)
- L4b **extends** [L2 · Account for exact arithmetic along a run](L2.md). Endpoint searches can skip internal flow switches. [Evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)

## Where the direction came from

- Robert Thomas Collins · [Transfer market structure and examine the Newton bound](../DIRECTIONS.md#direction-newton) · Selected linked research directions

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BL4b%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BL4b%5D+) · [Contributor guide](../CONTRIBUTING.md)
