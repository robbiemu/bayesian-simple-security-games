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
- [A4h12 · Use one-good block solvers for shared buyers and goods](A4h12.md) **supplies an oracle to** L4b. The bounded incidence block condition survives the capacity and reserve queries. [Evidence](../notes/A4h-buyer-proxy.md#an-exact-solver-on-bounded-incidence-blocks)
- [L4c · Use structure at one answer endpoint and test reusable price lists](L4c.md) **extends** L4b. A failed structure test can guide threshold bisection on the appropriate side of the requested budget. [Evidence](../notes/L4-structured-endpoints.md#the-two-endpoint-promises)
- L4b **gives an endpoint alternative to** [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md). A clearing oracle can recover the coverage at the requested budget without counting every internal step of the original path. [Evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)
- [A4i · Reduce affine market clearing to one-resource security games](A4i.md) **reverses** L4b. L4b solves the supplied budget with market calls. A4i obtains minimum prices from one game. [Evidence](../notes/A4i-market-to-game.md)
- [A4i1 · Find the exact minimum prices of one supplied unit market](A4i1.md) **uses** L4b. Common-capacity Hall comparisons give polynomial-size unit queries for exact threshold and budget recovery. [Evidence](../notes/A4i-market-to-game.md#jointly-uniform-games-and-unit-markets)

## Where the direction came from

- Robert Thomas Collins · [Transfer market structure and examine the Newton bound](../DIRECTIONS.md#direction-newton) · Selected linked research directions

## Contributions elsewhere that cite this work

- [Clear a common-offset core with heterogeneous single-vertex branches](../records/050f6342-7cce-48ec-b308-036810d0c200.md)
- [Equate unit market search with equilibrium under uniform priors and gains](../records/05ac5a83-21c6-4859-a3a6-3e9ee5a62863.md)
- [Reduce exact affine-market clearing to one defender resource](../records/0952bf4d-148a-4ea4-9130-b8c0ff07156e.md)
- [Use one answer endpoint to certify the threshold search](../records/70afccbf-e6a3-451d-9dac-08ae1cf33159.md)
- [Equate unit market search with equilibrium under uniform priors and gains](../records/792ca289-2e48-4b18-b6c2-67c2cb68a5a2.md)
- [Use one answer endpoint to certify the threshold search](../records/835e8a45-90e9-432d-a45c-dbf2f80f1444.md)
- [Reduce mixed buyer and good articulations to the one-good block solver](../records/9633dd66-8ec4-4f53-91b2-447e98e34710.md)
- [Reduce mixed buyer and good articulations to the one-good block solver](../records/e1fb17e8-e666-42cd-9900-778c96ddd3c6.md)
- [Clear a common-offset core with heterogeneous single-vertex branches](../records/e1fcfa01-8d57-4849-b50f-d8773258ea1e.md)
- [Reduce exact affine-market clearing to one defender resource](../records/f4f5b6ed-bad7-4af7-bb54-4175c6f95eed.md)

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BL4b%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BL4b%5D+) · [Contributor guide](../CONTRIBUTING.md)
