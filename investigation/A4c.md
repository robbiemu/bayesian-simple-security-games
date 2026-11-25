<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# A4c · Reduce minimum-price search to any clearing equilibrium

**🟩 Result for the stated scope**

Any clearing equilibrium of one suitably enlarged market yields original minimum prices.

[Read the evidence](../notes/A4c-any-clearing-equilibrium.md) · [Investigation index](README.md)

Parent question · [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md)

## Relevant work

- A4c **reduces** [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md). Solving one enlarged clearing instance recovers minimum prices. [Evidence](../notes/A4c-any-clearing-equilibrium.md)
- [L4b · Transfer market endpoints and exact threshold search to L1/L2](L4b.md) **uses** A4c. Clearing calls at perturbed supplies bracket both threshold endpoints. [Evidence](../notes/L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)
- [A4i · Reduce affine market clearing to one-resource security games](A4i.md) **uses** A4c. A supply increase makes any game certificate recover the original market minimum. [Evidence](../notes/A4i-market-to-game.md#one-padding-target-pins-the-relevant-score)
- [A4f3 · Scale price precision with stable flows at physical quotas](A4f3.md) **uses** A4c. Comparing clearance at the original and enlarged capacities gives the exiting Hall paths and makes the repaired prices unique. [Evidence](../notes/A4f-precision-scaling.md#exit-paths-certify-the-new-box)
- [A4l · Find exact clearing through ordinal stable allocation](A4l.md) **uses** A4c. Enlarged capacities let one ordinal stable allocation and its price lift recover the original minimum. [Evidence](../notes/A4l-ordinal-stable-allocations.md#exact-minimum-prices-and-the-unit-shortcut)

## Where the direction came from

- Robert Thomas Collins · [Switch from tracing the path to the market oracle](../DIRECTIONS.md#direction-pivot) · Selection of direction

## Contributions elsewhere that cite this work

- [Obtain a subexponential exact market solver by lattice block search](../records/02970891-b5d8-42fe-8b87-a99dcfe5d543.md)
- [Use grouped clearing to compare a proposed price relation](../records/03eaaf28-5c08-4810-9236-03878f2496cd.md)
- [Clear a common-offset core with heterogeneous single-vertex branches](../records/050f6342-7cce-48ec-b308-036810d0c200.md)
- [Equate unit market search with equilibrium under uniform priors and gains](../records/05ac5a83-21c6-4859-a3a6-3e9ee5a62863.md)
- [Reduce exact affine-market clearing to one defender resource](../records/0952bf4d-148a-4ea4-9130-b8c0ff07156e.md)
- [Preserve all completions at fixed boundary quotes](../records/454e63b5-abcb-4b53-8486-e516938db306.md)
- [Contract certified ties and recover the original allocation](../records/4becb293-dc4a-4f61-a4f5-af881f58eaa2.md)
- [Scale affine-market prices with stable contracts and exact support repair](../records/521d0fb1-878f-4e35-8f94-75eff883c296.md)
- [Equate unit market search with equilibrium under uniform priors and gains](../records/792ca289-2e48-4b18-b6c2-67c2cb68a5a2.md)
- [Sharpen the exact lattice bound by pinning a vertex cover](../records/97fe3bb1-1a6c-4fc7-93f2-3e153d799d0c.md)
- [Discover a clearing support through separated ordinal cutoffs](../records/a3264efb-3fa1-4fa8-88dc-d37f641d1c3a.md)
- [Find synchronized boundary quotes using signed branch loads](../records/b0f2709c-7011-4504-b5d9-c80c48ba7687.md)
- [Solve a factorized core with branches at shared buyers and goods](../records/c21ceda9-a451-4c9f-8ad0-8902f8678e95.md)
- [Find synchronized boundary quotes using signed branch loads](../records/d06b6e2a-b651-41a9-8c35-cb646e637913.md)
- [Clear a common-offset core with heterogeneous single-vertex branches](../records/e1fcfa01-8d57-4849-b50f-d8773258ea1e.md)
- [Find endpoint matching representatives and prune them with a price box](../records/ea760303-a4d3-40c2-ae09-b14211a35fef.md)
- [Reduce exact affine-market clearing to one defender resource](../records/f4f5b6ed-bad7-4af7-bb54-4175c6f95eed.md)

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BA4c%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BA4c%5D+) · [Contributor guide](../CONTRIBUTING.md)
