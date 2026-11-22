<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# L2b · Bound intermediate rational bit lengths by the original input size

**🟦 Open**

After j outer calls, L2 bounds the bit length of stored coordinates by a polynomial in the input length times j + 1. An input-only bound for the specified exact continuation remains open.

**Open task** — Bound the bit lengths of the reduced numerators and denominators of every retained coverage and flow by a polynomial in the original input length, or exhibit a family exceeding every such bound under specified optimizer choices.

[Read the evidence](../notes/L2-exact-arithmetic-audit.md#bit-length-bound-and-exact-lp-outputs) · [Investigation index](README.md)

Parent question · [L2 · Account for exact arithmetic along a run](L2.md)

## Relevant work

- L2b **uses** [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md). The question concerns exact intermediate states of the published continuation. Specify its flow and optimizer choices. [Evidence](../notes/L2-exact-arithmetic-audit.md#bit-length-bound-and-exact-lp-outputs)
- L2b **compares with** [B3a · Jump across steps that preserve an attack flow](B3a.md). The greatest-extension variant obtains an input-only bit bound for its LPs. Its update differs from the published continuation. [Evidence](../notes/B3a-fixed-flow-jump.md)

## Where the direction came from

- OpenAI Codex · [Track Hall certificates and the size of exact intermediate states](../DIRECTIONS.md#direction-continuation-followups) · Follow-up questions recorded in L1 and L2

[Join the discussion in issue #5](https://github.com/robbiemu/bayesian-simple-security-games/issues/5) · [Find other discussions](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BL2b%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BL2b%5D+) · [Contributor guide](../CONTRIBUTING.md)
