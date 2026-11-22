<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# L1a · Count necessary Hall-witness changes within one fixed-boundary phase

**🟦 Open**

At a successful increase, a maximizing weighted Hall set certifies the current threshold. Several sets can tie. Many attack-flow switches can occur while the threshold and all target totals stay fixed.

**Open task** — Specify how a witness is selected or retained across ties. Prove a bound on its changes on one run or give a family that forces many changes under that rule.

[Read the evidence](../notes/L1-published-algorithm.md#literature-check-and-next-lemma) · [Investigation index](README.md)

Parent question · [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md)

## Relevant work

- L1a **uses** [L2 · Account for exact arithmetic along a run](L2.md). The exact implementation gives a maximizing Hall ratio at each successful increase. Non-repetition of a full signature leaves the changes of a smaller certificate to count. [Evidence](../notes/L2-exact-arithmetic-audit.md#non-repetition-with-exact-flow-ties)
- L1a **is constrained by** [B3f · Force many flow switches at uniform margins](B3f.md). Flow switches occur even at a fixed threshold and fixed target totals. Any certificate-based shortcut must account for these internal changes. [Evidence](../notes/B3f-forced-flow-switches.md)

## Where the direction came from

- OpenAI Codex · [Track Hall certificates and the size of exact intermediate states](../DIRECTIONS.md#direction-continuation-followups) · Follow-up questions recorded in L1 and L2

[Join the discussion in issue #3](https://github.com/robbiemu/bayesian-simple-security-games/issues/3) · [Find other discussions](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BL1a%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BL1a%5D+) · [Contributor guide](../CONTRIBUTING.md)
