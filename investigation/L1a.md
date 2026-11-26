<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# L1a · Count strict threshold drops within one fixed-boundary phase

**🟩 Result for the stated scope**

Counting-network transportation margins force at least $2^h-1$ strict Algorithm 4 threshold drops on one fixed open boundary with $2h+2$ targets, unit losses, and two gains. The Hall-ratio upper bound gives a matching exponential worst-case count when the numbers of types and targets are equal. The lower bound holds over all exact optimizing flows and fixed seed orders.

[Read the evidence](../notes/L1a-strict-threshold-drops.md) · [Investigation index](README.md)

Parent question · [L1 · Locate the exact algorithm and its worst-case bottleneck](L1.md)

## Relevant work

- L1a **uses** [L2 · Account for exact arithmetic along a run](L2.md). At a successful increase the threshold is a weighted Hall ratio. Count strict changes of that value separately from changes of the set attaining it. [Evidence](../notes/L2-exact-arithmetic-audit.md#non-repetition-with-exact-flow-ties)
- L1a **is constrained by** [B3f · Force many flow switches at uniform margins](B3f.md). Flow switches occur even at a fixed threshold and fixed target totals. Any certificate-based shortcut must account for these internal changes. [Evidence](../notes/B3f-forced-flow-switches.md)
- L1a **uses** [B3b · Count progress in closed reachable groups](B3b.md). Counting prior and inverse-gain multiplicities bounds the number of threshold values in that restricted class. [Evidence](../notes/B3b-closed-group-rank.md#thresholds-and-changes-of-seed)
- L1a **compares with** [B3e · Embed a parametric path in one unchanged flow](B3e.md). The tight Hall families can change while the source’s witness spans the entire boundary and Algorithm 4 never runs. [Evidence](../notes/B3e-parametric-path-lower-bound.md#hall-witnesses-at-the-same-threshold)

## Where the direction came from

- OpenAI Codex · [Track Hall certificates and the size of exact intermediate states](../DIRECTIONS.md#direction-continuation-followups) · Follow-up questions recorded in L1 and L2

## Contribution log

- [Exponential strict threshold drops on one fixed open boundary](../records/8d52deb9-efe9-4870-896a-2fab554a6e93.md) · result · proof · Robert Thomas Collins, OpenAI Codex · Codex (underlying model snapshots unspecified), Python

[Join the discussion in issue #3](https://github.com/robbiemu/bayesian-simple-security-games/issues/3) · [Find other discussions](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BL1a%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BL1a%5D+) · [Contributor guide](../CONTRIBUTING.md)
