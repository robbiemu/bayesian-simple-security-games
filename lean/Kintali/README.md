# Formalizing Kintali’s Bayesian security-game algorithm

The target is the $L^{O(1)}$ deterministic bit-time result in Shiva
Kintali’s nine-page November 24, 2026 preprint. This work checks parts
of that proof with Lean 4.36.0 and the pinned Mathlib. The paper credits
Baïou and Balinski for ordinal transportation. [Short preprint](https://shivakintali.github.io/papers/SecurityGames-short.pdf) · [PDF at the author’s Git revision](https://github.com/shivakintali/shivakintali.github.io/blob/b28db0428e4cdcef7e9048a386b05d942d1eb57e/papers/SecurityGames-short.pdf)

I found no public author-led or independent solution formalization as
of November 25, 2026. I checked Kintali’s homepage, public repositories,
recent website commits, and public announcement, and searched for Lean
code and discussion by the paper title, Conitzer’s arXiv ID, and the
public theorem’s name. Work in private is unknown. Bocowgill’s merged
Formal Conjectures PR supplies a binary-rational input and compact
equilibrium predicate. Its theorem `exists_isPolyTime_bayesNash` has a
`sorry` proof term. [Author’s homepage](https://shivakintali.github.io/) · [Author’s repositories](https://github.com/shivakintali?tab=repositories) · [Formal Conjectures PR #8174](https://github.com/google-deepmind/formal-conjectures/pull/8174) · [Pinned Lean statement](https://github.com/google-deepmind/formal-conjectures/blob/9bd16c570aed942e00ae000c7522dd42ebbb25eb/FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean)

## Checked statements

| Paper location | Lean file | Kernel-checked claim |
| --- | --- | --- |
| §1, exact certificate | [Equilibrium.lean](Equilibrium.lean) | A feasible certificate gives the compact best-response inequalities. Joint masses normalize to conditional probabilities, and a zero-prior row chooses a minimizing reference target. |
| Lemma 5 | [StableAllocation.lean](StableAllocation.lean) | Every outside and vacancy balance is invariant at fixed quotas. The total absolute change in those balances is bounded by the total absolute change in quotas. |
| Equation (5) and Lemma 6 | [ContactComparison.lean](ContactComparison.lean) | At a stable allocation, positive ordinary bids number at most the sum of the numbers of incident buyers and sites. At two equal-budget contacts, their coverage vectors either agree or one of the omitted witness bids blocks the restricted allocation. |
| §3, failure bound | [QuoteSearch.lean](QuoteSearch.lean) | An interval missing every selected internal quantile carries weight at most $V/J$, including either endpoint interval. Each failure marks a member of a fixed witness of size at most $h$. With at most $G$ bids per pair and marked weight by pair at most its current total divided by $4h$, fewer than `2 * h * (G.log2 + 1)` failures are possible. |

## Two simplifications of the contact proof

**The support bound follows from stability.** At least one endpoint of
each positive ordinary bid rejects more of that bid. The bid is then
a worst positive holding at that endpoint. Strict ranks give each
endpoint only one such holding, so charging each bid to a rejecting
endpoint gives the count. Apply this to optional real bids to obtain
the fixed witness bound $k+m_+$ at any stable contact allocation.

**Comparative statics also follows from stability.** Compare stable
allocations $X,Y$ in the same restriction with different quotas.
At a vertex let $P,N$ be the total increases and decreases on its
records. By the rejection argument of Lemma 5, the charged weight
there is at most $\max(P,N)=(P+N+|P-N|)/2$, where $P-N$ is the
quota change. Each ordinary record contributes twice to the
incident weight and each outside or vacancy record contributes once.
Every changed record contributes at least once to the charged
weight. Summing bounds the absolute slack variation by the absolute
quota variation.

When only site quotas increase, conservation expresses the total
quota increase as site vacancy increases minus changes in buyer
outside balances, summed with their signs. The absolute variation
bound forces equality term by term. Thus each buyer’s outside
balance is nonincreasing, including each private buyer’s. The
private outside sums divided by their original mass give the
componentwise coverage order. For Lemma 6, join the two bid sets
through the witness and apply that order directly at their two
contact pressures. Equal budgets force equality in every coordinate.
Stability of those two allocations on the union suffices for the comparison.

## Remaining proof obligations

- Construct and verify the finite quota sweep from Lemma 3. Prove
  proposal and stability invariants, progress at cycles and
  exhaustions, first budget contact, and the rational bit bound.
- Connect finite quote grids and grouped private buyers to the
  ordinal market model. Verify the blocker interval, the compressed
  updates, and exact recovery from the full market’s pattern in
  Lemmas 2 and 4, including the determinant bound.
- Supply a polynomial-time rational LP implementation or a
  machine-model theorem for that subroutine. Connect the compact
  tables to the public list encoding, and compose the bit bounds
  with `IsPolyTime`. The compact output suffices for the public
  theorem. The paper also recovers a lottery on pure defenses.

## Replay

Run both commands from `lean/` with the project’s pinned packages and Lean toolchain.

```sh
lake --wfail build Kintali
lake env lean Replay/KintaliAxioms.lean
```

The derivation of the stronger quota comparison and the support
charging argument, and the Lean translation, were developed with
OpenAI Codex. Both commands passed on November 25, 2026. The audit
reported dependencies among `propext`, `Classical.choice`, and
`Quot.sound`. The source of the algorithm and the fixed-quota
rejection argument is Kintali’s manuscript.
