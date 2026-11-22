# B3. Progress and lower bounds with overlapping types

The unrestricted continuation can require $n^{\Omega(\log n)}$ distinct attack flows even with $n$ targets, $n$ equally likely types, identical defender gains, strictly positive losses close to one, and a final budget of one. Throughout the difficult budget interval the defender threshold and every target's aggregate attack mass remain fixed. Both the published resource-augmentation algorithm and the fixed-flow LP jump variant therefore have superpolynomial worst-case runs. The question of computing an equilibrium directly in polynomial time remains open. [Forced flow switches](B3f-forced-flow-switches.md) · [Published continuation](https://arxiv.org/pdf/1602.01896)

## Why the lower bound holds

Gajjar and Radhakrishnan construct acyclic networks with superpolynomially many distinct uniquely optimal paths as affine edge weights vary in one scalar parameter. Add self-loops, a closing edge from sink to source, and force that closing edge. The permitted perfect assignments then correspond to source–sink paths, with the remaining vertices matched to themselves. A large constant penalty excludes the other edges. [Parametric Shortest Paths in Planar Graphs, Lemma 14 and Appendix B](https://arxiv.org/pdf/1811.05115)

Write the resulting maximizing assignment weights as $B_{it}-C_{it}s$. Give the game uncovered utilities $a_{it}=\varepsilon B_{it}$ and losses $d_{it}=1+\varepsilon C_{it}$, for a small rational $\varepsilon$ of polynomial bit length. At an intermediate total coverage $b=ns$ in the chosen range, the spread of target coverages is at most $2\varepsilon M$, where $M$ bounds $|B_{it}|+|C_{it}|$. A larger spread would make every type prefer a least-covered target to every most-covered target, permitting an improving transfer of defender coverage. The choice of $\varepsilon$ forces interior coverages and uniform target attack totals.

At such a budget, write $x_t=s+\varepsilon y_t$. If a permutation lies in the support of the attack flow, each of its edges is a row best response. On summing the payoffs of any permutation, its target-price terms $y_t$ sum to the same number. The residual slope terms are small enough to preserve the parametric assignment's strict gap. Thus on each of the source's separated winning intervals **every equilibrium forces the same unique assignment**, and distinct intervals force distinct flows. A continuous resource-augmentation path with a fixed flow on each segment must pass through those intervals. At the final budget of the constructed family, one ordinary assignment and a rational support LP suffice to compute the equilibrium directly. [Full reduction and exact constants](B3f-forced-flow-switches.md)

## What the progress measures still give

| Approach | Proven scope |
| --- | --- |
| Jump to the greatest feasible coverage for one attack flow | At fixed target totals, each later jump consumes a distinct alternating cycle. Across threshold changes, the count is polynomial when the viable graph has at most logarithmic cycle rank per component. The bit length of each LP is polynomial in the original input. [Proof](B3a-fixed-flow-jump.md) |
| Count local cost and distance values | Reachability groups only grow while a seed and the target totals stay fixed. The resulting bound is polynomial with a fixed number of prior and inverse-gain values and bounded multiplicative rank of slope products around cycles. [Proof](B3b-closed-group-rank.md) |
| Separate a few shared targets | Exact polynomial search applies when deleting a fixed number of targets leaves at most a fixed number of types in each component. At fixed shared coverages and defender threshold, each component's budget interval is independent of its attainable shared flows. [Proof](B3d-shared-target-separator.md) |
| Charge progress to individual edges | A four-target exact trace has a strict flow-cost drop where every edge of the new unique optimizer had carried mass in an earlier optimizer. The replay also checks a three-target counterexample to optimizing on the union of historical best-response edges. [Examples](B3c-exact-path-search.md) · [Replay](../experiments/b3_fixed_load_search.py) |

The independent path construction forces a long original run even with one unchanged flow, by making the least coverage compatible with that flow trace a parametric path envelope. A greatest-extension LP can skip all those events. The forced-switch construction above also defeats that jump. [Fixed-flow path construction](B3e-parametric-path-lower-bound.md)

## Next target

Search directly at the requested resource total. The [minimum-price oracle reduction](L3-prior-partials.md#conditional-exact-reduction-to-a-minimum-price-oracle) gives one route. Any candidate market algorithm needs a total bit-time bound with binary masses and capacities. A method that visits every intermediate budget and follows each constant-flow segment encounters the lower bound above.
