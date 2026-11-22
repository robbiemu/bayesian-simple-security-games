# B3c · Strict cost drops can reuse old matching edges

Even with equal priors, constant defender gains, a fixed seed, and all targets reachable, a strict drop in the continuation's minimum log cost can be triggered by a reentering tie. In a four-target example, every edge of the new unique optimizer had carried mass in an earlier unique optimizer. This rules out charging strict cost drops to the first activation of an edge or to its first use in a minimum-cost flow. A surviving restriction is that the incoming edges of a strictly improving cycle cannot have been jointly active at an earlier coverage at which some target on that cycle was lower. [L2, fixed-total progress](L2-exact-arithmetic-audit.md#non-repetition-with-exact-flow-ties) · [Li, Conitzer and Korzhyk, Algorithms 2–3](https://arxiv.org/pdf/1602.01896#page=7)

In both examples $n=k$, the priors are $1/n$, every defender gain is $1$, and each row has a distinct unique best target initially. All column masses are $1/n$ through the displayed steps. All targets are below cap and have equal defender scores, so all belong to the open boundary throughout. The lexicographically first eligible seed is always $A$. Algorithm 2 has a unique optimal perfect matching at each displayed step. Write $P=\prod_i d_{i,m(i)}$ for its slope product, so its log-flow cost is $(\log P)/n$. An active string such as $AC$ gives the tied targets of one attacker row. [L1, model and algorithm](L1-published-algorithm.md#algorithms-14-and-the-iteration-bound)

## Three targets · Union of formerly active edges

Take defender budget $r=1$ and the following baselines and slopes in target order $A,B,C$.

| Type | Baselines $a_i$ | Slopes $d_i$ |
| --- | --- | --- |
| 1 | $(0,-5/16,-1/8)$ | $(2,1,2)$ |
| 2 | $(-2,0,-3/16)$ | $(1,2,1)$ |
| 3 | $(-2,-1/8,0)$ | $(1,2,2)$ |

| Step | Coverage | Active rows | Matching | $P$ | Coverage rates | Step length |
| --- | --- | --- | --- | ---: | --- | --- |
| 0 | $(0,0,0)$ | A, B, C | ABC | 8 | $(1,0,0)$ | $1/16$ |
| 1 | $(1/16,0,0)$ | AC, B, C | ABC | 8 | $(1,0,1)$ | $1/16$ |
| 2 | $(1/8,0,1/16)$ | AC, B, BC | ABC | 8 | $(1,1,1)$ | $1/16$ |
| 3 | $(3/16,1/16,1/8)$ | ABC, B, BC | ABC | 8 | $(1,2,1)$ | $1/16$ |
| 4 | $(1/4,3/16,3/16)$ | ABC, BC, C | ABC | 8 | $(1,2,4)$ | $1/32$ |
| 5 | $(9/32,1/4,5/16)$ | AB, BC, BC | ACB | 4 | $(1,2,2)$ | $1/32$ |

The reachable targets are all three from step 2 onward. At step 4 the union of previously active edges admits the cheaper matching $ACB$ using $(3,B)$, which was active at steps 2 and 3 and is inactive at step 4. The current graph requires $ABC$. The sole incoming tie at step 5 is $(3,B)$. Its reentry enables the strict switch to $ACB$ and lowers $\gamma_C$ from $4$ to $2$, increasing the shortest-path distance from $A$ to $C$ despite fixed reachability.

## Four targets · Union of formerly used edges

Take $r=3$ and targets $A,B,C,D$. The table gives $4a_i$ to keep the inputs in integers.

| Type | $4a_i$ | $d_i$ |
| --- | --- | --- |
| 1 | $(0,-14,-23,-6)$ | $(71,42,34,53)$ |
| 2 | $(-4,0,-7,-11)$ | $(42,55,47,70)$ |
| 3 | $(-15,-10,0,-21)$ | $(56,60,80,13)$ |
| 4 | $(-18,-3,-7,0)$ | $(17,36,54,79)$ |

The reachable set contains all four targets from step 3. The five strict drops occur at steps 5, 8, 10, 11 and 12, and at each drop at least one target's coverage rate falls. The table records the active graph and optimum at every step.

| Steps | Active rows | Matching | $P$ |
| --- | --- | --- | ---: |
| 0 | A, B, C, D | ABCD | 24679600 |
| 1 | AD, B, C, D | ABCD | 24679600 |
| 2 | AD, B, C, BD | ABCD | 24679600 |
| 3 | AD, B, C, BCD | ABCD | 24679600 |
| 4 | AD, BC, C, BCD | ABCD | 24679600 |
| 5 | AD, ABC, C, BD | DACB | 6410880 |
| 6 | D, ABC, CD, BD | DACB | 6410880 |
| 7 | BD, ABC, CD, B | DACB | 6410880 |
| 8 | ABD, AC, CD, B | ACDB | 1561716 |
| 9 | ABCD, C, CD, B | ACDB | 1561716 |
| 10 | ABCD, AC, D, B | CADB | 668304 |
| 11 | BCD, AC, D, AB | BCDA | 436254 |
| 12 | BCD, BC, D, AB | CBDA | 413270 |

Step 11 starts at $x=(177/700,313/1400,21/100,1139/5300)$ with rates $(1,17/36,7/12,119/318)$. After $8523/18200$ units it reaches $x=(75/104,185/416,201/416,4301/11024)$. The sole incoming edge is $(2,B)$, and $(2,A)$ goes inactive. The old optimum uses $(1,B),(2,C)$ and the new one swaps them for $(1,C),(2,B)$, with $34\cdot55<42\cdot47$. Type 1 used $C$ at step 10, and type 2 used $B$ at steps 0–4. The other two rows retain their step 11 assignments. Thus every edge of the improved matching had previously carried mass, and the union of all edges that had carried mass through step 11 already admitted the cheaper matching $CBDA$ using the then-inactive $(2,B)$.

## A restriction on the incoming edges of a cycle

At a strict cost drop, take an improving alternating cycle in the residual graph of the old flow on the next active graph. For each of its types $i$, let $s_i$ be the target losing mass and $t_i$ the target gaining mass. All cycle edges are active at the new coverage $x'$. If all incoming edges $(i,t_i)$ were jointly active at some earlier $x\le x'$, then at that earlier state each incoming payoff was at least the outgoing payoff. Subtract their equality at $x'$ to get

$$
d_{i,t_i}(x'_{t_i}-x_{t_i})\ge d_{i,s_i}(x'_{s_i}-x_{s_i}).
$$

If any target on the cycle has increased since $x$, strict positivity of the slopes propagates positive coverage differences along the cycle. Multiplying the inequalities and cancelling the coverage differences yields $\prod_i d_{i,t_i}\ge\prod_i d_{i,s_i}$, contradicting strict improvement. The argument applies to any fixed-margin flow, since a strict improvement in optimal cost yields an improving simple residual cycle. Within a fixed reachable group with positive rates, this can charge strict drops to distinct simple cycles. B3f proves that the number of forced flow changes can itself be superpolynomial in a single fixed-margin stretch. [Forced flow switches](B3f-forced-flow-switches.md)

At a constant optimum cost, every previously optimal flow survives the next coverage increase. Optimal-flow invariance from L2 gives the same rates for every optimum, and a used arc has equality between its row and target payoff rates. Combining feasibility of the old optimizer with a fixed lexicographic tie rule gives a nonincreasing pair of cost and lexicographic optimizer. A selected matching cannot disappear and later return under that rule. The four-target example shows why this invariant does not transfer from whole matchings to their individual edges. [L2, optimal-flow ties and fixed-total progress](L2-exact-arithmetic-audit.md#non-repetition-with-exact-flow-ties)

There is also a comparison for whole matches that uses only two clearing states. Let $x^a\le x^b$ have the same load vector $z$ and positive increments $X_t=x^b_t-x^a_t$ in every target. Put $U_i=v_i(x^a)-v_i(x^b)>0$. Comparison to the other state's maximum payoff gives $U_i\le d_{it}X_t$ on each edge used by a feasible flow $q^a$ at $x^a$, and $U_i\ge d_{it}X_t$ on each edge used by a feasible flow $q^b$ at $x^b$. Taking weighted logs and using the margins gives

$$
\sum_{it}q^b_{it}\log d_{it}
\ \le\ \sum_i p_i\log U_i-\sum_t z_t\log X_t
\ \le\ \sum_{it}q^a_{it}\log d_{it}.
$$

If a feasible flow occurs at two endpoints of a segment with strictly positive target rates, compare it to any feasible flow at an intermediate state from both sides. All three costs must equal. Equality for the endpoint flow at the earlier comparison forces $U_i=d_{it}X_t$ on every one of its used edges, making all such edges active at the intermediate state. Thus the entire flow remains feasible throughout that segment, even without requiring it to be a chosen optimum. When some increments vanish, the same inequalities and the equal margins force both endpoint flows to split between positive-increment rows and columns and their zero-increment complements. The weighted log comparison still applies on the moving block.

## Reproduction and scope

Run the [exact Python replay](../experiments/b3_fixed_load_search.py) from the project directory.

```sh
rtk proxy python3 experiments/b3_fixed_load_search.py --replay active
rtk proxy python3 experiments/b3_fixed_load_search.py --replay used
```

The tool enumerates unit-row assignments for the exact optimizer. It collapses each target-to-assigned-row-to-active-target path into a single arc, compares rational path products, and stops at the first budget or cap event. A separate verification enumerated all permutations and used the full bipartite residual graph with the original per-edge caps. It matched every optimizer, target rate and step length in the two replays. The tool also reproduced the five rates and event lengths in the earlier four-type witness. [L1, edge-revisit instance](L1-published-algorithm.md#exact-edge-revisit-instance)

With Python's random generator initialized to 1729, the search drew integer slopes from 1 to 80 and baseline gaps from 1 to 24, and assigned each row its unique diagonal maximum. A three-target historical-active and reentry witness appeared at zero-based sample 1579 of 10,000. The displayed three-target input was then constructed with smaller rational coefficients. An unscaled four-target sample at index 12792 of 16,000 had a historical-used gap. Dividing its baselines by four and changing $d_{1B}$ from $40$ to $42$ gave the displayed strict drop using only formerly used edges. These are small exact examples within the first fixed-load segment. They leave the maximum number of drops as game size grows and the behavior across saturation and Algorithm 4 outside the search.
