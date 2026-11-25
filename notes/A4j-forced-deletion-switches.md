# A4i1b · Forced deletion-matching switches at degree three

**Theorem.** Some affine unit markets with $N$ goods and $N+1$ buyers force $N^{\Omega(\log N)}$ internal updates of the deletion-matching ascent in one fixed reached-set phase. The specified insertion order places a distinguished degree-one buyer last. During that insertion the minimum matching product for deleting this same buyer takes $N^{\Omega(\log N)}$ distinct values. The viable graph has maximum degree three on both sides, and all nonunit offers form a matching. Minimum prices on the family can be computed by the near-factorized solver. [Deletion-matching ascent](A4j-unit-matching-ascent.md) · [Near-factorized solver](A4a-near-factorized-slopes.md)

## Transfer the forced assignments to a unit market

Use the B3f family of $n$-type, $n$-target games with uniform type probabilities and unit defender gains. Its attacker utilities, written at coverage $q$, are
\[
 a_{ij}-d_{ij}q_j=-q_j+\varepsilon(B_{ij}-C_{ij}q_j),\qquad
 |B_{ij}|+|C_{ij}|\le M,\quad \varepsilon=\frac1{64nM^2}.
\]
Here $M\ge2n+1$. Let $\rho=\varepsilon M$. B3f gives $K=n^{\Omega(\log n)}$ disjoint positive-length intervals in $[1/4,1]$ for $b=\sum_j q_j$. In interval $J_\ell$, at every equilibrium the row-maximizer graph admits only the perfect matching $\pi_\ell$. In interval order the products $\prod_i d_{i,\pi_\ell(i)}$ strictly decrease. B3f obtains the intervals from the separated shortest paths of Gajjar and Radhakrishnan. [B3f forcing and product comparison](B3f-forced-flow-switches.md#why-every-equilibrium-uses-the-prescribed-assignment) · [Parametric shortest paths, Lemma 14 and Theorem 1](https://arxiv.org/pdf/1811.05115#page=13)

Make the balanced market of $n$ unit buyers and $n$ unit goods with offers $2+a_{ij}-d_{ij}q_j$. Reserves and outside utilities are zero. Call these buyers and goods the core. For $b\le1$ all core offers have utility at least $1-\rho>0$. If the core has a supported perfect matching at $q$, allocate $1/n$ on each matched pair in the game. The rows best respond, and equal attack totals make the defender indifferent among all coverages of budget $b$. Thus $q$ is an equilibrium coverage. The matching must be $\pi_\ell$ whenever $b\in J_\ell$. Also, a supported perfect matching at any such $q$ implies
\[
 \max_j q_j-\min_j q_j\le 2\rho.
\]
A larger spread would make the highest-priced good strictly worse than a lowest-priced good in every row, so that good could not be matched.

At $b=1/4$ a B3f equilibrium supplies a clearing of the square core. Its least price vector $q^0$ therefore has $\sum_j q^0_j\le1/4$. Strict Hall forces some least price to be zero because the entire goods set has at most $n$ neighboring buyers. All core offers are positive at $q^0$, so there is a supported perfect matching, and the spread bound gives $\max_j q^0_j\le2\rho$. In particular, $\sum_j q^0_j<1/4$. [Strict minimum-price Hall test](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

Insert one more buyer $r$ with only the offer $2-q_1$, after the entire core. For $b\le1$ all $n+1$ buyers strictly want real goods and hence cannot clear. The final insertion starts at $q^0$ and its continuous, nondecreasing price path goes beyond $b=1$. Throughout every open price step in the band, all core buyers stay matched on demand. This gives exactly the supported core matching needed by the argument above. Once $b\ge1/4$, writing $s=b/n$, each $q_j\ge s-2\rho>2\rho$. Every good has increased from its starting price. The ascent moves only reached goods, and the reached sets are nested within the insertion. Consequently the whole witness band lies in the full reached-set phase. The minimum matching for deleting $r$ is held fixed through each open step. An open step can intersect at most one witness interval. This already gives at least $K-1$ internal updates for the square core with the extra buyer.

The earlier directional-auction construction uses capacity two and two copies of each type to obtain the core matching from a demand condition. The deletion-matching ascent maintains that matching explicitly by inserting the last buyer after the balanced core. [Earlier directional-auction transfer](A4-minimum-price-markets.md#lower-bound-for-the-directional-ascending-auctions)

## Preserve the witnesses under degree-three path splits

Before adding $r$, apply the buyer and good splits of the degree-three reduction to the square core, using private intercept $4$. This exceeds both each core bid and each bid divided by its slope. An original buyer with $n$ viable offers becomes $n$ buyer copies and $n-1$ private goods. An original good with $n$ viable offers becomes $n$ ports and $n-1$ guard buyers. There are $N=n(2n-1)$ unit goods and the same number of core buyers after splitting. Add $r$ with only the offer $2-p_g$ on an end port $g$ of original good 1. The end port had at most two incident buyers before this addition. All split-path offers have slope one, and each old offer occupies its own buyer copy and port. [Degree-three path splitting and price projection](A4j-unit-degree-three.md)

For an expanded price vector $p$, let $q_j$ be the highest port price for original good $j$, and let $b=\sum_j q_j$. Whenever $b\le1$, every port price lies in $[0,1]$. Every original buyer copy has its positive external offer at its own port, every guard has a positive private offer, and $r$ has a positive offer. The final insertion again cannot clear in this band. In an open step there, all expanded core buyers are assigned to real goods, so their matching is a clearing of the balanced expanded core. In the path-split projection, the original external purchases form a perfect core matching supported at $q$. Each external purchase retains its slope and all other used offers have slope one. Thus the full expanded matching product equals the product of the projected permutation.

The least expanded core prices before inserting $r$ project to $q^0$. Indeed, projecting those prices gives a core clearing, and lifting $q^0$ gives an expanded clearing. Coordinatewise minima and the order-preserving maximum give both inequalities. The projected sum is continuous and nondecreasing during the final insertion, so it visits the entire witness band.

In fact every expanded good is reached by the time $b=1/4$. To see this, write $s=b/n$ and consider an expanded core matching at a price with $b\le1$. The projection and the spread bound give $|q_j-s|\le2\rho$. The buyer copy that takes the external offer for a given original buyer has utility at most $2-s+3\rho$, since its purchased port is at $q_j$. The buyer path guarantees that this utility weakly dominates the utilities of all the copies of that buyer. Each copy can earn at least $2-s-3\rho$ on its own external offer, since its port price is at most $q_j$. These facts give
\[
 4-2+s-3\rho\ \le p_h\le\ 4-2+s+3\rho
 \quad\text{for each buyer-side private good } h.
\]
Indeed its matched copy earns $4-p_h$. They also give $s-4\rho\le p_g\le s+2\rho$ for each port $g$. Its attached copy can earn at least $2-p_g-\rho$ there, and earns at most $2-s+3\rho$ overall.

At the start of the insertion, $q^0_j\le2\rho$. Thus every port is at most $2\rho$ and every buyer-side private good is at most $4-2+5\rho$. For $b\ge1/4$ we have $s\ge1/(4n)>8\rho$. The displayed lower bounds put every expanded good strictly above its starting value. Nested reached sets then give one full reached-set phase throughout the witness band.

Choose an interior budget in each $J_\ell$ away from the finitely many projected prices at step endpoints. In its open step, the root-deletion plan is the fixed full expanded core matching. Its product is exactly $\prod_i d_{i,\pi_\ell(i)}$. The products strictly decrease in witness order, so there are at least $K$ updates and $K-1$ internal updates in the full phase. This applies to any choice among minimum-product matchings in the specified insertion order.

## Bit length, endpoint, and exact checks

The split uses constant-size bids and slopes on the added edges. B3f has $O((\log n)^3)$ bits per original coefficient, so even the dense split input has polynomial bit length in $n$. Since $N=\Theta(n^2)$, the number of updates is $N^{\Omega(\log N)}$ and is superpolynomial in the full binary input length. Moreover $|d-1|\le\rho=1/(64nM)\le1/(4N)$ for every slope of the expanded instance. A4a solves the same instances in polynomial bit time with row and column factors one. [B3f bit bound](B3f-forced-flow-switches.md#binary-input-size-and-the-one-resource-endpoint) · [A4a contraction and exact recovery](A4a-near-factorized-slopes.md#the-contraction-and-exact-recovery)

The replay uses B3f's four-type, three-path example. The unsplit market takes four updates, with two internal, and the degree-three market has 28 goods and takes ten updates, with two internal. Every split deletion minimum at every recorded update is checked by sparse exhaustive matching enumeration. The three witness budgets are in one phase with all goods reached in both runs. At the witnesses, independent enumeration finds the following unique assignments and products. [Exact replay](../experiments/a4j_deletion_product_replay.py)

| Budget | Assigned columns in core row order | Minimum slope product |
| --- | --- | --- |
| $1/4$ | $(3,1,2,0)$ | $1$ |
| $5/8$ | $(1,3,2,0)$ | $4859999/4860000$ |
| $1$ | $(2,1,3,0)$ | $2429999/2430000$ |

Run `python3 -B experiments/a4j_deletion_product_replay.py`. The finite replay checks the transfer on this fixture. The update lower bound follows from the interval family and the path argument above. Exact search for minimum prices in arbitrary unit markets remains open.

Robert Thomas Collins directed the follow-up. The Codex GPT-6.2 Astra subagent derived the final-insertion transfer and its extension through the existing degree-three splits. The coordinating Codex session audited the proof and independently implemented and ran the exact replay. The construction uses the project's B3f forcing proof, the A4i1b ascent, and the A4 degree-three reduction. OpenAI Dot's separately credited chain is the control that motivated seeking actual minimum-product changes. [Chain control and its credit](A4j-deletion-matching-chains.md)
