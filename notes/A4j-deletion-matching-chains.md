# A4i1b · Deletion-matching products on chains of squares

A chain of $m$ four-cycles can have $2^m$ attainable deletion-matching products at a single price and clear in one update. A uniform change to one intercept per square gives exactly $m$ internal updates in one reached-set phase. Every run on this incidence graph has at most $m$ internal updates, by a bound on the number of nonunit-gain simple cycles. [Deletion-matching ascent](A4j-unit-matching-ascent.md)

## Equal bids give the control

For each $i=1,\ldots,m$, put two unit buyers $a_i,b_i$ and two unit goods $A_i,B_i$ in a complete bipartite block. Add the offers $b_i A_{i+1}$ for $i<m$ and $rA_1$ for a last unit buyer $r$. Reserves and outside utilities are zero. Every viable intercept is $2$. The slope of $a_iA_i$ is the $i$th prime $q_i$. Every other slope is one. Absent offers can have intercept zero. Both sides have degree at most three.

Insert the block buyers first, in order $a_1,b_1,\ldots,a_m,b_m$. Each prefix admits a demanded matching at zero prices. Once $r$ arrives, the old off-diagonal assignment shows how to reach every good from $rA_1$ along the bridges. The following deletion matchings also establish reachability independently of how the old buyers were assigned.

With $r$ deleted, each prefix of blocks has as many buyers as goods and receives no offers from later blocks. Filling its goods uses all its buyers. Thus no bridge can be used, and each block independently uses its diagonal or off-diagonal matching. The resulting slope products are exactly $\prod_{i\in I}q_i$ for $I\subseteq\{1,\ldots,m\}$. Distinct subsets give distinct products.

Now remove all the prime-slope edges from the demand graph. Each good has two incident buyers, and contracting each good to an edge between those buyers produces a tree. For any deleted buyer, root that tree at the deleted buyer and assign each good to its endpoint farther from the root. This covers all goods with product one. The matching and the old assignment differ by alternating cycles and, when the free buyer changes, an alternating path to that buyer. Hence the whole chain is reached.

The union of the product-one deletion matchings is the whole tree of unit-slope edges. It pins every reached good's normalized price speed to one. On the ensuing step the prime-slope offers become worse, and every reached buyer retains a best offer of utility $2-p$ at the common price $p$. The first catch is outside at $p=2$, where the last buyer can be assigned outside. All goods sell. There was one update and no internal update.

OpenAI Dot's cross-project comparison supplied the chain derivation and initial exact replay. It drew inspiration from Cinna Davis's collection's proof about matching excess, which builds on Hartke, Stolee, West and Yancey's conjecture and binary matching construction. Their conjecture concerns matching excess for a prescribed matching count. The market uses distinct primes to distinguish the independent matching choices by price-slope product. The Bayesian games ascent and certificate checker predate the comparison. [Davis collection at the cited revision](https://github.com/1337isnot1337/solved-conjectures/blob/758066055ef49c2c66cb1087918ae62ad75e7ac1/results/hartke-stolee-west-yancey-matching-excess/PROOF.md) · [Original author manuscript, Theorem 2.3 and Conjecture 9.15](https://dwest.web.illinois.edu/pubs/perfmat.pdf) · [Ascent at the cited revision](https://github.com/robbiemu/bayesian-simple-security-games/blob/74589d93e4b078608e0a8ddb4b1e86722634f9ee/notes/A4j-unit-matching-ascent.md)

## Lower one intercept in each block

Keep the graph and every slope. Put $\delta=1/(m+1)$ and set each $b_iA_i$ intercept to $2-\delta$. The diagonal matching is demanded at zero in every block, so the first $2m$ buyers are still inserted at zero prices. The final insertion follows a curve parameterized by $x=p_{A_1}$ given by

\[
 p_{B_i}=F_i(p_{A_i}),\qquad
 F_i(z)=\min(q_i z,z+\delta),\qquad
 p_{A_{i+1}}=p_{B_i}\quad(i<m).
\]

To see this, first take $q_i p_{A_i}<p_{A_i}+\delta$. Buyer $a_i$ ties her two offers when $p_{B_i}=q_i p_{A_i}$. Buyer $b_i$ then strictly prefers $B_i$ to $A_i$ and ties her bridge when $p_{A_{i+1}}=p_{B_i}$. Once $q_i p_{A_i}>p_{A_i}+\delta$, the equation $p_{B_i}=p_{A_i}+\delta$ ties $b_i$ on both block goods, and $a_i$ demands only $B_i$. The bridge is still tied. On either side of the switch every good is incident to exactly two buyers. Regarding each good as an edge between its two buyers gives a tree, with the two buyers of each block joined by $B_i$ and consecutive blocks joined by the goods $A_i$. Its deletion matchings are unique and reach the whole chain. They prescribe $\mathrm d p_{B_i}/\mathrm d p_{A_i}=q_i$ before a switch and $1$ after it. These are the slopes of the curve above.

The switches, in order $m,m-1,\ldots,1$, occur at the distinct values

\[
 x_i=\frac{\delta}{(q_i-1)\prod_{j<i}q_j}.
\]

Indeed $x_{i+1}<x_i$, so at $x_i$ all upstream blocks $j<i$ still have $p_{B_j}=q_jp_{A_j}$. Then $p_{A_i}=x_i\prod_{j<i}q_j$ is exactly the unique crossing for block $i$. The functions $F_j$ are strictly increasing, so each switch occurs once.

At the crossing all four edges of that square are tight. The tree for the post-switch side supports a matching for every deleted buyer. Any alternative matching for that same buyer differs from the tree matching by a flip on this square, the only cycle in the current demand graph. The alternative uses the prime-slope diagonal and has $q_i$ times the product of the post-switch matching. Thus the minimizers select the post-switch rates even at the tie.

For the root-deletion matching, no bridge can occur, by the prefix count. The minimum product starts at $\prod_i q_i$ and divides by $q_i$ at each switch, ending at one. No outside option catches until $p_{B_m}=2$, since the $F_i$ are nondecreasing and $p_{B_i}\ge p_{A_i}$. The endpoint is $x=2-m\delta>\delta=x_1$, with
\[
 (p_{A_i},p_{B_i})=(2-m\delta+(i-1)\delta,\ 2-m\delta+i\delta).
\]
The whole chain stays reached, and outside becomes reachable at the endpoint. This gives $m$ internal updates and $m+1$ positive updates in the single final insertion. For $m=2$, the root-deletion products are $6,2,1$ at $x=0,1/12,1/3$, and the final vector is $(4/3,5/3,5/3,2)$.

## Charge each internal update to a simple cycle

Consider any internal event of the deletion-matching ascent. The reached sets are unchanged from the incoming positive step. By strict minimum-product progress, some deleted buyer has an old minimum matching $M^-$ and a new minimum matching $M^+$ with a strictly smaller product. Both are supported on the event's tight graph. Their symmetric difference is a union of alternating simple cycles, so at least one cycle has unequal alternating slope products.

Traversing a tight buyer's tie from $j$ to $k$ gives
\[
 p_k=\frac{d_{ij}}{d_{ik}}p_j+\frac{b_{ik}-b_{ij}}{d_{ik}}.
\]
Composing around the cycle gives $p_j=G p_j+H$ with $G\ne1$. Thus every good on that cycle has a unique price fixed by the input. The cycle cannot witness a later internal event. Prices never decrease, and all goods of a later event's cycle strictly increase in its incoming step because they belong to the unchanged reached set of that step. Their prices would then exceed their pinned values. This adapts the fixed-margin cycle argument of B3a to deletion matchings. [B3a cycle consumption](B3a-fixed-flow-jump.md#the-cycle-consumed-at-fixed-margins)

It follows that the **total** number of internal events, across all insertions, is at most the number of simple cycles in the viable graph with nonunit alternating slope gain. Each insertion has at most $n$ reached-set expansions and one terminal event for $n$ goods. Each update has polynomial bit cost by A4i1b. Thus the same ascent runs in polynomial time on cactus graphs, including long cycle blocks. More generally, for biconnected blocks $D$ of cycle rank $h_D$, there are at most $\sum_D(2^{h_D}-1)$ simple cycles. Logarithmic cycle rank per block suffices even when the rank of the whole connected component is large. The bound of $m$ internal events on the chain is attained by the shaded bids. [Per-event bit bound](A4j-unit-matching-ascent.md#matching-values-bound-the-number-of-steps)

There is a stronger obstruction when the normalized viable bids admit common offsets $b_{ij}=A_i+d_{ij}C_j$. In the recentered coordinates $p_j-C_j$, every row tie is homogeneous. A nonunit-gain cycle then pins each of its prices to $C_j$. Each good on a charged cycle has reached a strictly positive price and can take part in at most one such charge over the run. Hence there are at most $|\{j:C_j>0\}|$ internal events. With row-constant intercepts one can take $C_j=0$, so arbitrary changes to the slopes or graph within this bid class still give zero internal events. This is a bound on the ascent for the common-offset class that A4e already solves by a signed-root transformation. [A4e common offsets](A4e-covering-lp.md#common-offsets-with-arbitrary-slopes)

## Exact replay and credit

Run the following from the repository root.

~~~sh
python3 -B experiments/a4j_deletion_product_replay.py
~~~

For $m=1,2,3,5,8,10$, the replay enumerates the $2^m$ root-deletion matchings of the control, checks all deletion minima, verifies the event prices of the shaded family, and checks both market endpoints. It separately enumerates every required deletion minimum and all strict Hall subsets at $m\le5$. The local reference solver's Git blob is `196a6515408e63a4e39af1cc41edd91987d151dc`, identical to the one at the comparison's commit. [Replay](../experiments/a4j_deletion_product_replay.py) · [Pinned solver](https://github.com/robbiemu/bayesian-simple-security-games/blob/74589d93e4b078608e0a8ddb4b1e86722634f9ee/experiments/a4j_unit_prices.py)

Robert Thomas Collins requested the follow-up. The Codex GPT-6.2 Astra subagent derived the shaded family and the B3a transfer. The coordinating Codex session independently checked their proofs and wrote and ran the separate replay. [Superpolynomial forced switches from a different incidence construction](A4j-forced-deletion-switches.md)
