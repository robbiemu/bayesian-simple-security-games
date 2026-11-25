# A4i. Exact affine-market clearing and one-resource games

**Theorem.** Finding the componentwise minimum clearing prices of an explicitly encoded rational affine assignment market reduces to finding an exact equilibrium of one strictly signed Bayesian simple security game with one defender resource. The construction can impose uniform type priors or unit defender gains in separate variants. The reduction needs only the defender's equilibrium strategy. The original market flow can be recovered by a rational circulation.

Together with L4b, this gives polynomial-time Turing equivalence between general exact game equilibrium and exact affine-market clearing. A1's fixed-total rent-division embedding and the earlier fixed-threshold correspondence handle different inputs. The construction below starts with arbitrary fixed market masses, capacities, and reserves and submits a game at a fixed integer budget. [A1 and the fixed-total embedding](A1-threshold-transport.md#6-a-fixed-total-assignment-reduction) · [L4b](L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle) · [Conitzer's explicit game model](https://arxiv.org/pdf/2610.08796#page=1)

## One padding target pins the relevant score

If there are no goods or no positive-mass buyers, the reserve vector is already the minimum and all mass can take outside. For the remaining inputs, remove the zero-mass buyers and normalize the market reserves and outside utility to zero. Write the offers as $b_{ij}-d_{ij}p_j$ with $d_{ij}>0$, the positive buyer masses as $m_i$, and $M=\sum_i m_i$. Increase each original capacity by A4c's rational supply perturbation, denoting the result by $c'_j>0$. Every clearing price of the enlarged market is the requested original minimum. [Exact recovery by supply perturbation](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

Let $n$ be the number of original goods and $R=\max(0,\max_{ij} b_{ij}/d_{ij})$. Choose $H=n(R+1)$. Use one target for each original good, an outside target $o$, and a padding target $a$. Take budget $r=1$. Choose a padding type of unnormalized mass $w>0$ and use $S=M+w$ for normalization. Original buyer $i$ becomes a type of prior $m_i/S$; the padding type has prior $w/S$.

- An original type's offer on an old target is $b_{ij}-H d_{ij}x_j$. Its outside-target offer is $-x_o$, and its padding-target offer is $-2-x_a$.
- The padding type has offer $1-x_a$ at its target and $-2-x_j$ at all others. It strictly prefers its target for every coverage.
- Give an old target gain $\beta_j=S/c'_j$, give $a$ gain $S/w$, and give $o$ gain $1/2$.

All attacker slopes and defender gains are strictly positive. In any equilibrium the padding score is one, and the outside score is at most $1/2$. If $x_o>0$, then $x_a<1$ and a move from $o$ to $a$ strictly improves the defender payoff. Thus $x_o=0$ and the outside offer is zero. If $x_a=0$, some old target has $x_j\ge1/n$. Its offer is strictly below outside for every original type, so its score is zero. Moving coverage from it to $a$ again improves the defender payoff. Thus $x_a>0$.

Every old target is below its cap. Moving a little coverage from $a$ to any old target gives $s_j\le1$ by defender optimality. If an old target has positive coverage, then $a$ is below cap and the reverse move gives $s_j\ge1$. Therefore

$$
 \sum_i S q_{ij}\le c'_j,\qquad
 \sum_i S q_{ij}=c'_j\ \text{if }x_j>0 .
$$

The prices $p_j=H x_j$ and temporary enlarged-market masses $S q_{ij}$ clear. Any flow to $o$ is original outside mass. To lift a market clearing, every old positive price is at most $R$ since the enlarged capacity is positive and an above-reserve good must sell out. Set $x_j=p_j/H$, $x_o=0$, and $x_a=1-\sum_j x_j>0$; use the rescaled market flows and the fixed padding attack. The same score relations give an equilibrium.

Every coefficient is a rational expression of polynomial binary length. The construction adds two targets and one type. The old price is recovered by multiplication and restoration of reserves. A4c and one original-capacity flow return the full original answer. Since the enlarged price is unique, the constructed one-resource game has a unique defender strategy. Its probabilities on single targets are its coverage marginals.

## Uniform priors with binary masses

Keep the outside and padding targets and add one private target $h_i$ for each original type $i$. Give every type, including the padding type, the same prior $\pi=1/(k+1)$. Set $\gamma=\pi/(1+M)$, so $0<\gamma m_i<\pi$. Give old good $j$ gain $1/(\gamma c'_j)$, give $h_i$ gain $1/(\pi-\gamma m_i)$, and take padding gain $1/\pi$ and outside gain $1/2$.

Keep the outside and padding offers above. Give type $i$ the private offer $B_i-T_i x_{h_i}$, where $B_i=1+\max(0,\max_j b_{ij})$ and $T_i=(n+k)(B_i+1)$. All other types have offer $-2-x_{h_i}$ on $h_i$. Now use $H=(n+k)(R+1)$ on old goods. The same exchange fixes $x_o=0$. If $x_a=0$, an old or private target has coverage at least $1/(n+k)$, hence no type demands it and moving coverage to $a$ improves the payoff. Thus $x_a>0$ as before, and all other scores are at most one, with equality on their positive coverages.

At $x_{h_i}=0$, type $i$ would strictly prefer $h_i$ and its score would exceed one. Hence $x_{h_i}>0$ and it receives exactly $\pi-\gamma m_i$ from that type. The remaining flow, of mass $\gamma m_i$, uses only old best offers and outside. Dividing by $\gamma$ gives the old row and column constraints. Conversely at an enlarged clearing with row utility $v_i$, set $x_{h_i}=(B_i-v_i)/T_i$ so that the private offer ties. All old and private coverages are below $1/(n+k)$, so their sum is less than one and the padding target absorbs the rest. The argument also pins each private coverage from the recovered original prices. Thus the defender strategy is again unique when using A4c first. The added targets and numbers have polynomial size even when the original masses have large denominators.

## Unit defender gains with binary capacities

Use the base construction with no recipient-specific gain. Pick $C=1+M+\max_j c'_j$. Give the padding type unnormalized mass $C$, and add one dedicated type of mass $C-c'_j$ at each old target $j$. Each dedicated type values its own target at $1-x_j$ and all alternatives at $-2-x_\ell$. All defender gains are one. Normalize all type masses by $S=M+C+\sum_j(C-c'_j)$.

The padding score is now $C/S$, and the outside score is at most $M/S<C/S$, so $x_o=0$. If coverage one were placed entirely on the old targets, some $x_j\ge1/n$ and that target would receive only its dedicated mass, giving score $(C-c'_j)/S<C/S$. Thus $x_a>0$. Every old score is at most $C/S$, with equality on positive coverages. Subtract the dedicated mass from each old total and multiply by $S$. The resulting physical column upper bound is $c'_j$, with equality above reserve. Each original row still has precisely its market mass. The lifting and price recovery use the same scaled coverages as in the base construction and add the fixed attacks of the dedicated types.

The two variants keep uniform priors and unit gains, respectively, with one defender resource and strictly signed payoffs. With unit margins, the next construction enforces both restrictions together. [Prior and gain parameters in the continuation](B3b-closed-group-rank.md#thresholds-and-changes-of-seed)

## Jointly uniform games and unit markets

**Corollary.** Exact minimum-price search for one affine market with unit buyer masses and unit good capacities is polynomial-time Turing equivalent to exact equilibrium search for Bayesian simple security games with uniform type priors and a common defender gain. The market-to-game direction takes one game call, with one defender resource and unit gains. Its added targets and types are linear in the numbers of original goods and buyers. The game-to-market direction uses polynomially many explicitly listed unit markets even when its intermediate capacities have large binary denominators.

### Uniform capacities have small exact representatives

Take $k$ unit buyers, $n$ goods of common positive capacity $c$, and any fixed rational reserves and outside utilities. At a trial price let $f(S)$ count buyers whose entire demand is in $S$, and let $h(S)$ count buyers who demand at least one good of $S$. A buyer tied with outside is excluded from $f(S)$. The clearing inequalities compare these integers with $c|S|$, using $h(S)$ only on sets of goods strictly above reserve. Consequently the full clearing-price set depends on $c$ only through its comparisons with

$$
 \mathcal R=\{a/b:0\le a\le k,\ 1\le b\le n\}.
$$

If $c$ is a member of $\mathcal R$, keep it. If it is between two adjacent members $a/b<a'/b'$, use their mediant $(a+a')/(b+b')$, which lies strictly between them. For $c>k$, take $k+1$. This gives the same comparisons, including all equality cases, with a representative $A/B$ having $B\le2n$ and $A\le2k+1$. Sort and compare these rationals in polynomial bit time. [Both Hall families](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

Multiply all the representative margins by $B$. Replace each buyer by $B$ identical unit buyers and each good by $A$ identical unit goods, retaining its reserve on every copy. At any clearing, copies of a good have a common price. Otherwise an expensive copy sits above its reserve and strictly loses to the cheaper copy for every buyer, so cannot sell. At common copy prices, aggregating allocations or distributing an aggregate flow among the copies gives the same demand and capacity conditions. Bipartite integrality supplies an integral allocation if needed. Thus the least price of the explicitly copied market projects to the least price at the supplied $c$. There are $O(kn)$ buyer and good copies. One original-capacity circulation recovers the requested allocation at the projected prices.

### Use a unit-market oracle at a supplied game budget

Normalize the common positive defender gain to one. Multiplying the attack flows by $k$ gives unit buyer masses. At positive defender threshold $\lambda$, L4b's market has common capacity $c=k\lambda$, reserve zero, and outside offer $o_i=\max_j(a_{ij}-d_{ij})$. Its clearing prices are exactly the possible game coverages at threshold $\lambda$. Compute the least at $c$ by the unit reduction above. The greatest at $c$ is the clearing vector after L4b's small decrease in every capacity. The smaller query has another positive common capacity, so the same unit reduction applies, however large the trial denominator. [Fixed-threshold market and extremal capacities](L4-newton-and-continuation.md#the-market-endpoints-of-one-threshold)

At an interior budget, first check the zero-threshold test from A1. Otherwise the largest threshold $\lambda^*$ attainable at the supplied budget is the upper endpoint of a fixed-coverage Hall interval. It is $a/(kb)$ for some $a/b\in\mathcal R$. The greatest coverage sum is at least the requested budget exactly at the positive thresholds at or below $\lambda^*$, by the strong threshold order. Binary search the sorted finite list with the greatest-price oracle, using $O(1+\log(kn))$ calls.

At $\lambda^*$, let $q$ be the greatest coverage. For $0\le t\le1$, compute the least prices at reserves $tq$ and the same capacities. These are still clearing prices of the zero-reserve market. They vary continuously and monotonically from the least vector to $q$, so their sum reaches the supplied budget. Each least-price call uses the same small capacity representative with the indicated reserves. The first crossing parameter is obtained by exact bisection and rational reconstruction. On each affine branch the least price is given by independent tight comparisons or reserve equalities from a supported flow. At the first interior crossing the branch on the left has a nonzero sum slope. Adding the budget equality gives a nonsingular system in the prices and parameter. Row clearing and determinant bounds give a uniform polynomial-bit denominator bound without enumerating the branches. The two endpoint cases require no bisection. A flow at the original capacity, with full-target overflow restored from outside, recovers the exact attacks. [Zero threshold](A1-threshold-transport.md#2-eliminate-coverage-through-type-values) · [Exact reserve and budget recovery](L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)

Budgets zero and full coverage are direct, since the defender's coverage is fixed. A zero common defender gain allows any feasible coverage. For positive gains and weak attacker slopes, A1's strict perturbation and exact repair change only the zero slopes before applying this reduction. They retain the uniform priors and common gain. [Weak-sign repair](A1-threshold-transport.md#4-transfer-an-exact-positive-coefficient-solver-to-weak-inequalities)

### Encode one unit market in one resource

Normalize each reserve and outside utility to zero, with real offers $b_{ij}-d_{ij}p_j$. Let $Q=2n$. The enlarged capacities $1+1/Q$ give a unique clearing price equal to the requested original minimum by A4c. The game will enforce these enlarged capacities by splitting a fixed attack total across padding targets. [Supply perturbation](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

Use $n$ old targets, $k$ outside targets, $Q$ padding targets, and one defender resource. There are $k$ original types and $Q+1$ padding types, all with prior $1/T$, where $T=k+Q+1$. Every defender gain is one. Set $H=n(1+\max(0,\max_{ij}b_{ij}/d_{ij}))$. Original type $i$ has offers $b_{ij}-H d_{ij}x_j$ on old targets, $-x_o$ on each outside target, and $-2-x_a$ on each padding target. Each padding type offers $1-x_a$ on the padding targets and $-2-x_j$ everywhere else. Padding types always attack padding targets, and original types always have an outside offer higher than any padding offer.

In equilibrium every outside target is uncovered. If some outside target is covered and another is uncovered, no row attacks the covered one, while some padding target has positive score and room below one. If every outside target is covered, each has score at least the highest padding score, which is at least $(Q+1)/(QT)>1/T$. The required total outside mass would exceed $k/T$. Both possibilities contradict optimality. Next, at least one padding target is covered. Otherwise budget one lies on the old targets and some old target has coverage at least $1/n$. All of its offers are strictly below outside, so moving coverage from it to a padding target of positive score improves the defender payoff. If a padding target were covered while another was uncovered, it would receive no attack, and another such improving transfer would be possible. Thus all $Q$ padding targets are strictly inside the coverage box and have common score $(Q+1)/(QT)$.

Every old target is below its cap, since some coverage is on padding. Therefore its score is at most this common score, with equality when its coverage is positive. With prices $p_j=Hx_j$ and the original rows' attack masses multiplied by $T$, the old capacities are exactly $(Q+1)/Q$. The outside offer is zero. This is a clearing allocation at the enlarged capacities. Recover the original minimum using A4c and recalculate the clearing flow at the original capacities.

Conversely, from an enlarged clearing take $x_j=p_j/H$ on old targets. Each positive sold price is at most $\max(0,\max b_{ij}/d_{ij})$, so $\sum_j x_j<1$. Split the remaining coverage equally across the padding targets and set outside coverages zero. Divide the original flow by $T$, split its outside flow evenly across the $k$ outside targets, and distribute the $Q+1$ padding types evenly among their targets. All used offers maximize their row utilities, and the score comparisons are exactly the required defender best response. This also identifies the decoded coverage in every equilibrium of the constructed game. Empty market sides can be solved at reserve directly. All coefficients and the sizes of the two encodings are polynomial in the original input.

### Open unit-market search

Kintali’s polynomial-time game solver and the reduction above give a polynomial-time algorithm for unit and binary-quantity markets. A4i1 asks for a direct market solver with unit buyer masses, unit good capacities and arbitrary positive rational slopes. Clearing denominators in the general case can require exponentially many unit copies. [Kintali’s short proof](https://shivakintali.github.io/papers/SecurityGames-short.pdf) · [Direct unit-market question](../investigation/A4i1.md) · [Quantity representation](A4c-any-clearing-equilibrium.md#what-the-published-algorithms-imply)
