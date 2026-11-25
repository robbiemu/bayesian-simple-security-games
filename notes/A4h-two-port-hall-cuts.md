# A4h9 · Joint Hall cuts at independent port quotes

At supplied boundary prices, solve the private markets conditionally and run one joint Hall test. A failed upper Hall cut excludes a region of boundary quotes even when private prices and demand edges change. The proof replaces the boundary goods in the cut by one auxiliary good. The same two-buyer example that obstructs a raw-load potential shows why the excluded region need not yield a valid linear separation for every completing quote. [Conditional representatives](A4h-boundary-dominance.md#one-price-representative-at-fixed-boundary-quotes) · [A4h9 branch queries](A4h-mixed-port-composition.md)

## Two crossing switches rule out a raw-load potential

Take two unit buyers with offers $(20-p_1,20-p_2)$ and $(20-p_1,24-2p_2)$, and outside zero. Near $(4,4)$ both buyers strictly prefer real goods to outside. Their switching lines are $p_1=p_2$ and $p_1=2p_2-4$. Away from the lines let $L(p)$ be the vector of the two uniquely determined loads.

Suppose a local homeomorphism $x=\Phi(p)$ made $-L(p)$ a convex subgradient in the $x$ coordinates. On each open demand cell the asserted subgradient is constant, so the subgradient inequalities in both directions make the function affine there. Across either switch, the affine gradients differ by $(1,-1)$ up to sign. By continuity the two affine functions agree on the image of the corresponding tie ray. Its image therefore lies in a line of normal $(1,-1)$. Since each ray approaches the crossing, all four images lie on the same line through $\Phi(4,4)$. A continuous injective image of each ray contains an interval ending at that point. On a line, two of the four intervals must overlap. This contradicts injectivity.

In particular, at a diagonal scaling $x_j=s_jp_j$ the first switch requires $s_2/s_1=1$ and the second requires $s_2/s_1=2$. The homeomorphism argument also covers smooth separate transformations with positive derivatives, and a fixed invertible linear transformation of the reported loads because the two jumps would still be parallel and nonzero. The conclusion concerns using these same loads as subgradient data. [Original fixed-scaling obstruction](A4h-mixed-port-composition.md) · [Exact rational switch checks](../experiments/a4h_two_port_replay.py)

## Project a failed Hall test to the boundary

Partition the goods into private goods $U$ and boundary goods $H$. Use reserves and outside options as in A4b, with $v_{ih}(t)$ the decreasing affine offer from good $h$ to buyer $i$. At a supplied boundary quote $x$, fold all boundary offers into each buyer's outside option and find the least private prices $q(x)$. Reinsert the boundary goods and test whether the combined vector $(q(x),x)$ admits a flow with all buyer masses and capacity upper bounds. Call such a vector buyer-feasible.

This tests whether **any** buyer-feasible completion exists at $x$. Indeed, the private coordinates $q'$ of such a completion satisfy $q(x)\le q'$. Buyers whose best utility strictly rises when the private prices fall from $q'$ to $q(x)$ can use only the private goods whose prices fell. Give these buyers their assignments from a conditional flow at $q(x)$. Keep the original assignments of all other buyers. They used none of the strictly cheaper goods, since that would have raised their utilities. This preserves all upper capacities and demands at the combined vector. The argument extends A4b's one-good coordinate test to a fixed group. [A4b conditional switch and strict minimum Hall](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)

If the joint test fails, extract a Hall witness $R\cup S$ with $R\subseteq U$, $S\subseteq H$. Its trapped buyer mass strictly exceeds $c(R)+c(S)$, where a buyer is trapped when every demanded option lies in this set. Here $S$ is nonempty because the private solve already permits unlimited boundary flow. For each buyer define
\[
 B_i(x)=\max_{h\in S} v_{ih}(x_h),\qquad
 O_i(x)=\max\left(o_i,\max_{h\in H\setminus S}v_{ih}(x_h)\right).
\]
When a buyer has no offer in $S$, omit her edge to the auxiliary good below.

Build an auxiliary market with the original private goods and one new good $g$ of capacity $c(S)$, reserve zero and offer $B_i(x)-z$ at its price $z$. Use outside option $O_i(x)$. When $z=0$, folding $g$ into outside recreates the private conditional market at $x$. At its private minimum the failed Hall witness becomes $R\cup\{g\}$, so the conditional switch rules out buyer feasibility at $z=0$. The auxiliary minimum therefore has $z^*>0$.

Now consider a boundary vector $y$ satisfying $O_i(y)\le O_i(x)$ for every buyer and $B_i(y)\ge B_i(x)$ for every buyer with an offer in $S$. If it had a buyer-feasible completion, fold $H\setminus S$ into outside and combine the flows on $S$ into the auxiliary good at price zero, using intercepts $B_i(y)$. Compare this candidate with the auxiliary minimum for $x$. Let $J$ consist of $g$ and every private good whose price is lower at the candidate than at that minimum. Every buyer who demanded an option in $J$ at the minimum now strictly improves on an option in $J$. Her outside option and all offers outside $J$ weakly worsen. She must use $J$ at the candidate. Strict minimum-price Hall gives more such buyer mass than the capacity of $J$, a contradiction.

Consequently the failed joint test certifies the following cut on every buyer-feasible completion:
\[
 \bigvee_{h\in S} (y_h>x_h)
 \quad\text{or}\quad
 \bigvee_{h\in H\setminus S} (y_h<x_h).
\]
The computation uses the private conditional solve and a single max-flow/min-cut at the supplied quote. The auxiliary market proves the cut without an extra solve. A passing test instead gives $p_H^*\le x$ by domination by the least price. The actual boundary capacities enter the joint test. For several branches, glue their demanded edges and impose the shared capacities once. A test using an exterior commitment gives a certificate for that prescribed exterior.

### Allow some motion in the opposite directions

Let $Q$ be a polynomial-bit bound on the reduced denominators of minimum prices in the auxiliary market. The minimum anchor-path bound applies with the new rational intercepts and outside options. Since $z^*>0$, it is at least $1/Q$. Choose $0<\eta<1/Q$. The same comparison excludes quotes with $O_i(y)\le O_i(x)$ for every buyer and $B_i(y)\ge B_i(x)-\eta$ for every buyer with an offer in $S$, because each auxiliary offer still strictly improves relative to the minimum. A known larger lower bound for $z^*$ also works.

For an explicit rectangle, choose one maximizing port $h_i$ from $S$ for each buyer with an offer there. Require $y_{h_i}\le x_{h_i}+\eta/d_{ih_i}$ and impose $v_{ih}(y_h)\le O_i(x)$ on every outside port offer. These are individual rational bounds on the boundary quotes. They can rule out trials with a higher price inside the cut and a lower price outside. [Rational anchor-path bound](A4b-direct-hall-search.md#exact-recursion-and-its-precision)

For a mixed separator, apply the same goods-only test to the A4h12 proxy market. An original shared buyer quote $u_i$ becomes a pinned price $K_i-u_i$. Every original clearing extends to a proxy clearing at these quotes, so the proxy cut excludes the corresponding original completions. The signs for shared utilities reverse when translating back. [Buyer proxy and exact clearing correspondence](A4h-buyer-proxy.md#replace-one-buyer-by-a-good-and-a-set-of-two-option-buyers)

## Exact examples and use in search

Give both ports and the private good unit capacity. Three unit buyers have offers $(6-p_1,6-p_2,8-p_g)$ and outside utility $4$. A fourth unit buyer can only use the private good, with offer $13/4-p_g$ and outside zero. At $(p_1,p_2)=(1,3)$ the private minimum is $p_g=3$. The joint cut $\{1,g\}$ traps all four buyers. The auxiliary good's minimum price is $1$. The expanded certificate with $\eta=1/2$ excludes $p_1\le3/2$ and $p_2\ge2$. The replay checks 63 grid points and the off-grid quote $(11/8,5/2)$, where the private minimum has risen to $27/8$ and the fourth buyer now takes outside. The same calculation works throughout the rectangle.

To see the aggregation of two boundary goods, take three unit buyers with identical offers $(4-p_1,4-p_2)$ and outside zero. Each port has unit capacity. At $(1,1)$ neither singleton traps a buyer, and the two ports together trap all three. The auxiliary good has capacity two and intercept three for each buyer, so its least price is three. Raising either port to $5/4$ while keeping the other at one changes the maximizing port and keeps the aggregate bid at three. The certificate still rejects both trials. [Joint-aggregation example from the review](https://github.com/robbiemu/bayesian-simple-security-games/pull/13#issuecomment-7165893201)

For the two buyers in the switching example, give each good unit capacity. The quote vectors $(25/8,7/2)$ and $(37/8,9/2)$ both clear. At their midpoint $(31/8,4)$ both buyers demand only good 1. A half-space containing both clearing quotes also contains the failed midpoint. The projected Hall cut there is $y_1>31/8$ or $y_2<4$, and the two clearing quotes satisfy different sides of the disjunction. A search that retains every completing quote needs the disjunction or a different certificate. A search concerned only with the least quote can also use lower bounds or other information about that particular solution.

Use the cut to prune quoted boxes, or to advance a known coordinate lower bound when the alternatives are already excluded. With just two boundary goods and tractable conditional interiors, A4b's nested coordinate tests already give polynomial-bit exact search, followed by an original joint circulation at the recovered minimum. The remaining question is how to choose polynomially many joint queries when the number of independently priced ports grows. The cut supplies a valid rejection region and preserves the supplied-market capacities. [Exact replay](../experiments/a4h_two_port_replay.py)

Robert Thomas Collins supplied the two-buyer example from a cross-project comparison inspired by the shortcut obstructions in Cinna Davis's research collection. OpenAI Codex checked the example, derived the homeomorphism obstruction and the projected Hall cut, and implemented the rational replay. [Davis complexity research](https://github.com/1337isnot1337/solved-conjectures/blob/fbc92006c4ce1d57ded60baa8e1e849f58293b39/CONTENTS.md#open-complexity-research)
