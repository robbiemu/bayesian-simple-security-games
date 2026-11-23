# A4f. Price accuracy and scaling for affine markets

A price vector can be tested at a supplied tolerance by one circulation with the physical margins. At sufficiently fine tolerance, one LP recovers the exact minimum. Dyadic phases reach that tolerance in polynomial bit time when products of slope ratios along alternating paths are polynomially bounded. Each phase can use polynomial-size stable flow with binary masses and capacities. A fixed-tick auction provides a simpler implementation for unit markets. [PR review, precision interface](https://github.com/robbiemu/bayesian-simple-security-games/pull/8#issuecomment-7089066389) · [A4d support repair](A4d-p-matrix-complementarity.md)

## A price-only tolerance test

Normalize reserves and outside utilities to zero. Write \(v_{ij}(q)=b_{ij}-d_{ij}q_j\), \(v_{i0}=0\) for outside, and \(U_i(q)=\max_j v_{ij}(q)\) including outside. Let \(c'_j=c_j+1/(2nD)\) be the A4c supply increase, where \(D\) is a common denominator of the original margins. At \(q\ge0\), accept tolerance \(\eta\ge0\) if a circulation sends all mass \(m_i\) along edges with \(U_i(q)-v_{ij}(q)\le\eta\), respects the upper capacities \(c'\), and fills every good with \(q_j>\eta\). Outside is an ordinary option with no binding upper capacity. Evaluating this test takes one rational circulation. Its least passing tolerance is among zero, the offer slacks at \(q\), and the prices \(q_j\), so it can also be evaluated by binary search on that finite list. [Fixed-price circulation and supply increase](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

### One support LP at fine precision

Keep a passing circulation \(x\). In variables \(p,u,t\ge0\), require all exact covers \(u_i+d_{ij}p_j\ge b_{ij}\). On every real edge with \(x_{ij}>0\), bound its cover slack by \(t\). Impose \(u_i\le t\) if the buyer uses outside and \(p_j\le t\) if good \(j\) is underfilled at \(c'_j\). Minimize \(t\). The point \((q,U(q),\eta)\) is feasible.

All possible rows belong to one polynomial-size rational template. After clearing individual row denominators, let \(H\ge1\) bound the absolute entries including right sides. With \(a=k+n+1\) variables, \(Q=a!H^a\) bounds the denominators of all vertices by Cramer's rule. The LP has an optimal vertex since the variables are nonnegative and its feasible objective is bounded below. Any positive optimum is at least \(1/Q\). Thus \(\eta<1/Q\) gives optimum zero. The retained circulation clears at the resulting prices with the enlarged capacities. A4c identifies these prices with the original minimum \(p^*\). A second circulation with the original capacities recovers a clearing allocation. The tolerance and both circulation inputs have polynomial bit descriptions when \(q\) does. In particular the algorithm can choose a clearing matching in a unit market after recovery.

### Quantitative price bounds from Hall exits

Suppose \(q\) passes at tolerance \(\eta\), and set \(R=d_{\max}/d_{\min}\ge1\) for the available edges. Then

\[
 \lVert q-p^*\rVert_\infty
 \ \le\ \eta R^n(1+n/d_{\min}).
\]

For the upper bound on the prices set \(h=q-p^*\). Take any nonempty \(S\subseteq\{j:h_j>\eta\}\). The approximate flow sells all of \(c'(S)>c(S)\) in \(S\). Among the buyers sending positive flow there, some buyer \(i\) sends positive flow outside \(S\) at an original equilibrium at \(p^*\), because their total mass exceeds \(c(S)\). Let \(j\in S\) be one of her purchases at \(q\) and \(k\notin S\) a purchase or outside option she uses at \(p^*\). Comparing the two offers gives

\[
 d_{ij} h_j\le\eta+d_{ik} h_k,
\]

with the last term zero for outside. Hence the directed graph of these offer comparisons has an exit from every subset of \(\{h>\eta\}\). Starting at any such good there is a simple directed path of at most \(n\) arcs to outside or a good with \(h_k\le\eta\).

For the lower bound set \(h=p^*-q\). For any nonempty \(S\subseteq\{j:h_j>0\}\), strict minimum-price Hall at \(p^*\) gives neighboring buyer mass at least \(c(S)+1/D>c'(S)\). Some buyer who demands \(j\in S\) at \(p^*\) uses an option \(k\notin S\) at \(q\). Comparing those offers gives the same arc inequality, with an exit now to outside or \(h_k\le0\). In either direction, propagate the bound along the path using \(h_j\le\eta/d_{\min}+R\max(0,h_k)\). [Strict Hall at the minimum](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

The dependence on path length can be exponential even with slopes one and two. Take \(n\) unit goods and \(n+1\) unit buyers in path order. Buyer 0 offers \(1-p_1\). Buyer \(j\), \(1\le j<n\), offers \(3-2p_j\) and \(2-p_{j+1}\). Buyer \(n\) offers \(2-p_n\). The minimum is \(\mathbf1\), by clearance and strict Hall. At enlarged capacities \(1+\delta\) each buyer \(j\ge1\) sends \(1-(n-j)\delta\) to good \(j\), and for \(j<n\) sends \((n-j)\delta\) to good \(j+1\). Buyer 0 sends \(n\delta\) to good 1 and the rest outside. With \(q_j=1-2^{j-1}\eta\) and \(\eta=2^{-n}\), the same flow passes at tolerance \(\eta\). Interior ties persist and only buyer 0's outside use has positive regret. The last price is off by \(1/2=2^{n-1}\eta\).

The tolerance test can also have disconnected pieces on a price segment. Take two unit goods, three unit buyers, and offers

| Buyer | Good 1 | Good 2 |
| --- | --- | --- |
| A | \(4-4p_1\) | omitted |
| B | omitted | \(8-4p_2\) |
| C | \(5/2-p_1/2\) | \(5/2-p_2/2\) |

The original minimum is \((1,1)\) by strict Hall. At the A4c capacities \(5/4,5/4\), this price clears with A sending \(1/2\) to good 1 and \(1/2\) outside, B sending one to good 2, and C splitting \(3/4,1/4\). At \(q=(0,2)\) and \(\eta=1\), buyer A uses good 1, C sends \(1/4\) to good 1 and \(3/4\) to good 2, and B sends \(1/2\) to good 2 and \(1/2\) outside. At the midpoint \((1/2,3/2)\), all three buyers have utility at least two and therefore cannot take outside at tolerance one. Their mass exceeds the two enlarged capacities. Thus an exact endpoint and a passing price can have a failing midpoint.

## Scale price contracts at binary physical margins

**Theorem.** In normalized coordinates define \(r_i\) as the ratio of largest to smallest slope on the viable offers of buyer \(i\), or one for a row with at most one viable offer. Let \(C\) be \(n+1\) times the product of the \(n\) largest ratios, or all ratios if fewer. There is an algorithm for arbitrary binary rational masses and capacities with bit time polynomial in \(L\) and \(C\), where \(L\) includes any supplied scales. The LP normalization below gives a polynomial algorithm when every row can be scaled to spread \(1+O(\log n/n)\).

### A phase with an explicit contract list

Use the enlarged capacities \(c'\). Start a phase with a box \([\ell,u]\) containing \(p^*\). For each good \(j\), list prices in increments \(\Delta\) starting at \(\ell_j\) and ending at the first grid price \(H_j>u_j+C\Delta\). A buyer can purchase that good under any listed contract where her offer is positive. Rank her contracts by descending utility and rank each good's contracts by descending price. Break equalities by a fixed order. Buyers and goods keep the original masses and enlarged capacities as their quotas.

Compute any stable flow in this ordinal network. Put capacity \(m_i\) on the arc from source to buyer \(i\), \(c'_j\) from good \(j\) to sink, and one two-arc path from buyer to good through a private vertex for each contract. Each of the two arcs has capacity greater than the entire buyer mass. The buyer ranks first arcs of her paths, and the good ranks last arcs. Flow conserves the contract amount at its private vertex. A positive contract that would improve an unsaturated buyer or improve on a used contract at that buyer, and would likewise fill a slack good or improve on a used contract there, gives a blocking walk. Start at the source for an unsaturated buyer and end at the sink for a slack good. The stable-flow algorithm gives an allocation with no such walk using polynomially many operations in the explicit network. Clearing denominators of capacities at the start gives integer flow arithmetic with polynomial bit lengths. [Cseh and Matuschke, Definition 2 and Theorem 2](https://arxiv.org/pdf/1309.3701#page=12)

Decode \(q_j\) as the floor if good \(j\) is slack and its lowest used quote otherwise. Thus \(q_j\) is at most the quote of every buyer using \(j\). For a buyer using \(j\), and every good \(k\) with \(q_k<H_k\), stability gives

\[
 v_{ij}(q_j)\ge v_{ik}(q_k)-d_{ik}\Delta.
\]

The alternative contract priced \(q_k+\Delta\) would fill slack capacity or displace a lower quote, and if it strictly improved on her existing contract it would block. When the alternative has nonpositive utility the inequality already holds. A buyer with unspent mass has the same bound with zero on the left. Outside as an alternative gives a zero right-hand side.

### Exit paths certify the new box

For \(h=q-p^*\) and a nonempty set \(S\subseteq\{h>0\}\), every good of \(S\) sold its enlarged capacity since its quote exceeds its floor. Some buyer using a good \(j\in S\) thus buys an option \(k\notin S\) at the original minimum with the original capacities. Otherwise the mass of buyers touching \(S\) would exceed its original stock. Use an arc \(j\to k\) for every such pair of purchases from the two allocations. For an uncapped real destination \(k\), the preceding inequality implies

\[
 h_j\le (d_{ik}/d_{ij})(h_k+\Delta).
\]

For an outside destination the bound is \(h_j\le0\). Every subset of the positive difference set has an exiting arc. On any shortest path to its complement the buyers labeling the arcs are distinct. A repeated buyer permits a shortcut from her earlier current purchase to her later original purchase.

To rule out a quote at its cap, take a shortest path from the set of all capped goods to outside or a nonpositive difference. Every destination on the path is uncapped because reaching a second capped good would give a shorter suffix from that set. Thus the inequality applies along the whole path and gives \(h_{\mathrm{start}}\le C\Delta\). The starting cap was strictly above \(u_j+C\Delta\), so no quote is capped. The same argument from any positive difference gives \(h_j\le C\Delta\).

For \(s=p^*-q\) and \(S\subseteq\{s>0\}\), strict Hall at the original minimum gives neighboring buyer mass strictly above \(c'(S)\), by the original denominator grid. Some buyer demanding a good \(j\in S\) therefore uses a current option \(k\notin S\) or has unspent mass. Use an arc for each such demand and current option. The bound now is \(s_j\le\Delta+(d_{ik}/d_{ij})s_k\), or \(s_j\le\Delta\) for unspent mass. A repeated buyer again gives a shortcut, from her earlier exact demand to her later current purchase. These paths give \(s_j\le C\Delta\), so the new box is \([\max(0,q-C\Delta),q+C\Delta]\).

Start with zero lower bounds and upper bounds given by the largest willingness to pay. Take the first dyadic mesh at least the largest upper bound and at least one. Halve it each phase. The initial box and the proved width bound give \(O(C+1)\) quote levels per good at every phase. All integer capacity scales and grid denominators have polynomial bit lengths. When \(\eta=\max(1,2d_{\max})C\Delta<1/Q\), a clearing flow at \(p^*\) for the enlarged margins demonstrates that the price-only tolerance test passes at \(q\). Its circulation and support LP recover the exact minimum, with an original-capacity circulation to recover the allocation. The number of phases is logarithmic in \(1/\eta\) and in the encoded constants. The slope promise is independent of capacities and survives reserve increases, which can only remove viable edges. The algorithm therefore supplies the oracle in L4b's exact budget search when its induced market has that slope promise. [L4b exact budget recovery](L4-newton-and-continuation.md#exact-threshold-and-budget-recovery-with-a-clearing-oracle)

## Price ticks with dyadic restarts for unit markets

**Theorem.** For a supplied unit market, consider any rational normalization of buyer utilities and good prices by positive row and column scales. In normalized coordinates let \(r_i\ge1\) be the ratio of largest to smallest slope on buyer \(i\)'s viable offers, with \(r_i=1\) for a buyer with at most one viable offer. Let \(C\) be \(n+1\) times the product of the \(n\) largest \(r_i\), or all ratios if fewer. The algorithm below computes exact minimum prices in \(C\operatorname{poly}(L)\) bit time. In particular it is polynomial when this product is polynomially bounded. It discovers the support from the supplied market.

### A phase and its two bounds

Start with an empty matching and price floors \(\ell\le p^*\). Fix an increment \(\Delta>0\). Select a free buyer. If her best offer is nonpositive, send her outside. Otherwise choose a best real good, allocate it to her, raise its price by \(\Delta\), and free any previous owner. Prices only rise, so decisions to take outside persist. A buyer holding good \(j\) is at most \(d_{ij}\Delta\) behind her current best utility throughout that tenure. This holds immediately after the one tick and survives increases in other goods' prices.

**Upper bound during a phase.** Fix an integral matching \(M^*\) at the true minimum for the proof. At a pending bid by \(i_0\) on \(j_0\), let \(h=q-p^*\) at the pre-bid prices. If \(i_0\) takes outside in \(M^*\), her positive bid gives \(h_{j_0}<0\). Otherwise follow her good in \(M^*\), its current owner, that owner's good in \(M^*\), and so on. The trail ends at an outside assignment in \(M^*\) or an unowned good still at its floor. Both matchings are injective on real goods and the initial buyer is free. A repeated buyer or good would force a repeat backwards to a current owner equal to the free root, so the trail is simple.

At the root the best-offer inequality gives \(d_{i_0j_0}h_{j_0}\le d_{i_0k}h_k\) for her good \(k\) in \(M^*\). For an incumbent \(i\) on \(j\) with good \(k\) in \(M^*\), the guarantee during her tenure gives \(h_j\le\Delta+(d_{ik}/d_{ij})h_k\). An incumbent taking outside in \(M^*\) instead gives \(h_j\le\Delta\). A free terminal good satisfies \(h_k\le0\). The ratios along the trail use distinct buyers and at most \(n\) ratios. Substitution and addition of the new tick give \(q_{j_0}\le p^*_{j_0}+C\Delta\) after every bid. This also proves phase termination since each good rises by a fixed positive increment from its floor.

**Lower bound at termination.** Put \(s=p^*-q\) for the terminal prices. Every nonempty \(S\subseteq\{j:s_j>0\}\) has more neighbors in exact demand at \(p^*\) than goods. Some such buyer with \(j\in S\) in her exact demand is assigned outside \(S\) in the phase's matching. If her assigned good is \(k\), the tenure guarantee yields

\[
 s_j\le(d_{ik}/d_{ij})(s_k+\Delta).
\]

An outside assignment gives \(s_j\le0\) directly. The resulting graph has an exit from every such \(S\), so each positive \(s_j\) has a simple path to a nonpositive terminal difference. Along it, real assigned goods are distinct, hence so are the buyers whose ratios appear. The same product bound yields \(s_j\le C\Delta\). Together the bounds give \(\lVert q-p^*\rVert_\infty\le C\Delta\).

### Restart, normalization and exact recovery

Begin at zero with a dyadic \(\Delta_0\ge\max(1,\max_{ij} b_{ij}/d_{ij})\), within twice that bound. Each good receives at most \(1+C\) bids in the first phase. After a phase, use floors \(\max(0,q_j-C\Delta)\) and halve \(\Delta\). These floors are at most the true minimum and at most \(2C\Delta\) below it. The next phase uses at most \(5C\) bids per good.

At a terminal phase choose \(\eta=\max(1,2d_{\max})C\Delta\) in the normalized market. Compare the clearing flow at \(p^*\) for the enlarged capacities to the terminal vector \(q\). Every edge of the clearing flow has regret at most \(2d_{\max}C\Delta\) at \(q\), and every good with \(q_j>\eta\) had positive price and sold out at \(p^*\). Thus the price-only circulation test passes. Once \(\eta<1/Q\), its support LP and original clearance return the exact minimum. Undo the normalization. There are \(O(1+\log(\Delta_0 C\max(1,2d_{\max})Q))\) phases. All price coordinates are floors plus integer multiples of a dyadic tick, with denominators dividing the denominator of \(C\) times the current dyadic grid denominator. Price magnitudes and the coefficient bit lengths are polynomial in the input and supplied scales. The two flow calls and one support LP use rational data of polynomial bit length.

### Find suitable price scales

To find a normalization with row spreads bounded by a supplied \(\rho\), solve the rational feasibility LP

\[
 x_i\le d_{ij}y_j\le\rho x_i,\qquad x_i,y_j\ge1
\]

on viable offers. Use normalized prices \(p_j/y_j\) and utilities \(u_i/x_i\). Any feasible positive scales can be multiplied by a common constant to satisfy the lower bounds, and the LP gives polynomial-bit scales. A geometric grid \(\rho=(1+1/n)^a\), with \(a=0,\dots,O(nL)\), permits a binary search for a feasible bound within factor \(1+1/n\) of the best uniform spread. This gives polynomial time when \(\rho^n\) is polynomial, including \(\rho=1+O(\log n/n)\). In a market with the repeated slope pattern \((1,\rho)\) and \((\rho,1)\) on pairs of columns for two buyers, the sum of the two A4a normalized-column error terms on each pair is at least \(1-\rho^{-2}\) for every row scaling. Indeed, writing their row-scale ratio as \(t\), the two terms are one minus the smaller of \(t/\rho\) and its reciprocal, and one minus the smaller of \(t\rho\) and its reciprocal. Their sum is minimized at \(t=\rho\) or \(t=1/\rho\). With \(\rho=1+\lfloor\log_2 n\rfloor/n\) and sufficiently many pairs, the sum exceeds one, while the normalization \((x,y)=(\mathbf1,\mathbf1)\) gives a polynomial phase size. [A4a column error criterion](A4a-near-factorized-slopes.md#a-wider-region-by-a-weighted-euclidean-norm)

### A long phase under the global restart bound

Take a good \(g\) with two dedicated unit buyers offering \(1-p_g\), and attach \(m\) disjoint two-by-two markets by one low viable bid on \(g\) from each. Each attached market uses slopes \((1,2;2,1)\) and intercepts \(1/2\). Set the linking intercept to \(1/4\) with unit slope. Each square has an alternating slope ratio of four or its reciprocal, so the two row spreads have product at least four after any column scaling. Thus the global \(C\) is at least \((n+1)4^m\), with \(n=2m+1\).

In original coordinates each completed phase has \(1\le q_g\le1+\Delta\). Some dedicated buyer finishes outside, and every bidder on \(g\) bids below price one before the tick. Run to a dyadic phase with \(2/C\le\Delta<4/C\). The next floor on \(g\) is zero. At mesh \(\Delta/2\) the next phase needs at least \(2/\Delta>C/2\) bids on \(g\). This bounds the specified global-floor restart rule when run to that precision. A per-good reset or larger safe ticks remain possible improvements.

## Reuse a certified price box

At any certified box, test whether each offer can be demanded at some price in that box. The test is a rational LP using the original row comparisons. An offer that fails this test is absent from demand at \(p^*\). Deleting all such offers preserves clearance at \(p^*\) with the enlarged capacities, so A4c makes \(p^*\) the reduced market's minimum as well. The next scaling phase can use the reduced graph's slope ratios and price scales. If scales change, transform the certified box coordinatewise and choose the phase mesh from the transformed width. This gives a way to exploit priced-out offers. A bound on the work needed to reach a suitably sparse box in an unrestricted market remains open.

The unit replay checks 19,750 bids and 2,160 phases against the exact solver and strict Hall. The rational replay checks 1,400 phases on 100 markets, including zero capacities and fractional quantities, for both proposer sides. It generates the small reference allocations by token expansion. The bit-time theorem uses the cited stable-flow algorithm on the physical quotas. [Unit replay](../experiments/a4f_unit_tick_scaling.py) · [Rational replay](../experiments/a4f_contract_scaling_replay.py)
