# A4h Counting rows of the all-capacity price table

**Theorem.** Given binary rational market data and a specified good \(h\), counting the maximal positive-length intervals on which \(p_h^*(x)\) is constant as its capacity \(x\) varies is NP-hard. This holds with unit slopes, zero reserves and outside utilities, and two viable offers per buyer. Counting strict jumps of the associated price-indexed minimum-load function is also NP-hard. The reduction uses one market and a comparison with a known integer. [Disser–Skutella, §3 and Corollaries 1.5 and 1.8](https://www2.mathematik.tu-darmstadt.de/~disser/pdfs/DisserSkutella18.pdf#page=17)

## A single reduction using parallel counters

For a PARTITION instance \(w_1,\ldots,w_n>0\) of integers, set \(\varepsilon=1/(24\sum_i w_i)\), \(a_i=\varepsilon w_i\), and \(T=2^{n+1}\). For \(0\le j<2^n\), let \(s_j=\sum_{i=1}^n(-1)^{\operatorname{bit}_{i-1}(j)}a_i\). Write \(Z\) for the number of \(j\) with \(s_j=0\), counting complementary sign assignments separately.

Build one §3.1 counter with perturbations \(v_i=a_i\) and one with \(v_i=-a_i\). In each counter, level zero is one arc of capacity 1 and cost 0. A level \(i\) adds two new terminals and four arcs of capacity \(F=2^{i-1}\). The two straight arcs have cost \(v_i/2\), and the two crossing arcs have cost \(F-1/2-v_i/2\). To verify its min-cost curve directly, at outer throughput \(x\) and inner throughput \(y\) the two groups carry \(x+y\) and \(x-y\) respectively. Every \(0\le y\le\min(x,2F-x)\) is possible by dividing each group equally. With \(b=F-1/2\), the cost is

\[
 b x+\min_{0\le y\le\min(x,2F-x)}
 \bigl[C_{i-1}(y)-(b-v_i)y\bigr].
\]

The previous maximum slope is at most \(F-1+\sum_{\ell<i}|v_\ell|< b-v_i\). Thus \(y=\min(x,2F-x)\) minimizes the expression. The first half shifts previous slopes by \(v_i\). The second half reverses their order and maps a previous slope \(m\) to \(2F-1-v_i-m\). The reversal complements the low \(i-1\) bits of the segment index. Induction gives successive slopes \(j+s_j\) in the positive counter and \(j-s_j\) in the negative counter, on unit-length throughput intervals. [Counter construction and Lemma 3.1](https://www2.mathematik.tu-darmstadt.de/~disser/pdfs/DisserSkutella18.pdf#page=8)

Identify the two sources and the two sinks to put the counters in parallel. Maximizing total throughput gives \(T\). At any fixed throughput the cheapest way to split it is to take marginal units in increasing cost order, since each counter's list already increases. The two slopes in the \(j\)-th pair lie in \([j-1/24,j+1/24]\). Different pairs cannot merge. Within a pair the slopes coincide exactly when \(s_j=0\), in which case the two unit segments merge. The resulting minimum-cost flow curve \(C(x)\) on \([0,T]\) has exactly

\[
 K=T-Z
\]

maximal affine pieces. In particular PARTITION has a solution exactly when \(K<T\). This construction uses \(O(n)\) vertices and arcs. The two counters admit a path decomposition of width three by taking successive pairs of levels in the first counter up to the shared terminals and then in reverse level order in the second counter. Its costs and capacities have polynomial binary length. Signed original arc costs cause no circulation problem because the constructed network is acyclic.

## What the published perturbation does

Corollary 1.8 names the §3.2 network and concludes using Corollary 1.5. The latter step requires splitting the connector \(e\). The unsplit §3.2 network already has \(T\) distinct marginal slopes for every instance. To see this, put \(\beta=\varepsilon/5\), the cost of both base arcs in §3.2. In a round \(j\) with \(s_j\ne0\), the two unit marginal costs from Lemma 3.2 are \(j+(-1)^j\beta-|s_j|\) and \(j+(-1)^j\beta+|s_j|\). When \(s_j=0\), the round instead has successive costs \(a<b\), where \(a=j+((-1)^j-1)\beta\) and \(b=a+2\beta\). The first unit uses \(e\) forward and the second uses it backward. Both counters have sent \(j\) units at the start of round \(j\), and \(e\) has zero flow at the even throughput checkpoints. A shortest residual augmentation gives an optimal interpolation up to its bottleneck. Hence these are slopes of the value curve as well as shortest-path costs. [Lemma 3.2 and its two parity cases](https://www2.mathematik.tu-darmstadt.de/~disser/pdfs/DisserSkutella18.pdf#page=10)

Here are explicit costs for the perturbation. Replace \(e\) by parallel arcs of capacity \(1/2\) and costs \(0,\delta\) with \(\delta=\varepsilon/100\). Before adding the cost \(\delta\), this split leaves all aggregate flows and costs unchanged. At a half-integer throughput an optimal vertex flow is half-integral, by scaling the ordinary incidence constraints by two. The old costs of those vertices are multiples of \(\varepsilon/20\), since the arc costs are multiples of \(\varepsilon/10\). Paying at most \(\delta/2\) can therefore only select among the old optima at such a throughput.

At an even throughput or any half-integer checkpoint in a nonsolution round, an old optimum has \(e=0\), using interpolation where needed. In the middle of a solution round at throughput \(2j+1\), every old optimum in the unsplit graph has \(e=1\). Indeed an optimum with \(e=0\) is impossible, since the independent counters would pay \(\beta\) more for that unit. The feasible vertices at this integer throughput are integral, so all old optimal vertices use \(e=1\). The split arcs then cost \(\delta/2\). At \(2j+1/2\) and \(2j+3/2\) an old optimum with aggregate \(e=1/2\) comes from interpolating the neighboring unit checkpoints, so the free half-arc suffices. There can be no knots at other abscissae. Adding a return arc with flow equal to throughput models the variable-throughput polytope as a circulation polytope, whose vertices are half-integral. Every vertex of its two-dimensional image comes from a vertex of that polytope.

Consequently each solution round now has four half-unit slopes \(a,a+\delta,b-\delta,b\) in strict order. Every other round keeps its two slopes, and different rounds still occupy disjoint costs. The split instance has \(T+2Z\) lower edges. The literal unsplit graph cannot give the intended threshold. The split graph gives the single threshold \(K>T\), using the same two base costs \(\beta\). [Corollaries 1.5 and 1.8](https://www2.mathematik.tu-darmstadt.de/~disser/pdfs/DisserSkutella18.pdf#page=17)

For the paper's projection onto throughput and cost, the **upper** envelope is the maximum-cost curve. The two outer bypasses in each counter cost \(2^{n-1}-1/2\) per unit, have total capacity \(T\) across both counters, and avoid the base arcs and connector. Every path bypassing at a lower layer is cheaper even after the signed cost shifts. A base or connector path costs at most \(\sum_i a_i+\beta+\delta<1/2\). Acyclicity thus gives the single upper edge of slope \(2^{n-1}-1/2\) before and after splitting. At zero throughput there is only zero flow. At \(T\) both counters' external arcs are saturated, so the flow across the connector must be zero by balance of the positive counter as a whole. All four outer arcs of each counter then saturate, leaving zero inner throughput. The lower and upper envelopes therefore meet at both endpoints, with no vertical edge. There are \(K+1\) projected vertices when the lower curve has \(K\) pieces. The market reduction below needs only the lower curve.

## Transfer to unit-slope prices

Use either of the preceding networks, with source \(s\) and sink \(h\). Make each vertex a good. An arc \(e=(u,v)\) of capacity \(U_e\) and cost \(\kappa_e\) becomes a buyer of mass \(U_e\) with unit-slope bids \(L+A_u\) at \(u\) and \(L+A_v-\kappa_e\) at \(v\). Set \(A_s=0\), \(A_v=R\) for \(v\ne s\), and take \(L,R>1+|V|\max_e|\kappa_e|\). Other bids can be zero. Each nonsink capacity is the sum of outgoing arc capacities, and only \(c_h=x\) varies. All data, including the threshold \(T\), have polynomial binary length even if zero bids are entered in a dense array. [A4h arc-to-buyer construction](A4h-complete-candidate-generation.md#a-single-boundary-table-and-a-two-dimensional-load-hull)

At a minimum-cost flow \(f\) of value \(x\), assign \(f_e\) to the head and \(U_e-f_e\) to the tail of each arc. Internal goods and the sink fill, and the source has slack \(x\). The residual graph has no negative cycles. Shortest-path potentials \(\lambda\) from an auxiliary zero-cost source, shifted to \(\lambda_s=0\), satisfy \(\lambda_v-\lambda_u\le\kappa_e\) when \(f_e<U_e\) and the reverse inequality when \(f_e>0\). Their magnitudes are at most \(|V|\max_e|\kappa_e|\). Therefore \(p_v=A_v-\lambda_v\) is nonnegative and supports the indicated choices, with the outside option strictly worse. It is a clearing assignment price at every \(0\le x\le T\). Summing the assignment bids and applying flow balance gives the welfare

\[
 W(x)=K_0+Rx-C(x),\qquad K_0=\sum_{e=(u,v)}U_e(L+A_u).
\]

The unit-slope assignment dual is a fixed pointed polyhedron whose objective depends on \(x\) only through \(xp_h\). Its optimum as a function of \(x\) is the minimum of the affine functions from its vertices. At a knot the least \(p_h\) among optimal solutions is attained at an optimal vertex, by minimizing \(p_h\) on the optimal face. The right derivative of the minimum is the smallest slope of an active affine function, so \(p_h^*(x)=W'_+(x)\), including at \(x=0\). On open segments this is \(R-C'(x)\). The total buyer mass incident to \(h\) is \(T\), so \(W\) is constant for \(x\ge T\) and \(p_h^*(x)=0\) there.

More explicitly, let \(0=x_0<x_1<\cdots<x_K=T\) be the knots of \(C\), let \(m_i\) be the slope on segment \(i\), and put \(\rho_i=R-m_i\). Then \(\rho_1>\cdots>\rho_K>0\), and the capacity-price plateaus are \([x_{i-1},x_i)\) with value \(\rho_i\). The domain \(0<x<T\) contains \(K\) positive-length plateaus. The domain of all nonnegative capacities adds one zero-price tail. Each convention gives a known threshold shift.

For trial price \(t\ge0\), let \(L_h(t)\) be the least boundary load with \(h\) uncapped and the other capacities enforced. The A4b coordinate test gives \(L_h(t)\le x\) exactly when \(p_h^*(x)\le t\). Thus

\[
 L_h(t)=\sum_{\rho_i>t}(x_i-x_{i-1}).
\]

At \(t=\rho_i\), the load is \(x_{i-1}\), with left limit \(x_i\). The price-indexed table has \(K\) strict drops, including the last drop to zero, or \(K+1\) rows when the initial and terminal levels are both listed. Hence counting either kind of table solves PARTITION in one call. At a **supplied** \(x\), a rational assignment LP and a second LP minimizing the price sum on its optimal face return the full least equilibrium, with polynomial-size LPs irrespective of \(K\). [A4b coordinate test](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price) · [A4a assignment dual](A4a-near-factorized-slopes.md#normalization-and-a-transferable-utility-oracle)
