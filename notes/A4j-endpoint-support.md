# Find a matching at the minimum prices

After PR #8, the question is to find one matching supported at the unknown componentwise minimum of a supplied unit market. A proposed matching takes one LP to finish. The two bounds below give ways to find one on additional classes. The first produces a list of matchings before solving for prices. The second bounds the number of events in the existing ascent. [PR review](https://github.com/robbiemu/bayesian-simple-security-games/pull/8#issuecomment-7089066389) · [Deletion-matching ascent](A4j-unit-matching-ascent.md)

Normalize reserves and outside utilities to zero. Let \(H\) be the graph of viable offers \(b_{ij}>0\), with slopes \(d_{ij}>0\). At a fixed clearing price, the unit capacity and mass circulation admits an integral matching. A purchase on a nonviable edge can be replaced by outside because it must occur at reserve and tie outside.

## One representative per normalization choice

Give each buyer \(i\) a nonempty finite list \(A_i\) of positive rational utility multipliers and each good \(j\) a nonempty finite list \(C_j\) of positive rational price multipliers. Require that for each viable edge \((i,j)\), some \(a\in A_i\) and \(c\in C_j\) satisfy \(a d_{ij}=c\). This is an edgewise test. For every simultaneous choice \(a_i\in A_i,\ c_j\in C_j\), keep the edges on which \(a_i d_{ij}=c_j\). Compute one maximum-weight partial matching on those edges with weight \(a_i b_{ij}\). Keep that matching as the choice's representative.

**Completeness.** Fix any clearing prices \(p\), utilities \(u\) and an integral clearing matching \(M\). For each edge of \(M\), choose its two multipliers to make the edge eligible. The choices are independent because \(M\) is a matching. Choose arbitrary values on unmatched vertices. For any eligible partial matching \(N\), the original covering inequalities give

\[
  \sum_{ij\in N}a_i b_{ij}
  \le \sum_{ij\in N}(a_i u_i+c_j p_j)
  \le \sum_i a_i u_i+\sum_j c_j p_j.
\]

The matching \(M\) attains both bounds. Every maximum-weight matching for this choice therefore also attains both. The first equality makes every edge it uses tight in the original market. The second forces it to cover every buyer with positive utility and every good with positive price. It clears at \(p\). This proves that the representatives cover the entire original clearing-price set, including the minimum.

**Recovery.** For each representative, solve the LP in \(p,u\ge0\) with all original covers \(u_i+d_{ij}p_j\ge b_{ij}\). Impose equality on the representative's edges, \(u_i=0\) on unmatched buyers and \(p_j=0\) on unmatched goods. Minimize \(\sum_j p_j\). Every feasible point clears with the representative. The LP for a representative supported at the componentwise minimum attains that minimum. Take the feasible optimum of smallest price sum across the list. All choices use the original unit capacities. For \(K=\prod_i |A_i|\prod_j |C_j|\), there are \(K\) assignment calls and at most \(K\) original support LPs. The rational coefficients have bit length polynomial in the market and lists. No price samples enter the selection.

For a directly computable version, fix any known positive row scales \(\alpha_i\). Put \(A_i=\{1/\alpha_i\}\) and let \(C_j\) be the distinct normalized slopes \(d_{ij}/\alpha_i\) in column \(j\), or \(\{1\}\) if it has no viable edge. If every column but \(h\) has just one normalized slope, and the remaining columns have at most \(s\) each, there are at most \(s^h\) matchings to test. This gives polynomial time when \(h=O(\log L)\) and \(s\) is constant, even if each exceptional column has large viable degree.

### Find lists by one bipartite cut

Start from any positive rational baseline \(a_i^0,c_j^0\), such as all ones. For each edge with residual \(r=a_i^0d_{ij}/c_j^0\ne1\), join the auxiliary label vertices \((i,r)\) and \((j,r)\). Selecting the buyer label adds \(a_i^0/r\) to \(A_i\). Selecting the good label adds \(r c_j^0\) to \(C_j\). Either choice represents that edge using the other endpoint's baseline. Edges with residual one already have their baseline representation.

One minimum vertex cover of this bipartite graph gives the smallest number \(B\) of extra labels that cover the residual edges through these specified alternatives. The graph has at most two vertices per residual edge and the usual unit-capacity cut computes the cover. Include the baseline at every physical vertex. The number of representatives is at most \(2^B\), since \(1+t\le2^t\) for \(t\) extra labels at one vertex. This yields a fully specified polynomial procedure on instances for which the chosen baseline gives \(B=O(\log L)\). The cover does not have to optimize over baselines or coincident representations that use two extra labels.

The cover can also minimize the actual product \(K=\prod_v(1+t_v)\) over these alternatives, where \(t_v\) is the number of selected labels on physical vertex \(v\). Use the source side to mean selected for buyer labels and unselected for good labels. An arc from the good label to the buyer label enforces each cover constraint. Give these arcs capacity above the sum of all other capacities. For a group of \(m\) labels on one physical vertex, with \(s\) source-side labels, the log of its factor is \(g(s)=\log(1+s)\) on the buyer side and \(g(s)=\log(1+m-s)\) on the good side. Both sequences are concave. With \(h_t=g(t)-g(t-1)\), write

\[
 g(s)=g(0)+h_m s+\sum_{t=1}^{m-1}(h_t-h_{t+1})\min(s,t).
\]

A term \(\lambda\min(s,t)\) uses one auxiliary vertex. Give it an incoming arc of capacity \(\lambda\) from each label in the group and an outgoing arc of capacity \(t\lambda\) to the sink. Minimizing over its side of the cut yields the term. A positive linear coefficient uses arcs from the labels to the sink. A negative coefficient uses arcs from the source to the labels and a constant.

The cut can use integer capacities. If \(E\) is the number of residual edges and \(V\) the number of physical vertices, every product is at most \(U=2^{2E}\) and distinct log products differ by at least \(1/U\). Every strict discrete second difference of a group log has magnitude at least \(1/(E+1)^2\). Multiply the group log values by \(16(V+1)U(E+1)^2\) and approximate each to within one by an integer. The scaled second differences stay negative and the total errors cannot reverse distinct product orders. Such log approximations use polynomial bit time, as in A4c's rational cost argument. Build the cut from these integer sequences. This selects lists with minimum \(K\) among the specified covers, even if some physical vertices receive many labels. [Rational logarithm evaluation](A4c-any-clearing-equilibrium.md#a-polynomial-local-search-on-fractional-transportation-supports)

For example, take a complete market with \(h\) exceptional columns. Column \(j\) uses a distinct prime \(r_j\) on odd rows and one on even rows. All other columns use one. The all-one baseline gives \(B\le h\). If there are at least \(h\) ordinary columns, pair each exceptional column with a different ordinary one. Pair consecutive rows within each such pair of columns. The resulting \(h\lfloor k/2\rfloor\) unbalanced four-cycles are edge-disjoint. Thus \(h=\lfloor\log_2 n\rfloor\) can give a polynomial candidate list even when making the slopes factorable requires deleting \(\Omega(k\log n)\) offers.

## Count matching products using the rank of the cycle gains

The cycle gain of an even cycle is the ratio of the two alternating products of its slopes. Let \(r\) be the rank of the multiplicative subgroup of positive rationals generated by all cycle gains. There is an exact unit-market algorithm with bit running time \(L^{O(r+1)}\). The rank is computable in polynomial time. Rank zero is the factorized case.

On each connected component of \(H\), propagate positive rational factors \(\alpha_i,\beta_j\) along a spanning tree so that \(d_{ij}=\alpha_i\beta_j\) on its edges. The residual slopes \(g_{ij}=d_{ij}/(\alpha_i\beta_j)\) are one on tree edges and are the fundamental cycle gains or their reciprocals on the other edges. The alternating products of the residual slopes generate the same subgroup as the original gains. These residual slopes have polynomial bit length.

Compute a coprime basis for the positive numerators and denominators of the residual slopes. Write each \(g_{ij}=\prod_h q_h^{v_{ij,h}}\) for pairwise coprime integers \(q_h>1\), with integer exponents. The exponents have polynomial magnitude, since reduction cancels any basis factor that would otherwise occur in both numerator and denominator. The basis represents distinct exponent vectors by distinct rationals. Thus the rank of the exponent vectors over \(\mathbb Q\) equals \(r\). Row reduction selects \(r\) coordinates on which projection is injective on their span. This step uses gcd and exact division through the coprime basis construction and does not need prime factorization. [Bernstein, factoring into coprimes](https://cr.yp.to/lineartime/dcba-20040404.pdf)

During one reached-set phase of the ascent, consider matchings of the fixed reached goods to the fixed reached buyers with one specified free buyer. All matching products have the same factor \(\prod_i \alpha_i\prod_j \beta_j\), where the buyer product omits that free buyer. Each residual product is determined by the sum of the exponent vectors on the matching. Its projection has \(r\) integer coordinates, each of absolute value at most \(sB\) for \(s\) goods and a bound \(B\) on individual exponent magnitudes. There are at most \((2sB+1)^r\) product values. An internal event strictly decreases at least one of the free-buyer minimum products and increases none. The ascent's bound on the numbers of insertions and reached-set phases, and its per-event bit bound, now give the stated runtime. Use its final matching or one original circulation to recover the allocation. The algorithm can run without first checking the rank.

In the complete \(k\)-buyer, \(n\)-good example with slope two on odd–odd pairs and one elsewhere, the rank is one. Pair consecutive buyers and goods to see \(\lfloor k/2\rfloor\lfloor n/2\rfloor\) edge-disjoint unbalanced four-cycles. A slope-factorization deletion must hit each, so sparsity of exceptions is not needed by this bound. A related special case in rent division controls an assignment potential when slopes are powers of a common base. Here the counted objects are the residual cycle gains after arbitrary row and column normalization, with a fixed number of independent generators allowed. [Arunachaleswaran, Barman and Rathi, Theorem 5](https://arxiv.org/pdf/1807.04163#page=24)

## Test a supplied price box

Let \([\ell,h]\) contain \(p^*\). Pad the unit market to a square assignment with one outside slot per real buyer and one dummy buyer per real good. Outside slots give zero. A dummy buyer's offer on good \(j\) is \(-s_jp_j\) for any \(s_j>0\). A clearing matching extends to a perfect assignment that attains every row's individual maximum. Dummies can purchase only zero-price goods in such an assignment and hence enforce the seller condition.

Write \(V_M(p)\) for the total affine value of a padded assignment \(M\). Find one maximizing assignment \(M\) at the relative midpoint of the box. To find its worst rival anywhere in the box, use one further assignment in which edge \(ij\) has weight

\[
 b_{ij}-b_{m_j j}+
 \max\{(d_{m_j j}-d_{ij})\ell_j,\ (d_{m_j j}-d_{ij})h_j\},
\]

where \(m_j\) owns column \(j\) in \(M\). Use zero intercepts and slopes on outside slots. Each rival uses one edge per column, so its maximizing prices can be chosen independently. The optimum is exactly \(\max_{p,N}(V_N(p)-V_M(p))\). If it is zero, \(M\) attains every row's maximum at \(p^*\). Its original support LP recovers the minimum. If any common maximizing assignment exists on the box, every relative-midpoint optimum has the same affine value on the box. Indeed their affine difference is nonpositive everywhere and zero at an interior point of the affine hull. Thus the test decides whether this common-assignment certificate exists. A failed test gives a price at which a rival beats \(M\).

The test can fail even in the box from zero to the exact minimum. Take offers \((3-p_1,4-3p_2)\), \((4-3p_1,3-p_2)\), and \((1-p_1,1-p_2)\). At \((1,1)\) the first two buyers strictly demand their respective goods and the third ties both with outside. Strict Hall gives the minimum. At zero, swapping the first two buyers strictly improves each of their values, so a common optimizer across the two prices is impossible, even under any positive rescaling of real rows.

### Exclude a matching edge with one LP

For a restricted padded graph \(G\), for example with a particular edge required, ask whether its perfect assignments can ever maximize the full assignment value across the box. An empty perfect-matching set can be rejected immediately. For a fractional perfect assignment \(X\) on the full padded graph, put \(B(X)=\sum b_{ij}X_{ij}\) and \(s_j(X)=\sum_i d_{ij}X_{ij}\). Minimize

\[
 \sum_i \alpha_i+\sum_j\beta_j-B(X)
\]

over \(X\) with unit row and column sums and over free \(\alpha,\beta\), imposing

\[
 \alpha_i+\beta_j\ge b_{ij}+(s_j(X)-d_{ij})t
 \qquad (ij\in G,\ t\in\{\ell_j,h_j\}).
\]

By assignment duality and the same columnwise maximization, its value is \(\min_X\max_{p,N\subseteq G}(V_N(p)-V_X(p))\) over perfect rivals \(N\). If negative, every rival is strictly below the value of a feasible fractional assignment at every price in the box, so none is optimal in the full assignment there. This certifies exclusion from the matching search. Retain the excluded offers in the final cover LP. A nonnegative value leaves the edge open. Testing each forced edge takes one polynomial-bit LP per edge. This gives a way to prune the multiplier lists' matching search using endpoint price bounds even when the box has several maximizing assignments.

## Open endpoint step

Requiring a representative at every clearing price can itself make the list exponential. One two-good block has offers \((4-p_1,5-p_2)\) and \((4-p_1,7-2p_2)\). At \((1/2,8/5)\) the two buyers strictly demand the diagonal matching. At \((2,11/4)\) they strictly demand the swap. Take \(h\) copies and give each buyer a cross-block offer \(1-p_j\) on every other good. All cross-block offers are strictly worse at the two price choices in each block. Their combinations give \(2^h\) clearing vectors with distinct uniquely supported matchings. The minimum is \((0,1)\) in each block by the original strict Hall check, and cross-block offers are strictly worse there too. An endpoint list can target that one matching. [Minimum-price test](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

On this family the selector keeping the slope-one edges first returns the swap. Its least supporting prices are \((1,2)\) per block. In the resulting box every buyer prefers any local real option to any cross-block option, and maximizing assignments stay within the blocks. The diagonal has total value \(2-p_2\) above the swap in each block. The common-optimizer test therefore returns a minimum-supported diagonal on the full box.

The degree-three reduction bounds the number of heterogeneous offers incident to one vertex. It does not bound the product of list sizes over all vertices or the rank of the cycle gains. A useful next result would find a polynomial sublist of compatible normalizations from the capacities and intercepts, or bound the changing deletion-matching products without a rank assumption. Every such proposed sublist can be checked with the original support LP. [Degree-three normal form](A4j-unit-degree-three.md)

The exact replay checks 7,487 multiplier choices from 360 small unit markets and compares the box certificate to exhaustive assignments and price corners on 80 boxes. It checks 80 multiplier-product cuts against exhaustive residual covers. [Replay](../experiments/a4j_endpoint_support_replay.py)
