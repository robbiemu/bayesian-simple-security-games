# A4h Complete candidates at the supplied capacity

At an input capacity \(x_0\), Hall cuts can be tested directly against \(x_0\). Reusing a cut chosen at an earlier price can discard the only current witness. Two rules give complete polynomial candidate sets under structural hypotheses. The first clips branch loads to the range where the actual capacity can distinguish them. The second queries only selected prices and handles branch tables with exponentially many relevant rows. [Counting the full table](A4h-table-count-hardness.md) · [A4g Hall finisher](A4g-budgeted-support-search.md#searching-a-product-of-lists-without-enumerating-it)

## Which representatives can be reused

For a common nonnegative toll and nonnegative base lengths, an optimal route can be chosen simple. A layered shortest-path calculation gives a best base length for each toll count up to \(|V|-1\), which covers every value of the common toll. The scalar penalty agrees for all routes within one count. With edge-specific affine tolls, the lower envelope can have superpolynomially many pieces, even on planar graphs. [Gajjar and Radhakrishnan, Parametric Shortest Paths in Planar Graphs](https://arxiv.org/abs/1811.05115)

A hard budget imposes a different test. Consider three parallel routes with pairs (resource, base length) \((0,4),(1,3),(2,0)\). At budget 1 the unique feasible optimum is the middle route. To win at a scalar resource price \(\lambda\) it would require both \(3+\lambda\le4\) and \(3+\lambda\le2\lambda\), which is impossible. A reduction from the hard-budget problem must preserve this kind of budget optimum. An envelope of scalar-optimal routes alone loses it. [Hassin, Approximation Schemes for the Restricted Shortest Path Problem](https://www.math.tau.ac.il/~hassin/restrictedPath.pdf)

### One Hall cut per size and capacity can fail

Take three goods \(h,a,b\), all of capacity one, including the supplied \(x_0=1\) for \(h\). Buyer A has mass four and bids 1 for each of \(h,a\). Buyer B has mass three and bids 3 for each of \(h,b\). Use unit slopes, outside and reserve zero, and zero on other bids. At a trial \(p_h=t\), the conditional least prices on \(a,b\) are \(\min(t,1),\min(t,3)\), because each leaf buyer must be able to take her boundary or outside offer.

Define \(\Delta_t(S)=f_t(S)-c(S)\), where \(f_t(S)\) counts buyers whose entire demand is trapped in \(S\) at those conditional prices. A rule that keeps the most violated cut in each class \((|S|,c(S))\) at the first trial keeps \(\{h,a\}\) in the size-two class. The actual capacities are the same at both trials.

| Goods \(S\) | \(\Delta_0(S)\) | \(\Delta_1(S)\) |
| --- | ---: | ---: |
| Any singleton | −1 | −1 |
| \(\{a,b\}\) | −2 | −2 |
| \(\{h,a\}\) | 2 | −2 |
| \(\{h,b\}\) | 1 | 1 |
| \(\{h,a,b\}\) | 4 | 0 |

At \(t=1\), A can take outside and B still demands exactly \(h,b\). Every saved cut passes. The omitted \(\{h,b\}\) is the unique violated cut, and the conditional load on \(h\) is 2. Both buyers' masses exceed the combined capacities of their two goods, so neither can strictly prefer real goods to outside at any buyer-feasible price. This forces the least vector \((p_h,p_a,p_b)=(3,1,3)\), where a clearing flow exists. The representative rule is safe on a fixed demand graph, and on any domain where each group has one representative that dominates its other cuts throughout. At a new demand graph, a fresh Hall flow finds a current witness in polynomial bit time. [A4b conditional test](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)

## Clip branch loads to the range that can affect capacity

Use the goods-interaction block decomposition from A4h. Choose a quantity quantum \(q\) such that all input margins, including \(x_0\), are multiples of \(q\), for instance the reciprocal of the product of their denominators. For an articulation \(h\), write \(U_h\) for the total original mass of buyers with a viable offer on \(h\). For a child branch \(B\) there, let \(U_B\) be its share of that mass and \(L_B(t)\) its true minimum boundary load. These upper bounds add across the child branches and the local buyers. Put \(D_h=(U_h-c_h)_+\). Retain only

\[
 \widehat L_B(t)=\max\{(U_B-D_h)_+,\ \min\{L_B(t),c_h+q\}\}.
\]

This is valid for every price at which the capacity on \(h\) is the actual \(c_h\). If a load is clipped upward, it is then \(U_B-D_h\), and even with every other contributor at its upper bound the total is at most \(c_h\). The original total passes as well. All clipped loads stay within their individual upper bounds. If no upward clip fires, every downward clip represents an individual overload and still exceeds \(c_h\). In all other cases the loads are unchanged. Hence both totals have the same feasibility at \(h\) for every choice of local allocation. This preserves the projection onto the block, including the feasible choices of how much local mass goes to the outgoing boundary. The genuine descendant flows can be restored from the original messages at the selected prices.

If the reserve load exceeds \(c_h\), one local solve at capacity \(c_h+q/2\) jumps directly to the first passing price. Replace the whole earlier prefix by its overload sentinel. Continue the A4h sweep only down to the floor \((U_B-D_h)_+\), then keep the floor. If the reserve load is already at or below the floor, it suffices to keep the floor everywhere. A positive floor is represented by a unary buyer with an offer above the original price ceiling throughout the local search box. All interior articulation capacities stay at their supplied values while the outgoing boundary capacity is varied in a sweep. Thus previously clipped messages can be used in each local solve.

Each message has at most \(2+\min(c_h,D_h,U_B)/q\) retained levels. With boundedly many goods per block, this proves polynomial bit time whenever \(\min(c_h,(U_h-c_h)_+)/q\) is polynomial at every articulation, including any such \(h\) at \(c_h=x_0\). Buyer counts per block, depth, branching and the slopes can be arbitrary. A large binary capacity can qualify when it is within polynomially many quantity units of the total incident mass. When a branch owns all the incident mass, a single feasible/infeasible breakpoint suffices for any \(c_h\).

The bounded-dimension arrangement method uses one local solve per retained drop, plus an initial solve and one conditional load flow per retained price. Each local solve tests polynomially many rational arrangement vertices by flow. Breakpoints are coordinates of genuine branch minimum prices at rational trial capacities, or fixed input bounds, so the original tight-path argument bounds their bit length. The quantities are multiples of \(q\) of polynomial bit length. After the root solve, fix each attachment at its recovered price and descend through least conditional prices. The preserved projection gives the original least vector. One original clearing flow completes the solution. [Block sweep and bit bounds](A4h-complete-candidate-generation.md#generate-the-breakpoints-adaptively)

The level bound can still be large. Put an A4h counting branch of incident mass \(T\) at \(h\), give another group of incident buyers mass \(T\), and take \(c_h=T\). The counting branch's clip has floor zero and leaves every level of its original table. An explicit table can remain exponential even with this supplied capacity.

## Query branch loads at selected prices

**Theorem.** Suppose the buyers and goods split into a core and branches. Core buyers have viable offers only on core goods, and each branch shares just one good with the core. Branch buyers and internal goods are disjoint between branches. The core slopes factor as \(d_{ij}=\alpha_i\beta_j\) with positive factors. Assume that fixing the shared price in any branch and folding its offers into the outside option leaves a polynomial-bit-time minimum-price problem on that branch's internal goods. Then a polynomial-size list of full price vectors containing the original minimum can be generated in polynomial bit time for the supplied capacities. Branch slopes can be heterogeneous and their full boundary tables can be exponential.

For example, it suffices that the internal slopes in each branch factor after deleting its shared good. The boundary slopes of those buyers are arbitrary. There can also be an arbitrarily large unit-slope counting branch, and an unrelated branch with an unbalanced slope cycle, on a dense factorized core. The decomposition can be supplied with the input. [Conditional market test](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)

### A convex potential with implicit unary buyers

Normalize reserves and outsides to zero. Use core coordinates \(z_j=\beta_j p_j\) and divide each core buyer's net values by \(\alpha_i\), so that her bids at trial \(z\) are \(b_{ij}-z_j\). The factors can be found by the A4a normalization LP. For branch \(B\) at good \(j\), use \(L_B(z_j/\beta_j)\) as its minimum load. Compute that number at a rational trial price by one conditional branch solve followed by one min-load flow. These branch queries use the original internal capacities.

Each branch drop of size \(\Delta\) at price \(\nu\) in normalized coordinates can conceptually be represented by a unit-slope unary buyer of mass \(\Delta\) and intercept \(\nu\). The augmented core has precisely the projection of the original buyer-feasible price vectors by the one-boundary flow swap. Its least price \(z^*\) is therefore the projection of the original minimum. The potential whose minimizers are its clearing prices is the assignment dual with utilities eliminated:

\[
 F(z)=c\cdot z+\sum_{\text{core }i}m_i\max(0,\max_j(b_{ij}-z_j))
       +\sum_{\text{branch drops }(j,\nu,\Delta)}\Delta(\nu-z_j)_+ .
\]

The algorithm needs a subgradient of \(F\) at a trial \(z\). Use the vector \(c\), subtract each core buyer's mass on any one of her best goods, and subtract each branch's queried load on its attachment. Allocate no core mass for a buyer when the chosen best option is outside. The branch contribution gives the right derivative, including at a breakpoint where the tying unary buyer can take outside. The actual \(x_0\) enters directly in \(c\) if the specified good is in the core, and in the conditional solve if it is inside a branch. The algorithm never sums the exponential list of unary terms.

### Exact candidate recovery and call count

Let \(k\) be the number of core goods and let \(R\ge1\) bound all least core prices, using the original offer ceilings in normalized coordinates. Let \(\delta=q/(4k)\), \(\mu=q/(4kR)\), and set \(G(z)=F(z)+\delta\sum_jz_j+\mu\|z\|_2^2/2\) on \([0,R]^k\).

At \(z^*\), increasing each augmented core capacity by \(\delta+\mu z_j^*\) leaves \(z^*\) the least clearing vector and makes it the unique clearing price vector for the increased capacities. Indeed every synthetic mass is a difference of original load levels and hence a multiple of \(q\). The A4c fixed-price Hall proof applies to arbitrary positive increases whose sum is below \(q\), which holds here. Equivalently \(z^*\) minimizes \(F(z)+(\delta\mathbf1+\mu z^*)\cdot z\). Subtracting that inequality from the difference of the quadratic potentials gives

\[
 G(z)-G(z^*)\ \ge\ (\mu/2)\|z-z^*\|_2^2 .
\]

Use central cuts at rational ellipsoid centers. A center outside the price box gives a coordinate cut through the center that preserves the box. A center \(z\) inside gives the cut \(g(z)\cdot(y-z)\le0\) for the subgradient just described plus \(\delta\mathbf1+\mu z\). A zero subgradient identifies \(z^*\). A computed rational bound \(M\ge1\) on \(\|g(z)\|_2\) throughout the box can use total core capacity, total original buyer mass and \(k(\delta+\mu R)\).

Take a computable denominator bound \(Q\) for \(z^*\) from the original tight anchor paths and the rational normalization factors. It has polynomial bit length and never uses the number of synthetic offers. Set \(\tau=1/(4Q^2)\). If no inside center is within \(\tau\) of \(z^*\), every subgradient cut preserves the ball of radius \(r=\min\{R/2,\mu\tau^2/(4M)\}\) about \(z^*\), intersected with the box. In fact \(g(z)\cdot(z-z^*)\ge\mu\tau^2/2\) at every such center. The intersection contains an orthant of that ball oriented into the box and so has at least a \(2^{-k}\) share of its volume. The rounded rational ellipsoid method then forces an inside center within \(\tau\) in \(O(k^2\log(2kR/r))\) cuts, starting from a ball of radius \(kR\). Both the iteration count and the rational center bit lengths are polynomial in the binary input length. In one dimension interval bisection gives the same guarantee. [Grötschel, Lovász and Schrijver, Geometric Algorithms and Combinatorial Optimization, Chapter 3](https://www.zib.de/userpage/groetschel/pubnew/paper/groetschellovaszschrijver1988.pdf)

At each inside center, use continued fractions to reconstruct each coordinate with denominator at most \(Q\) within \(\tau\), when possible. Such a rational is unique, and the center near \(z^*\) reconstructs it exactly. Extend every reconstructed core candidate by the original conditional minimum of each branch at its attachment price. This extension is the original least vector when the core candidate is \(z^*\), by the one-boundary projection and the fact that replacing a conditional completion by its least one can only lower prices and weakly reduce the attachment's required flow. Check each extended vector by one original rational clearing flow and the A4 minimum-price certificate. Alternatively collect its coordinates and use the A4g list finisher. This produces an exact equilibrium at the original capacities, including all price ties.

For \(b\) branches and \(N=O(k^2\log(2kR/r))\) cuts, at most \(O(bN)\) conditional solves, \(O(bN)\) min-load flows and \(O(N)\) original clearance tests suffice. All their trial prices, capacities, and offer coefficients have polynomial bit length. With factorized residual branches there are two polynomial-size rational assignment LPs per conditional solve for value and least prices. The list has at most \(N\) full candidates. [Original minimum-price certificate](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

### Near-factorized cores

The same composition works if the normalized core slopes have error at most \(1/(4k)\) from one. Freeze the core intercepts at a trial vector as in A4a, and solve that implicit unit-slope core by the preceding theorem. The branch messages and conceptual unary intercepts stay fixed during this iteration. A4a's bound makes the map of frozen least prices contract by a factor at most \(1/2\), including after clipping to the price box. At the original least price, the frozen demands and the minimum-price certificate agree with the original augmented core, so it is a fixed point. Dyadically rounded iteration needs \(O(\log(R/\tau))\) exact frozen solves for the same reconstruction tolerance from the original tight paths. Extend the exact core prices through the branches and clear by one original flow. [A4a stability and exact recovery](A4a-near-factorized-slopes.md#stability-of-least-tu-prices)

### The full A4a column bound

The composition also extends to rational normalized column errors \(e_j\) with \(2\sum_j e_j/(1+e_j)\le1\). Put \(J=\{j:e_j>0\}\), let \(d=|J|\), and let \(f\) be the projection of the frozen least-price map onto \(J\). It depends only on trials in those coordinates. The case \(J=\varnothing\) is the factorized solver. A4a's sensitivity proof applies with the same conceptual unary buyers in every frozen market, so \(f\) is nonexpansive in the Euclidean norm weighted by \(\operatorname{diag}(e_j:j\in J)\). Enlarge \(R\) as in A4a to bound all frozen core prices as well as all branch thresholds on the core. This maps the box into itself. A fixed point of \(f\) restores a full fixed point by one frozen solve. The original minimum-price certificate makes this fixed point unique. [A4a weighted nonexpansive region](A4a-near-factorized-slopes.md#a-wider-region-by-a-weighted-euclidean-norm)

For exact recovery, the frozen price map has a useful precision bound from the **explicit** market. At any trial, choose a tight anchor path for each price of the full frozen market, including the branch prices. Every frozen intercept is affine in the trial and the slopes are constant. Hence the paths give affine price formulas with polynomial-bit coefficients. The region where these formulas give the same demand comparisons and reserve statuses is specified by the original comparisons and reserve constraints. On its closure, ties may be added and positive prices may reach reserve. The old clearing flow and strict minimum-price certificate still apply. Thus \(f\) is affine on these closed cells, with uniformly polynomial-bit coefficients in the affine rules and cell inequalities.

In one such cell, add a variable \(0\le v\le R\) and impose \(|t-f(t)|\le v\) coordinatewise. Each vertex with \(v>0\) has \(v\ge1/H\) for a uniform determinant bound \(H\) of polynomial bit length. Each vertex with \(v=0\) has \(t=z_J^*\). Expressing \((t,\|t-f(t)\|_\infty)\) as a convex combination of vertices bounds the combined weight on the positive-\(v\) vertices by \(H\|t-f(t)\|_\infty\). All their trial coordinates lie in the box, giving

\[
 \|t-z_J^*\|_\infty\le RH\|t-f(t)\|_\infty.
\]

With \(W=\operatorname{diag}(e_j:j\in J)\), nonexpansiveness gives \((Wg)\cdot(t-z_J^*)\ge \|g\|_W^2/2\) for \(g=t-f(t)\). A trial outside distance \(\tau\) from the fixed point has \(\|g\|_\infty\ge\eta=\tau/(dRH)\). Its central cut preserves the ball of radius \(\min(R/2,\eta\min_{j\in J}e_j/(4d\max_{j\in J}e_j))\) about the fixed point, intersected with the box. The same rational ellipsoid volume argument forces a center near enough for reconstruction in polynomially many frozen solves. Extend each reconstructed trial by one frozen solve, and check the resulting full original candidate by flow. All calls have polynomial bit length. In particular, one core good can have arbitrary slope ratios when the other core slopes factor.

For an unrestricted core, differentiating a maximum of the original offers charges each demanded good by the buyer-specific slope times its demand. The needed Hall charge is unweighted. The potential argument therefore requires structure such as the factorized or nearly factorized core. A general polynomial-time generator of complete lists at \(x_0\) remains open. [A4e covering mismatch](A4e-covering-lp.md)

Three further tests address supplying the next price, contracting certified ties, and comparing partial solutions with shared quotes. [Alternating price jumps](A4h-alternating-tree.md) · [Forced price relations](A4h-forced-price-relations.md) · [Boundary dominance](A4h-boundary-dominance.md)
