# A4e Covering linear programs for market equilibrium

The covering inequalities describe the permissible utility and price pairs. Market equilibrium also requires an unweighted transportation flow supported by the tight inequalities. A fixed covering objective can select a point with no such flow, and a failed flow test need not give a linear cut. A particular reweighting rule always reaches a clearing point with polynomial work per iteration and an exponential bound on iterations. Covering LPs give polynomial-time algorithms for nearly factorized slopes and for arbitrary slopes with common intercept offsets. The tight worst-case iteration count for this descent rule remains open.

## The weighted dual can miss clearance

Let \(C\) be the polyhedron \(u,p\ge0,\ u_i+d_{ij}p_j\ge b_{ij}\), and let \(\ell_{ij}=u_i+d_{ij}p_j-b_{ij}\). A point of \(C\) clears if it has a nonnegative allocation \(x\) with \(\sum_j x_{ij}\le m_i\) and \(\sum_i x_{ij}\le c_j\), satisfying

\[
 x_{ij}\ell_{ij}=0,\qquad
 u_i\left(m_i-\sum_j x_{ij}\right)=0,\qquad
 p_j\left(c_j-\sum_i x_{ij}\right)=0.
\]

The dual of the cover with objective weights \(w_i,v_j\) maximizes \(\sum_{ij} b_{ij}y_{ij}\) with \(\sum_j y_{ij}\le w_i\) and \(\sum_i d_{ij}y_{ij}\le v_j\). Its complementary slackness concerns these weighted capacities. With one buyer and one good, take \(m=1,\ c=2,\ d=3,\ b=3\). The cover with weights \(m,c\) has the unique optimum \((u,p)=(0,1)\). A positive price requires two units of sales, and the market has only one unit of mass. The market clears at \(p=0\). After the supply perturbation the capacity is \(5/2\), and the covering optimum is still \((0,1)\). [Supply perturbation](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

Weights chosen from slopes, masses and capacities alone cannot fix this uniformly, even when every intercept is positive. Take three unit-mass buyers, three goods of capacity \(3/2\), and slopes \(d_{ii}=3,\ d_{ij}=1\) for \(i\ne j\). For each good \(j\), compare two intercept matrices with all unlisted entries \(1/4\).

- Set \(b_{jj}=3\). Any clearing price has \(p_j\le1/4\), since above \(1/4\) only buyer \(j\) can demand it. Buyer \(j\) strictly prefers \(j\) and has positive utility, so a cover optimum at a clearing pair needs \(v_j\ge3w_j\).
- Set \(b_{ij}=1\) for \(i\ne j\) in column \(j\). At prices \(p_j<3/4\) both other buyers strictly prefer \(j\), exceeding capacity. Thus \(p_j\ge3/4\) and the \(jj\) constraint is slack. A cover optimum at a clearing pair needs \(v_j\le\sum_{i\ne j}w_i\).

These inequalities for all \(j\) imply \(3\sum_i w_i\le2\sum_i w_i\), impossible with positive weights. The argument allows the weights to know the full graph of positive intercepts, which is the same in all six instances.

## Reweighting with an allocation

For any unweighted-feasible \(x\), set \(v_j(x)=c_j-\sum_i x_{ij}+\sum_i d_{ij}x_{ij}\) and keep buyer weights \(m_i\). The difference between the cover objective and the allocation's value is

\[
\begin{aligned}
G(x,u,p)
 &= m\cdot u+v(x)\cdot p-\sum_{ij}b_{ij}x_{ij}\\
 &=\sum_{ij}x_{ij}\ell_{ij}
  +\sum_i \left(m_i-\sum_j x_{ij}\right)u_i
  +\sum_j \left(c_j-\sum_i x_{ij}\right)p_j .
\end{aligned}
\]

Each term is nonnegative. The minimum over the cover is zero exactly when \(x\) has supporting equilibrium prices. In that case every optimum supports that same allocation. Thus good objective weights exist, and the formula uses the allocation that the procedure is trying to find. Minimizing over \(x\) as well leaves a bilinear objective. Minimizing first over the cover gives a concave function of \(x\), since it is a pointwise infimum of affine functions.

Alternating exact LP minimization of \(G\) can stop with positive gap. Take two unit-mass buyers, capacities \((3/2,3/2)\), and

\[
d=\begin{pmatrix}1&2\\2&1\end{pmatrix},\qquad
b=\begin{pmatrix}2&3\\3&2\end{pmatrix}.
\]

At \(p=u=(1,1)\) all four edges are tight. The frozen assignment bids \(b_{ij}-(d_{ij}-1)p_j\) are all 2. Lexicographically maximizing the row-major allocation among optimal flows gives \(x_{11}=1,\ x_{12}=0,\ x_{21}=x_{22}=1/2\). Its weights are \(v(x)=(2,3/2)\). The reweighted dual has a feasible flow with rows \((1/3,2/3)\) and \((5/6,1/6)\), using both weighted capacities exactly. All four dual entries are positive, so every covering optimum satisfies all four edge equalities. The equalities uniquely give the same \(p,u\). The ordinary good totals of \(x\) are \(3/2,1/2\), yielding gap 1 and a failed clearance test. The original objective with weights \(m,c\) also starts at this unique cover point, as certified by the weighted dual with all entries \(1/2\).

### An exact descent rule

At a cover point \((u,p)\), solve the unweighted assignment LP with bids \(b_{ij}-(d_{ij}-1)p_j\). Let \((\tilde u,q)\) be an optimal nonnegative dual of this assignment. Among the optimal allocations choose \(x\) that maximizes

\[
 \sum_{ij}-\operatorname{sgn}(q_j-p_j)\log(d_{ij})\,x_{ij}.
\]

If the gap is zero, \(x\) clears. Otherwise minimize the cover with weights \(m_i,v_j(x)\) and take a new cover vertex. The secondary objective guarantees strict decrease in \(\min_x G(x,u,p)\) at each nonterminal iteration.

To prove strictness, suppose instead that the old point already minimizes the reweighted cover. Take an optimal dual \(y\) of this cover. Include dummy arcs \(i\to0\) for unused buyer mass and \(0\to j\) for unused good capacity, all with slope 1. Use the ordinary row and column slacks for \(x\), and the row and weighted column slacks for \(y\). Their difference \(f=x-y\) has zero sum at every buyer and zero slope-weighted sum at every good. Orient positive \(f\) forward and negative \(f\) backward. A forward buyer–good arc carries \(|f|\) at its tail and \(d_{ij}|f|\) at its head. A backward arc carries \(d_{ij}|f|\) at its tail and \(|f|\) at its head. The ratio of head to tail is the arc's gain. Every real node balances its incoming and outgoing amounts.

Put \(V_i=u_i-\tilde u_i\) at buyers, \(V_j=q_j-p_j\) at goods and \(V_0=0\). Along every oriented arc \(V\) is nonincreasing. On a real arc with \(f>0\), frozen optimality gives \(\ell_{ij}=V_i-V_j\ge0\). On a real arc with \(f<0\), true tightness and frozen dual feasibility give \(V_i-V_j\le0\). The dummy arcs obey the same comparison by complementary slackness for outside and reserve. A positive term in \(G\) uses an arc of \(x\) missing from \(y\), including a dummy arc if appropriate. Its oriented arc has a strict drop in \(V\).

If a strict drop begins at positive \(V\), choose a positive threshold between its endpoint values and consider the nodes above it. This set excludes 0, has an exit and has no entrance. It contains a directed cycle of gain product greater than one. Otherwise let \(\pi_v\) be the maximum gain product of an internal walk starting at \(v\), including the empty walk. With every cycle's gain at most one this maximum is finite, and \(\pi_v\ge\gamma_{vw}\pi_w\) on each internal arc of gain \(\gamma_{vw}\). Multiplying the node balances by \(\pi_v\) and summing makes the weighted internal deliveries at most the weighted internal departures, so the strictly positive exit is impossible. If the strict drop begins at nonpositive \(V\), take a strictly negative threshold between the endpoints and the nodes below it. There is an entrance and no exit. Reversing the flow with reciprocal gains gives the same argument and yields an original directed cycle of gain product less than one.

Along either cycle \(V\) is constant with a nonzero sign. Move a small ordinary amount around the cycle against the orientation of \(f\), decreasing \(x\) on the forward arcs and increasing it on the backward arcs. Every adjusted edge is frozen-tight. For the increased edges this follows from \(V_i=V_j\) and true tightness. The move preserves unweighted row and column totals and frozen optimality. If the cycle gain product is \(\Gamma\), the secondary improvement per unit is \(\operatorname{sgn}(V)\log\Gamma>0\), contradicting the choice of \(x\). Thus the reweighted cover must improve the gap at the old allocation, which also improves the next minimized gap.

The secondary LP can use rational log approximations. A simple cycle uses at most \(k+n\) slopes or reciprocals, so a nonunit gain product is a rational of polynomial bit length with log separated from zero by \(2^{-\operatorname{poly}(L)}\) for input length \(L\). Round each coefficient sufficiently to preserve the sign of every strict simple-cycle improvement. Start at the cover vertex \(p=0,\ u_i=\max(0,\max_j b_{ij})\), and return a vertex at every reoptimization. All cover vertices have uniform polynomial bit bounds because their defining inequalities are fixed. Each iteration uses a frozen LP and its dual, one secondary transportation LP, and one reweighted cover LP. Strict decrease prevents revisits, so the number of iterations is bounded by the number of cover vertices, at most \(\binom{kn+k+n}{k+n}\).

One can also count in price space or utility space. At a vertex every \(u_i\) is a maximum of its offers and zero, since otherwise that coordinate can vary in both directions. Eliminating one active \(u_i\) equality per row leaves \(n\) independent price floors or within-row offer comparisons, including comparisons to outside. There are at most \(n+k\binom{n+1}{2}\) such hyperplanes. Eliminating prices instead leaves \(k\) independent comparisons of the bounds \((b_{ij}-u_i)/d_{ij}\) and zero in each column, or utility floors. There are at most \(k+n\binom{k+1}{2}\) such hyperplanes. The smaller count gives \(2^{O(\min(k,n)\log(kn+1))}\) iterations. This is finite exact recovery with polynomial-bit calls. A defect-one family forces superpolynomially many solves for this exact rule, even with near-factorized slopes. The scalar projection gives both extremal solve counts on that family. [Reweighted-cover lower bound](A4h6-reweighted-cover-lower-bound.md)

## Failed Hall tests and linear cuts

At a cover point, the outside option is available precisely when \(u_i=0\), and a real good is available precisely when its inequality is tight. Test a circulation with all row masses assigned, including outside, and all above-reserve capacities filled. An upper Hall violation is a set \(S\) of goods whose capacity is below the mass of the buyers restricted to \(S\). A lower Hall violation is a set \(S\) of positive-price goods whose capacity exceeds the mass of the buyers touching \(S\). These cut families follow from the circulation with lower bounds. [Fixed-price Hall conditions](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

The violated numerical inequality depends on the current tight edges. For example, take unit buyer masses, capacities \((1,2)\), and

\[
b=\begin{pmatrix}6&6\\6&8\\0&8\end{pmatrix},\qquad
d=\begin{pmatrix}1/2&1\\1/2&2\\1&2\end{pmatrix}.
\]

Prices \((2,3/2)\) clear with buyers assigned to \((1,2,2)\) and utilities \((5,5,5)\). Prices \((6,3)\) clear with assignment \((2,1,2)\) and utilities \((3,3,2)\). At their midpoint, \(p=(4,9/4),\ u=(4,4,7/2)\), the first two buyers both strictly demand good 1, and the third buyer alone demands good 2. The midpoint fails both Hall conditions. All three points minimize the original cover objective at value \(20\). The objective lower bound comes from summing the covering rows for \(11,21,32\), and all three points attain it.

Any linear cut preserving the two clearing points also preserves their midpoint. This applies to prices alone and to the full utility and price vectors. An LP with auxiliary continuous variables and affine projection therefore cannot represent the entire clearing set exactly. A formulation selecting one equilibrium can have a smaller projection.

A failed cut yields a disjunction of equalities. In an upper violation some currently restricted buyer must acquire the outside option or a tight edge outside \(S\). In a lower violation some good in \(S\) must reach reserve or a buyer outside the old neighbor set must acquire a tight edge into \(S\). Each alternative sets a currently positive cover slack to zero. One exact algorithm branches on these alternatives, solving one feasibility LP and one circulation at each node. Every clearing point survives in some child. Each nonempty child is a proper face because its new equality fails at the trial point. With \(k\) types and \(n\) goods, the depth is at most \(k+n\) and the width at most \(kn+k+n\). This proves finite exact recovery with polynomial-bit calls and a generally exponential call bound.

Some failed points do admit a global linear cut. At a failed vertex of a current LP relaxation that preserves every clearing point, take the sum of its active slacks after integer row clearing. Its zero set in the relaxation consists of that vertex alone. For a fixed clearing allocation, its supporting pairs form a face of the original cover, given by setting the complementary slacks to zero. On each such face the active-slack sum has a positive minimum attained at an original cover vertex. If \(D_C\) bounds the common denominator of any original cover vertex by Cramer's rule, the sum is at least \(1/D_C\) on every clearing face. The corresponding cut excludes the failed vertex. Further LP solves can generate new vertices, and this argument supplies no polynomial bound on the number or encoding length of the cuts. [Direct Hall search](A4b-direct-hall-search.md)

## Factorized slopes and repeated covering solves

Discard \(b_{ij}\le0\) from the graph. These cover inequalities are redundant. They can carry market flow only at ties with outside and with the good at reserve, where that flow can take outside instead. Suppose the slopes on the remaining edges factor as \(d_{ij}=\alpha_i\beta_j\) with positive row and good factors. Use the cover weights \(w_i=m_i/\alpha_i\) and \(v_j=c_j\beta_j\). On setting \(y_{ij}=x_{ij}/\alpha_i\) its dual constraints become exactly the unweighted capacities, after division by \(\beta_j\) at each good. Complementary slackness gives clearance. One covering LP and one unweighted flow suffice. Minimizing the sum of prices on the optimal face returns the componentwise minimum.

This condition is necessary for a diagonal normalization to identify the two capacity systems on all arc loads. A row constraint requires a common scaling on every incident flow variable, and the normalized good constraint requires \(d_{ij}/\alpha_i=\beta_j\) on every edge. Factorization is equivalent to equality of the products of alternate slopes on each cycle of the remaining graph. Propagating ratios along a spanning forest and checking the other edges recognizes it with rational arithmetic in polynomial bit time. It holds automatically on a bipartite forest. The more general linearly transferable matching setting also distinguishes this rescaling from exchangeability for particular outcomes. [Galichon and Jacquet, §4](https://arxiv.org/html/2402.12200v2#S4)

Suppose instead that after the normalization \(z_j=\beta_jp_j\) and division of row utilities by \(\alpha_i\), the slopes are \(s_{ij}=1+\eta_{ij}\) with \(|\eta_{ij}|\le e_j\). At a trial \(t\), solve an ordinary unit-slope cover with intercepts \(b_{ij}/\alpha_i-\eta_{ij}t_j\). Let \(F(t)\) be its least prices. At a fixed point the demand graphs agree, so its unweighted flow clears the original market. The strict minimum-price Hall test depends only on that graph and the reserve coordinates, and transfers to the original market.

The price-sensitivity bound for an intercept change of at most \(\delta_j\) in column \(j\) is \(\delta_j+2\sum_{h\ne j}\delta_h\) for price \(j\). Its alternating-path proof compares two allowed edges for the same buyer, so it also applies to a fixed sparse offer graph. In particular, the frozen map is a contraction with factor at most \(1/2\) under the uniform bound \(e_j\le1/(4n)\). A weighted Euclidean norm and central cuts also work under the wider condition

\[
2\sum_j \frac{e_j}{1+e_j}\le1 .
\]

This includes the uniform bound \(1/(2n-1)\) and a single good with arbitrary slopes when the others factor exactly. Each map evaluation takes a covering LP and a linear minimization on its optimal face. Write \(E=\max_j e_j\), and let \(\Delta\) bound the denominator of a vertex of the repair LP after integer row clearing. The repair preserves every frozen demand tie and fixes each frozen reserve coordinate at zero, allowing one common utility violation \(v\ge0\) to relax the demand inequalities. At residual \(\|F(t)-t\|_\infty\le\tau=1/(4(1+E)\Delta)\) on the columns with nonzero errors, the frozen prices witness \(v\le2E\tau<1/\Delta\). A positive minimizing \(v\) would be at least \(1/\Delta\). Thus the optimum is zero and the stored flow and strict Hall certificate both transfer.

With the factor-\(1/2\) contraction, dyadic rounding to mesh at most \(\tau/4\) needs \(O(1+\log R+\log(1/\tau))\) map evaluations for a known rational price bound \(R\ge1\). For the wider condition, the central cuts preserve a ball of radius \((\tau/2)\min_{e_j>0}e_j/\max_{e_j>0}e_j\) around a fixed point in the active coordinates until a residual passes. The ratio of the initial to retained radii has polynomial logarithm, so the ellipsoid method uses polynomially many evaluations. The factors for prescribed \(e_j\) are found by rational linear feasibility. Trial and LP data have polynomial bit length, and exact recovery uses one additional LP and a clearing flow. [Sensitivity, precision and exact repair](A4a-near-factorized-slopes.md)

Swapping buyers and goods gives another use of these solvers. In the reciprocal transpose the masses are \(c_j\), capacities are \(m_i\), intercepts are \(b_{ij}/d_{ij}\), and slopes are \(1/d_{ij}\). The inequality is \(p_j+(1/d_{ij})u_i\ge b_{ij}/d_{ij}\). Transposing the flow gives the same complementary conditions. Apply the supply perturbation to the original capacities before swapping. Any transposed solution then recovers the original minimum, regardless of which extremal solution the transposed solver selects. [Supply perturbation](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

## Common offsets with arbitrary slopes

Suppose the remaining edges admit \(b_{ij}=A_i+d_{ij}C_j\). Rational linear algebra tests the equations and produces polynomial-bit offsets when they are feasible. The slopes can be arbitrary positive rationals. The offsets let a single increasing transformation bring all slopes close to one, regardless of which offers lie above or below the offsets. Perturb the capacities first, so every good has positive capacity. [Common offsets in the game](A3-mixed-offsets.md) · [Supply perturbation](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

Write \(t_j=p_j-C_j\) and \(w_i=u_i-A_i\). The cover inequalities become \(w_i\ge-d_{ij}t_j\), with outside lower bound \(w_i\ge-A_i\) and reserve \(t_j\ge-C_j\). For a positive integer \(K\), put \(H(a)=\operatorname{sgn}(a)|a|^{1/K}\). Since \(H(-d_{ij}t_j)=-d_{ij}^{1/K}H(t_j)\), the transformed cover has intercept zero, slopes \(D_{ij}=d_{ij}^{1/K}\), outside offers \(O_i=H(-A_i)\) and reserves \(R_j=H(-C_j)\). The flow is unchanged. Tight edges and nodes at outside or reserve correspond exactly because \(H\) is strictly increasing.

Choose \(L\ge2\) such that all \(d_{ij},1/d_{ij},|A_i|,|C_j|\) are at most \(2^L\), and take \(K=32nL\). Then \(|D_{ij}-1|\le1/(16n)\) and \(|O_i|,|R_j|\le 2\). Approximate these transformed coefficients by rationals within \(\xi\le1/(32n)\) using bisection and comparisons of rational \(K\)-th powers. The approximate slopes satisfy the uniform \(1/(4n)\) condition, so the contraction algorithm computes its exact least price vector \(\widehat P\) and a clearing allocation \(x\). Take \(\widehat W_i\) to be the exact row maxima including the rounded outsides. Every price strictly above its rounded reserve is paid on a demanded edge, by positivity of the perturbed capacities. This bounds \(\widehat P_j\) between \(-3\) and \(6\), and \(|\widehat W_i|\le 9\).

To choose precision, form the original support LP template in \(u,p\) and a common violation \(v\in[0,1]\). Bound each utility and price in absolute value by \(1+2^L+16^K\). Relax original nonnegativity and covering by \(v\), impose each positive-flow edge equality within \(v\), and impose \(u_i=0\) for rows with outside mass and \(p_j=0\) for undersold goods, also within \(v\). The possible rows come from the original data and the displayed box. If \(N=k+n+1\) and \(B\) bounds the integer entries after clearing these rows, take \(Q=N!B^N\). Any positive optimum of this compact LP is at least \(1/Q\), independently of the chosen support.

Let \(g(a)=\operatorname{sgn}(a)|a|^K\), the inverse of \(H\), with Lipschitz constant \(\Lambda=K16^{K-1}\) on \([-16,16]\). Invert the approximate solution as \(p'_j=C_j+g(\widehat P_j)\) and \(u'_i=A_i+g(\widehat W_i)\). The transformed inequalities and supported equalities differ from the exact transformed ones by at most \(6\xi\), since the slopes were rounded within \(\xi\). Floor and outside errors are at most \(\xi\), including equality at a slack-capacity good or outside-using row. Applying \(g\) converts all these residual bounds to at most \(6\Lambda\xi\) in the original units. In particular \(g(-D_{ij}\widehat P_j)=-d_{ij}g(\widehat P_j)\). Choose \(\xi\le1/(32Q\Lambda)\) before running the covering solver. The inverted rational point witnesses \(v<1/Q\), so the support LP has optimum zero.

Solving the support LP exactly returns an original clearing pair for the enlarged capacities. One fixed-price flow recovers clearance for the original capacities at those minimum prices. The root approximations, the call to the near-factorized solver, signed integer powers and the final LP all use polynomial bit length. In particular \(\log(1/\xi)=O(\log Q+K+\log n+\log K)\), and the number of covering calls is polynomial by the contraction bound. This gives exact polynomial search even when the graph of allowed offers is sparse and the common offsets exist only on its edges. [Near-factorized solver](A4a-near-factorized-slopes.md) · [Original flow at the perturbed prices](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)
