# A4h Complete candidate generation

Kintali’s algorithm and the A4i reduction recover the exact minimum-price vector at the supplied capacities in polynomial bit time. That vector is a complete singleton list. [Supplied-capacity result](A4h-supplied-capacity.md#one-exact-candidate-at-the-supplied-capacities)

This note studies direct candidate generation from the market’s own structure. A4g searches a product of coordinate lists in time polynomial in their total length, so separate lists containing the corresponding coordinates of the minimum-price vector suffice. A list that includes an affine region containing the regularized solution also suffices. The results below give complete lists under additional structure and lower bounds for several restricted generators. A general direct generator that runs in polynomial bit time remains open. [Price-list and region finishers](A4g-budgeted-support-search.md)

## Polynomially many queries are possible

There is an unconditional polynomial bound on the number of adaptively chosen candidate regions in a query model. Take the regularized A4f contraction on buyer utilities and signed good prices. Use a common rational width \(R\) for its box and translate and scale it to \([0,1]^d\). The contraction factor \(\lambda<1\) is unchanged, and \(\log(1/(1-\lambda))\) is bounded by a polynomial in the original input length. A determinant bound on the unique regularized solution gives a computable denominator bound \(D_s\) on its offer slacks \(b_{ij}-B_{ij}^{\mathsf T}h^*\). A nonzero slack has magnitude at least \(1/D_s\).

The grid algorithm of Haslebacher, Lill, Schnider and Weber finds a point with \(\ell_1\) residual at most \(\eta\) in \(O(d^2(\log(1/\eta)+\log(1/(1-\lambda))))\) queries, at grid points of polynomial bit length for the tolerances here. The point is within \(R\eta/(1-\lambda)\) of \(h^*\) in the original coordinates. Choose

\[
\eta<\frac{1-\lambda}{2R(1+d_{\max})D_s}.
\]

Then every nonzero offer sign is correct, and either sign choice is valid on an exact zero. The resulting sign region contains \(h^*\) in its closure. A4g solves that region and A4d repairs exactly. The theorem counts queries. Its centerpoint step chooses a query from the surviving grid and supplies no polynomial total-time bound for that choice. [Grid theorem and centerpoint discussion](https://arxiv.org/html/2503.16089v3#S4.SS2) · [A4f contraction and precision](A4f-handicap-formulation.md#eliminating-flow-variables)

## Candidate lists from one-good separators

Build the goods-interaction graph by joining two goods if a buyer has positive net offers at reserve on both. Each buyer's viable goods form a clique and lie in a single biconnected block. Assign one-good buyers to an incident block or to their isolated good. Root the block–cut tree. A nonroot branch shares one articulation good \(h\) with the remaining market.

For a trial price \(t\) on \(h\), the branch's message \(L_h(t)\) is its least necessary flow into \(h\) with \(h\) uncapped and all internal capacities respected. It is a nonincreasing, right-continuous step function of \(t\) that is zero at a sufficiently high price. One computes it at the conditional minimum for the internal goods, treating the offer on \(h\) as an extra outside alternative. This conditional choice minimizes parent usage among all buyer-feasible branch completions. In detail, take any other completion \(q\) with the same parent price. Lower to the conditional minimum. Use its flow for buyers whose utility increases, all of whom use strictly cheaper internal goods. For the other buyers keep their old flow, which cannot use the strictly cheaper goods. The merged flow uses no more at the parent than the original completion. [A4b coordinate test](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)

Replace a completed child message at good \(j\) by unary buyers on \(j\). A jump of size \(\Delta\) at \(\nu\) gives a buyer of mass \(\Delta\) with offer \(\nu-p_j\) and outside zero. It forces \(\Delta\) units at \(p_j<\nu\) and can choose outside at \(p_j=\nu\). The total minimum drain from these buyers is exactly the message. The preceding flow swap shows that the buyer-feasible prices of the augmented block are exactly the projections of buyer-feasible prices of the block with its descendants. Extension uses actual child flows attaining their minimum drains. The least prices on the block can therefore be computed in the augmented block.

### Generate the breakpoints adaptively

Let \(q>0\) be a common quantity quantum, so all original margins are integer multiples of \(q\). It can be the reciprocal of a common denominator. Every actual message value is a multiple of \(q\) by fixed-price unweighted flow integrality. Suppose the current boundary price has message level \(\ell>0\). Solve the augmented block with boundary capacity \(\ell-q/2>0\). Its least boundary price is exactly the next breakpoint. In fact it is the first \(t\) with \(L_h(t)\le\ell-q/2\) by A4b, and this is the first strict drop from \(\ell\). At that price recompute the message by a minimum-parent-usage flow at the conditional minimum and repeat. Start at reserve and stop at level zero. This takes one augmented block solve per actual breakpoint, without listing intermediate capacity values.

With a fixed maximum block size \(k\), solve each augmented block by enumerating the vertices of its price arrangement. Use comparisons of local offers, including unary offers and outsides, and reserve and finite ceiling hyperplanes. The least buyer-feasible price is a vertex. In the relative interior of a positive-dimensional cell, the demand graph stays constant and a sufficiently small move within the cell can lower some coordinate, contradicting price domination. Thus a polynomial number of local vertices suffice. For unbounded block size the same recursion applies if an exact local solver is available for a class closed under adding unary offers and changing the boundary capacity.

If the block has \(M\) offers including its unary offers, at most \(O(M^2+k)\) hyperplanes are needed. Enumerating at most \(O((M^2+k)^k)\) candidate vertices and testing each by one flow finds the feasible price minimizing the price sum. A sweep uses one such solve per reported drop, plus one conditional solve and one minimum-load flow at each visited price, including reserve. The total number of offers processed is polynomial in the input length and the total number of reported drops.

After the root solve, descend at the recovered articulation prices, using the least conditional completion in every branch. Substituting such a completion cannot raise any price or consume additional capacity at the attachment. It must recover the original least vector by domination. One fixed-price flow recovers original clearance. Each retained breakpoint is the least price of a genuine subtree market with a trial boundary capacity. The tight anchor path bound using the original offers gives polynomial bit length, independently of the depth of synthetic buyers. Message quantities are signed sums of original margins and also have polynomial bit length.

### Bounds that give polynomial candidate generation

At the internal conditional price vector extended by \(t\) on \(h\), a Hall cut gives

\[
 L_h(t)=\max_{S\subseteq J\setminus\{h\}}
 \left[f_{(t,p)}(S\cup\{h\})-\sum_{j\in S}c_j\right],
\]

where \(f(S)\) counts buyers restricted to \(S\) and \(J\) denotes the branch's goods. Cuts excluding \(h\) already pass with \(h\) uncapped. Thus every level is a difference of a subset sum of original masses and a subset sum of original internal capacities. With \(s\) distinct margin values, there are at most \((2N+1)^s\) such differences, where \(N\) counts all margin entries. This gives polynomially many exact candidates for fixed \(k,s\), with arbitrarily deep block trees and binary magnitudes. A separate sufficient bound uses the quantity quantum. The range of the message is at most the mass of buyers in the branch who consider \(h\), so polynomial mass in units of \(q\) at each attachment also suffices.

One unrestricted binary-margin class consists of a forest with bounded-size leaf blocks attached at single goods. Compute a leaf's message by the same algorithm. Its range has polynomial size because it comes from the polynomial number of whole local demand cells in fixed dimension, including the boundary price. Replace each leaf by its unary buyers and use A4b on the remaining forest. This handles arbitrarily many cyclic decorations, and does not require a bound on their combined cycle rank or feedback size. [A4b arbitrary binary-margin forests](A4b-direct-hall-search.md#polynomial-time-on-arbitrary-forests)

### Polynomial tables without a margin bound

A stronger binary-margin result applies when each block has a bounded number of goods and at most two articulation goods. It also applies when each block has bounded numbers of original buyers and goods, with arbitrary branching through the articulations. Artificial unary buyers representing descendants are excluded from the latter size bound.

To prove the bound, take a nonroot block with parent attachment \(h\) and choose one downstream attachment \(j\). Call the child blocks of \(j\) distinguished and aggregate their loads as \(B_j(x)\) at \(p_j=x\). Encode the other child messages as unary buyers on their local goods. Let \(K\) consist of the local goods other than \(h,j\). At fixed \(p_h=t,p_j=x\), fold both boundary offers into outside and compute the least local prices \(y(t,x)\) on \(K\). For \(\varnothing\ne E\subseteq\{h,j\}\) let

\[
 R_E(t,x)=\max_{S\subseteq K}\bigl[f_{t,x,y(t,x)}(S\cup E)-c(S)\bigr].
\]

The same flow swap works with both boundary prices fixed. Thus the local capacity tests at \(h\)-capacity \(w\) are \(R_{\{h\}}\le w\), \(R_{\{j\}}+B_j(x)\le c_j\) and \(R_{\{h,j\}}+B_j(x)\le w+c_j\). Internal-only cuts already pass at the conditional local minimum. Let \(x(t)\) be the least price of \(j\) conditional on \(h\) being set at \(t\) and uncapped. The associated least prices on \(K\) equal \(y(t,x(t))\) by conditional price domination. At those prices the outgoing message is therefore

\[
 L_h(t)=\max\{R_{\{h\}}(t,x(t)),\ R_{\{h,j\}}(t,x(t))+B_j(x(t))-c_j\}.
\]

All conditional internal prices are nondecreasing with \(t\). Decreasing an outside offer shrinks the set of internal buyer-feasible prices, since any flow feasible with the lower outside offer remains feasible with the higher one by sending newly outside-preferring buyers there. The two-attachment term \(R_{\{h,j\}}(t,x(t))\) is nonincreasing. To see this, merge \(h,j\) into one good \(e\) at reserve zero with buyer intercept \(\max(v_{ih}(t),v_{ij}(x))\) and unit slope. In this auxiliary market \(R_{\{h,j\}}\) is precisely the least \(e\)-capacity for which reserve zero is feasible. As \(t\) and \(x\) rise, the merged intercepts decrease buyer by buyer. If a capacity passes for the old intercepts but fails for the new ones, compare an old buyer-feasible price with \(p_e=0\) to the new least price. Let \(S\) be the coordinates that rose. It includes \(e\), and each coordinate of \(S\) is now above reserve. Every buyer touching \(S\) at the new price is strictly restricted to \(S\) at the old price, since the only intercept changes favor old offers in \(S\). The strict Hall bound at the new price then contradicts old feasibility at the same capacities. Thus the least passing capacity does not increase.

Let \(Q_B\) bound the number of demand graphs of the **original** buyers in block \(B\), over all its local price vectors. An arrangement of their offer comparisons gives a polynomial \(Q_B\) for bounded block goods, and a constant for bounded original buyers and goods. Denote by \(J_C\) the number of drops in a child message. Along the monotone internal prices, the vector of loads of the nondistinguished children changes at most \(\sum_{\mathrm{other}\ C}J_C\) times. Between changes, these unary buyers contribute a fixed forced mass at each local good. Each \(R_E\) therefore takes at most \(Q_B\) values per such interval, since its remaining inputs are the original demand graph and fixed capacities. The two-attachment term is nonincreasing and \(B_j(x(t))\) is nonincreasing, so their sum has at most the sum of their drop counts. \(R_{\{h\}}\) can oscillate, but takes only the counted distinct values. As \(L_h\) itself is nonincreasing, its total drops satisfy

\[
 J_B \ \le\ \sum_{C\text{ at }j}J_C
             + 2Q_B\left(1+\sum_{\mathrm{other}\ C}J_C\right).
\]

For a leaf block the local demand-graph count supplies the bound directly. With at most two articulation goods there are no nondistinguished children, so these bounds add at arbitrary depth. For general branching, choose \(j\) to contain the largest child subtree. Each edge to another child at least halves the subtree size, so a root-to-leaf path has at most \(\log_2 N\) such edges. Unrolling the recurrence with constant \(Q_B\) multiplies each local contribution by at most \((2\max Q_B)^{\log_2 N}\). Thus all message tables have polynomial total size. The adaptive breakpoint solver generates exactly those tables. With bounded goods but unbounded original buyers per block, the same branching argument gives a quasipolynomial bound, while the two-articulation case remains polynomial.

## Guess aggregate slope corrections

Normalize buyer utilities and good prices by arbitrary positive rational row and column scales, leaving the masses, capacities and allocations unchanged. Write the resulting cover as \(U_i+s_{ij}P_j\ge B_{ij}\). Let \(X\) be the ordinary transportation polytope of nonnegative flows with row bounds \(m_i\) and column bounds \(c_j\). Define \(T_j(x)=\sum_i(s_{ij}-1)x_{ij}\). For every \(x\in X\) and feasible normalized cover, the sum of nonnegative complementarity products equals

\[
 m\cdot U+\sum_j(c_j+T_j(x))P_j-\sum_{ij}B_{ij}x_{ij}.
\]

At a proposed \(T\) impose \(T(x)=T\) and set this expression to zero. Both additions are linear. Feasibility gives a clearing equilibrium, and minimizing the original price sum in each LP and comparing across a complete list recovers the original minimum. The guesses do not specify which edges are tight or which carry the correction. [A4e gap identity](A4e-covering-lp.md#reweighting-with-an-allocation)

Take \(q\) to be the rational greatest common divisor of the positive margins. At a clearing price, the fixed-demand transportation problem has an exact flow in units of \(q\). If a good has capacity \(C_j=c_j/q\) in these units and \(r_j\) different nonzero normalized slope errors \(e_{j1},\ldots,e_{jr_j}\), all corrections at that good occur among

\[
 q\sum_{a=1}^{r_j}e_{ja}z_a,\qquad z_a\in\mathbb Z_{\ge0},\quad \sum_a z_a\le C_j.
\]

This has at most \(\binom{C_j+r_j}{r_j}\) choices. Enumerating their product gives an exact solver whenever the product is polynomial. For example, there can be \(O(\log L)\) heterogeneous goods of bounded capacity in the chosen units with a bounded number of normalized slopes per good. Each can connect to every buyer, and other margins may be large binary numbers. One can also localize defects at either endpoint. Multiply each edge complementarity product by a positive \(\gamma_{ij}\), and the buyer and good slack products by positive \(a_i,v_j\). Buyer corrections are then \(\sum_j(\gamma_{ij}-a_i)x_{ij}\), and good corrections are \(\sum_i(\gamma_{ij}d_{ij}-v_j)x_{ij}\). Choosing \(\gamma_{ij}=a_i\) or \(v_j/d_{ij}\) removes that edge's correction at the chosen endpoint. The same counting test applies to the remaining node corrections.

A second candidate filter uses the projection

\[
 Q=\{(T(x),B\cdot x):x\in X\}.
\]

At equilibrium the compatible allocations are the optimizers of \(B\cdot x-P\cdot T(x)\), by the gap identity. At least one vertex of that exposed face of \(Q\) therefore supplies a valid correction. For a single nonzero correction coordinate one can enumerate the upper polygon by LP optimization in the normals to chords between known vertices. If a chord is supported, its endpoints are consecutive on the upper hull. Otherwise optimize in its normal to split it, taking an endpoint of any exposed face by a secondary objective. The number of LP calls is linear in the number of output vertices. This can avoid a large quantity grid, but the complete upper hull need not have polynomial size, even in two dimensions.

## Approximate common offsets give one exact candidate

There is a binary-margin subclass with unbalanced slopes and slightly inconsistent offsets, for which an adaptive candidate search contracts. Drop nonpositive offers and use zero reserves and outsides. Set \(\delta=1/(100n)\) and test for positive \(t_j\) and row quantities \(A_i\) satisfying

\[
 (1-\delta)d_{ij}t_j\le A_i-b_{ij}\le(1+\delta)d_{ij}t_j
\]

on every remaining edge. This is an LP by maximizing a common lower bound \(0\le\rho\le1\) on all \(t_j\). A positive optimum finds polynomial-bit rational data. At the allowed price range \(0\le p_j\le H_j=\max_i b_{ij}/d_{ij}\), both \(t_j+p_j\) and \(A_i-(b_{ij}-d_{ij}p_j)\) are strictly positive.

Use increasing rational piecewise-linear coordinates \(\Psi_j(p)\) and \(\Phi_i(u)\), anchored at zero. Approximate derivatives \(1/(t_j+p)\) and \(1/(A_i-u)\) on the full price and offer ranges, including outside utility. For a positive argument \(s\) in a knot interval \([s_0,(1+\delta)s_0]\), use derivative \(1/s_0\). This gives an approximation between \(1/s\) and \((1+\delta)/s\). There are polynomially many geometric knots and each has polynomial bit length. In price coordinate \(z_j=\Psi_j(p_j)\), the transformed offer \(W_{ij}(z_j)=\Phi_i(b_{ij}-d_{ij}\Psi_j^{-1}(z_j))\) has slope magnitude between \((1+\delta)^{-2}\) and \((1+\delta)/(1-\delta)\). The normalization inequality gives this through the ratio \(d_{ij}(t_j+p_j)/(A_i-b_{ij}+d_{ij}p_j)\).

Freeze each transformed offer with ordinary unit-slope bids \(W_{ij}(z_j)+z_j\) and take the least prices in that TU market. Clip them to the transformed price box. Each frozen intercept changes with slope of absolute value below \(1/(4n)\), so the A4a sensitivity bound makes this map a contraction with factor less than \(1/2\). The transformed true least price is fixed because the demand graph, reserve status and minimum-price test agree there. A4g's tight path bound and the rational piecewise-linear coefficients give a polynomial-bit denominator bound for the transformed fixed point. Dyadic-rounded contraction iteration, rational reconstruction, exact inverse coordinate maps and one flow give the original price and allocation in polynomial bit time. [TU sensitivity and finite precision](A4a-near-factorized-slopes.md#stability-of-least-tu-prices) · [Exact common offsets](A4e-covering-lp.md#common-offsets-with-arbitrary-slopes)

The condition can hold with arbitrarily large cycle gains and no exact common offsets. Use \(k=n=2h\ge4\) with slopes 1 except for \(d_{2a,2a}=D\ge16\), \(a=1,\ldots,h\). Put \(A_i=2D+1,\ t_j=1\), \(b_{ij}=A_i-d_{ij}\), and increase \(b_{13}\) by \(\delta/2\). A unit-slope rectangle on rows and columns 1 and 3 has nonzero alternating intercept sum, so exact common offsets are impossible. In each disjoint \(2\times2\) principal cycle the ratio of alternating slope products is \(D\), invariant under row and column scaling. At least one column in each pair must have normalized slope error at least \((\sqrt D-1)/(\sqrt D+1)\ge3/5\). These violate even A4a’s wider global bound when \(h\ge2\). The approximate-offset LP still passes on this family with arbitrary binary masses and capacities.

## Limits on complete tables and fixed formulas

### Fixed affine libraries

Even unit slopes defeat a polynomial-size library of affine price formulas fixed independently of the intercepts. Take \(n\) buyers of mass 1 and \(n+1\) goods of capacity \(c=1-1/(2n)\), with \(n\ge2\). Fix the root \(g_0\) and terminal \(g_n\). For any alternating Hamiltonian path \(g_0,i_1,g_1,\ldots,i_n,g_n\), set the initial prices to zero at the root and one elsewhere, and buyer utilities to two. On a path edge set the intercept to utility plus price. Set other intercepts one half below that value, so every edge remains viable. Buyer \(i_k\) sends \((n-k+1)/(2n)\) left and the remainder right. Every path edge has positive flow, every nonroot good is full, and the root has slack.

On an open intercept box around these data, propagate equalities from \(p_{g_0}=0\) along the path. All other edge slacks remain positive and the old flow still clears. Complementary slackness for the unit-slope assignment LP forces every clearing dual to retain those path equalities and the zero root price, because the exhibited primal flow is optimal and has that positive support and slack. Hence the unique terminal price is

\[
 p_{g_n}=\sum_{k=1}^n\bigl(b_{i_k,g_k}-b_{i_k,g_{k-1}}\bigr).
\]

There are \(n!(n-1)!\) distinct such forms. A fixed library missing one cannot cover its open box, since each wrong formula agrees with it only on a proper hyperplane. Polynomial-bit rational inputs suffice. For instance perturb each intercept independently by \(r/(64nD)\) for integers \(0\le r<D\), with \(D=2^{n^2}\). The changes to prices and utilities along the path are at most \(1/32\), so the strict slacks persist. Each proper hyperplane meets at most a \(1/D\) fraction of this grid. This also rules out a polynomial library of fixed forests with a fixed allowance of off-forest edges, since those unfold to polynomially many path formulas. Data-dependent choice of a forest is outside the bound, and these unit-slope inputs have a direct assignment LP.

### Lists that omit masses

Even arbitrary formulas using all offers and capacities can fail if they omit row masses. Use goods \(g_0,\ldots,g_h\) with capacities one except \(c_{g_h}=1/2\). Between each \(g_{k-1},g_k\) have two buyers. Each values the left at \(4-p_{k-1}\), one values the right at \(4-3p_k\), and the other values the right at \(6-2p_k\). Other offers can be \(1-p_j\). For each bit \(z_k\), use

\[
 p_k=\begin{cases}
 p_{k-1}/3&z_k=0,\\
 1+p_{k-1}/2&z_k=1,
 \end{cases}
 \qquad p_0=0.
\]

For bit zero the first buyer ties and the second strictly prefers right. For bit one the second ties and the first strictly prefers left. Give the tying buyer mass \(3/4\) and the strict buyer mass \(1/4\). The tying buyer can split so that each link sends one half to each endpoint, with positive mass along both tied edges. Every nonroot good is full and the root is slack. All unlisted best-response alternatives are strictly worse. A4’s tight connectivity test certifies that this is the least price.

The price is unique even with these heterogeneous slopes. If a higher clearing price raises \(S\), buyers who used an unchanged good under the displayed flow cannot buy in \(S\) at the higher price. If \(S\) contains the root, its old capacity already had slack. Otherwise a tied buyer has positive purchases across a boundary of \(S\) along the chain. In either case the buyers who bought entirely in \(S\) have total mass strictly below \(c(S)\), so they cannot sell out \(S\) at the higher price. The two price updates have disjoint images on \([0,2)\). Reading back from \(p_h\) thus recovers the full bit word. There are \(2^h\) prices with all offers and capacities fixed, even with a constant alphabet of slopes, offers and masses. A method observing masses at only \(q\) links and returning at most \(K\) terminal prices can cover at most \(2^qK\) of the words, since there are at most \(2^q\) resulting transcripts.

### A single boundary table and a two-dimensional load hull

One capacity parameter can produce exponentially many exact price breakpoints even with unit slopes. Use the four-arc counting network of Disser and Skutella. Start with one arc of capacity 1 and cost 1. Given a network of maximum throughput \(F\) between \(s,t\), add new terminals \(S,T\), arcs \(S\to s,t\to T\) of capacity \(F\) and cost zero, and arcs \(S\to t,s\to T\) of capacity \(F\) and cost \(2F\). At total throughput \(x\) the inner throughput \(y\) ranges up to \(\min(x,2F-x)\), and the added cost is \(2F(x-y)\). The inner marginal costs are below \(2F\), so the optimum takes the greatest \(y\). Induction gives, after \(k\) stages, a cost curve \(C_k(x)\) on \([0,F]\), \(F=2^k\), with successive unit-interval slopes \(1,3,\ldots,2F-1\). The network has polynomial binary size. [Disser and Skutella, §3.1 and Figure 1](https://www2.mathematik.tu-darmstadt.de/~disser/pdfs/DisserSkutella18.pdf#page=6)

Convert each network vertex to a good. Give each arc \(e=(a,b)\) of capacity \(U_e\) and cost \(c_e\) a buyer of mass \(U_e\) with unit-slope intercepts \(L+A_a\) at good \(a\) and \(L+A_b-c_e\) at good \(b\). Put \(A_s=0\), \(A_v=R\) elsewhere, with positive \(R,L\) larger than the number of vertices times the largest arc cost, plus one. Each nonsink good has capacity equal to total outgoing arc capacity. Only the sink capacity \(x\) varies. A minimum-cost \(s\)-to-\(t\) flow of value \(x\) assigns \(f_e\) at the head and \(U_e-f_e\) at the tail. Internal and sink capacities fill, while the source has slack \(x\). Residual shortest-path potentials \(\lambda_v\), normalized by \(\lambda_s=0\), satisfy \(\lambda_b-\lambda_a\le c_e\) on unsaturated arcs and the reverse inequality on positive arcs. Thus prices \(A_v-\lambda_v\) support this allocation. Shortest paths from an added zero-cost source bound \(|\lambda_v|\) by the number of vertices times the largest arc cost. Every non-source price and every buyer's utility therefore has the required nonnegative sign.

The optimal unit-slope market value is consequently \(W(x)=\mathrm{const}+R x-C_k(x)\), by summing the arc offers on the flow. Any clearing price \(p_t\) is a supergradient of \(W\) in sink capacity because its feasible assignment dual remains feasible as the capacity changes. At each \(j-1<x<j\) it follows that every clearing price has \(p_t=R-(2j-1)\). By the one-boundary coordinate test, each of these distinct prices is a strict drop of the corresponding boundary load function. Thus writing a full response table for unrestricted binary margins can take exponential size. The goods graph has a path decomposition of width three using successive terminal pairs. A fixed-capacity variant adds a sink-only buyer of mass \(F-x\) with an intercept above every original sink offer. The buyer must purchase that amount, because a price so high that she declines would permit too little total sale at the sink. Then varying just this one mass gives the same price behavior.

The same construction makes the upper-hull filter for load corrections exponential with only one correction coordinate. Append a final arc of capacity \(F\) and cost zero to a new sink \(h\). Its market buyer \(v\) has intercept \(L+R\) at both endpoints. Set \(c_t=c_h=F\) and make the slope on \(vh\) equal to 2, with all other slopes 1. The ordinary assignment polytope ignores those slopes. Its correction \(T_h=x_{vh}\) equals the head flow on the appended arc. For fixed \(T_h=x\), assigning \(F-x\) units of \(v\) at \(t\) allows the old optimum of value \(W(x)\). Leaving some amount \(\sigma\) of \(v\) unassigned would free \(\sigma\) units of capacity at \(t\). The old dual bounds the resulting gain by \(p_t\sigma\), which is below the new buyer's loss \((L+R)\sigma\) for \(\sigma>0\). Thus the best assignment value at fixed \(T_h\) is exactly \(W(x)+F(L+R)\).

To retain an unbalanced cycle, add one buyer \(a\) and good \(g\), both of margin 1, with unit-slope intercepts 3 at \(ag\) and 1 at \(ah,vg\). In every fixed-\(T_h\) assignment optimum, \(x_{ag}=1\). Moving to that value and discarding \(x_{ah},x_{vg}\) loses at most twice the added private amount in the other offers and gains three times it. This leaves \(T_h\) and the old feasible assignment capacities intact. The cycle \(v,h,a,g,v\) has gain 2 and the hull acquires only the constant 3. Every integer corner of \(W\) is exposed by a positive penalty on \(T_h\), yielding at least \(2^k+1\) upper vertices. This is a bound on enumerating all exposed corrections. It leaves open finding a suitable one directly.

Counting the price plateaus or boundary-load jumps is NP-hard even with unit slopes. At a supplied capacity, load clipping and conditional load queries give further polynomial classes, including cases with exponential branch tables. A general polynomial-time generator remains equivalent to general exact polynomial-time search. [Count reduction and endpoint conventions](A4h-table-count-hardness.md) · [Capacity-specific candidate generation](A4h-supplied-capacity.md)
