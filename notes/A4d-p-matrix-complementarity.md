# A4d. A P-matrix reduction for exact prices and security games

**Theorem.** For binary rational inputs, each of the following search problems has a polynomial-time many-one reduction to a single promised P-matrix linear complementarity problem (P-LCP).

1. Find clearing prices and an allocation in the fractional assignment market with arbitrary strictly decreasing pair-specific affine utilities, outside options and reserves.
2. Find the componentwise minimum clearing prices and a compatible allocation in the same market.
3. Find an exact Bayes–Nash equilibrium in the explicitly given Bayesian simple security game, including zero attacker-loss slopes and zero defender gains.

Consequently all three problems belong to UniqueEOPL. The game reduction includes the defender's resource budget directly. The promise concerns the constructed P-LCP, whose solution is unique. The original game may have several equilibria. This sharpens A4c's CLS containment. The unrestricted polynomial-time algorithm remains open. [A4c, minimum-price reduction and CLS bound](A4c-any-clearing-equilibrium.md) · [L3, prior game and market reductions](L3-prior-partials.md) · [Fearnley, Gordon, Mehta and Savani, §4.3, Theorem 39](https://arxiv.org/pdf/1811.03841#page=37)

## Two equilibrium systems

Write \(0\le z\perp w\ge0\) for the conditions \(z_i,w_i\ge0\) and \(z_iw_i=0\) at each coordinate. In an LCP, \(w=b+Mz\) is affine. All variables in the two displays below are nonnegative.

**Market.** Let \(m_i>0\) be a buyer's mass, \(c_j\ge0\) a capacity, \(\rho_j\) a reserve and \(o_i\) an outside utility. Write \(p_j\) for the price above reserve, and \(b_{ij}=a_{ij}-d_{ij}\rho_j-o_i\), with \(d_{ij}>0\). The buyer's net outside utility is zero. With purchase amounts \(x_{ij}\) and net indirect utilities \(u_i\), take

\[
\begin{aligned}
 x_{ij}&\perp u_i+d_{ij}p_j-b_{ij},\\
 u_i&\perp m_i-\sum_j x_{ij},\\
 p_j&\perp c_j-\sum_i x_{ij}.
\end{aligned}                                                    \tag{1}
\]

A positive purchase attains the buyer's largest utility. The residual row mass takes the outside option and can be positive only at \(u_i=0\). Indeed, if the whole row takes outside then \(u_i=0\), and otherwise a positive purchase attains \(u_i\). A positive excess price forces the good to sell out. Conversely, every clearing allocation gives (1) by taking each buyer's maximum utility. The market price is \(\rho+p\).

**Game.** Let \(m_i>0\) be a type's prior, \(q_{ij}\) its prior-weighted attack mass and \(p_j\) the defender's coverage of target \(j\). The defender uses exactly \(r\) resources across \(n\) targets. For \(r=0\) or \(r=n\), use the forced coverage and pick a best target in each row. Suppose \(0<r<n\). Add a common constant to all utilities in each row so that its new intercepts \(a'_{ij}\) satisfy \(a'_{ij}-d_{ij}\ge1\). For instance, add \(1-\min_j(a_{ij}-d_{ij})\) in row \(i\). Write \(Q_j=\sum_i q_{ij}\). The marginal gain for covering \(j\) is \(\beta_j Q_j\). Increasing each marginal by one adds the constant \(r\) to the defender's objective on feasible coverages. Allowing \(d_{ij},\beta_j\ge0\), use

\[
\begin{aligned}
 q_{ij}&\perp u_i+d_{ij}p_j-a'_{ij},\\
 u_i&\perp m_i-\sum_j q_{ij},\\
 p_j&\perp \lambda-1-\beta_jQ_j+h_j,\\
 h_j&\perp 1-p_j,\\
 \lambda&\perp r-\sum_j p_j .
\end{aligned}                                                    \tag{2}
\]

The last two inequalities give \(p_j\le1\) and \(\sum_jp_j\le r\). The shifted utilities force \(u_i\ge1\), so each type sends its entire mass to maximizers. If \(\lambda=0\), the \(p_j\)-inequalities force \(h_j\ge1+\beta_jQ_j>0\) for every \(j\), hence \(p_j=1\) for every target. This contradicts \(r<n\). Thus \(\lambda>0\) and the full budget is used. The \(p,h\) conditions are precisely the defender's threshold conditions with shifted marginal \(1+\beta_jQ_j\). At zero coverage that marginal is at most \(\lambda\), at interior coverage it equals \(\lambda\), and at full coverage it is at least \(\lambda\). These conditions certify a best response by linear programming duality. Conversely, from an equilibrium choose \(\lambda\) equal to the \(r\)-th largest shifted marginal, set \(h_j=\max\{0,1+\beta_jQ_j-\lambda\}\), and take the type maxima for \(u\). This gives (2). [Compact game model](../README.md#compact-model)

Return \(q_{ij}/m_i\) as the conditional attacks. Types of prior zero, omitted when constructing (2), can be assigned a best target at the resulting coverage. An explicit defender mixture is also available in polynomial time. Partition \([0,r)\) into successive half-open intervals of lengths \(p_j\). For uniform \(t\in[0,1)\), choose the targets whose intervals contain \(t,t+1,\ldots,t+r-1\). The points lie in distinct intervals, and each target is chosen with probability \(p_j\). Sorting the fractional parts of the interval endpoints gives the pure strategies and their rational weights.

## Why every principal minor is nonnegative

A matrix is \(P_0\) when all its principal minors are nonnegative, and \(P\) when all its nonempty principal minors are positive. In (1) group the variables as \(x\mid (u,p)\). In (2) group them as \((q,h,\lambda)\mid(u,p)\). In either order the linear part is

\[
 M=\begin{pmatrix}0&B^{\mathsf T}\\-A&0\end{pmatrix}.
\]

A principal minor that selects different numbers of indices from the two groups vanishes by rank. If it selects columns \(C\) in the first group and node rows \(R\) in the second, with \(|C|=|R|\), its determinant is

\[
             \det A_{R,C}\,\det B_{R,C}.                         \tag{3}
\]

The block interchange and the sign in \(-A\) cancel. For this product we may multiply each target row by \(-1\) in both \(A\) and \(B\). The signed entries in these two arrays are as follows. Unlisted entries are zero.

| Column | Buyer/type row \(i\) | Good/target row \(j\) |
| --- | --- | --- |
| \(ij\) in the market | \(+1\) in both | \(-1\) in \(A\), \(-d_{ij}\) in \(B\) |
| \(ij\) in the game | \(+1\) in both | \(-\beta_j\) in \(A\), \(-d_{ij}\) in \(B\) |
| Upper multiplier \(h_j\) | | \(+1\) in both |
| Budget multiplier \(\lambda\) | | \(+1\) in both at **every** target |

First assume all gains and slopes are strictly positive. In the game divide row \(j\) of the signed \(A\) by \(\beta_j\). This preserves minor signs and makes each attack column an ordinary oriented incidence column, \(+1\) at its type and \(-1\) at its target. The market already has this form. View each \(h_j\) as an edge from \(j\) to a private leaf whose row is always omitted. Its one recorded entry remains positive in both arrays. In \(B\) each two-ended edge also has opposite signs, with arbitrary positive magnitudes.

**Edge columns.** If the chosen pair columns contain a cycle, their ordinary incidence columns in \(A\) are dependent before restricting rows. Then (3) is zero, even if \(C\) also contains \(\lambda\). Otherwise the edge columns form a forest \(F\), including any private leaves and all isolated vertices. Consider a square restriction consisting solely of forest columns. Its determinant is nonzero precisely when each tree has exactly one omitted vertex. Indeed, each tree has one fewer edge than vertices, and a determinant term must match its selected rows bijectively to its edges. With one omitted root, the matching is unique. It pairs each other vertex to its incident edge toward the root, as can also be seen by successively removing leaves. Thus on this restriction both determinants vanish together or consist of single monomials of the same sign. This proves (3) is nonnegative whenever the budget column is absent.

**The budget column.** Suppose \(\lambda\in C\) and the remaining columns form \(F\). Expand either determinant on the budget column. A cofactor at row \(v\in R\) deletes that row and uses only \(F\). If any cofactor is nonzero, the preceding criterion says that before deletion one tree \(T\) has every vertex selected, while every other tree already has one omitted vertex. Consequently the nonzero cofactors occur at exactly the vertices of \(T\) in both arrays. Their individual signs agree between \(A\) and \(B\) by the unique matching.

Within each array, the signed cofactor vector lies in the left kernel of the remaining columns by Laplace expansion with a repeated column. Along an edge of \(T\), opposite signs at the two endpoints imply that the two nonzero cofactor entries have the same sign. Connectedness gives a common sign throughout \(T\), including the case of a single vertex. All budget coefficients at target rows are positive in both arrays, and all coefficients at type rows vanish. The two expansions therefore vanish together or have the same sign. This proves (3) also for budget minors.

For weak game gains or slopes, take a limit from strictly positive coefficients in the original, unscaled matrices. Each principal minor is a polynomial in those coefficients. Its limit stays nonnegative, proving the \(P_0\) property at zeros as well.

## One exact P-LCP call

The November 2026 Newton theorem applies to this regularized call. L4 compares its handicap-dependent solve count with the continuation bound. A4f tests different formulations and proves that the large handicap can persist after arbitrary positive diagonal scaling. [Newton runtime](L4-newton-and-continuation.md) · [Bounded-handicap formulations](A4f-handicap-formulation.md)

A4g proves that the all-ones Lemke trajectory can take superpolynomially many pieces on the structured market matrix. It also gives exact shortcuts through selected affine regions or candidate price lists. [Bounded support search](A4g-budgeted-support-search.md)

For \(\varepsilon>0\), set \(M_\varepsilon=M+\varepsilon I\). For each nonempty index set \(S\),

\[
 \det (M_\varepsilon)_{S,S}
 =\sum_{T\subseteq S}\varepsilon^{|S|-|T|}\det M_{T,T}>0 .
\]

The empty minor contributes \(\varepsilon^{|S|}\), and the remaining terms are nonnegative. Thus \(M_\varepsilon\) is a P-matrix, and the LCP with residual \(b+M_\varepsilon z\) has a unique solution \(z^\varepsilon\). We bound it uniformly and choose a rational \(\varepsilon\) before making the call.

**Bounds for \(0<\varepsilon\le1\).** Let \(V\) be the maximum of one and all shifted intercepts \(b_{ij}\) in (1) or \(a'_{ij}\) in (2). In a positive \(u_i\) row the load equals \(m_i+\varepsilon u_i>0\). A positive edge on that row has \(u_i+d_{ij}p_j+\varepsilon x_{ij}=b_{ij}\) in (1), with \(q_{ij},a'_{ij}\) in (2). Hence \(0\le u_i\le V\). Every row load is at most \(m_i+\varepsilon u_i\le m_i+V\).

In (1) a positive \(p_j\) gives column load \(c_j+\varepsilon p_j>0\), even at zero capacity. Some positive edge \(ij\) then gives \(p_j\le V/\min_{ij}d_{ij}\). These inequalities bound every coordinate.

In (2) put \(H=1+(\max_j\beta_j)\sum_i(m_i+V)\). A positive \(h_j\) gives \(p_j=1+\varepsilon h_j>0\), and a positive \(p_j\) gives \(\lambda+h_j+\varepsilon p_j=1+\beta_jQ_j\le H\). Thus \(h_j\le H\), and the upper-bound inequality gives \(p_j\le1+\varepsilon h_j\le1+H\). If \(\lambda>0\), the budget row gives \(\sum_jp_j=r+\varepsilon\lambda>0\), so some positive \(p_j\) gives \(\lambda\le H\). In either model take \(K\ge1\) to be the ceiling of the maximum of the applicable coordinate bounds. Its binary encoding length is polynomial in the input.

**Recovering an original solution.** Let \(N\) be the LCP dimension. For a prospective support \(S\subseteq[N]\) consider this rational LP in \(N+1\) variables, with \(w(z)=b+Mz\) computed from the original data.

\[
\begin{aligned}
 \text{minimize }&t\\
 0\le z_i&\le K,\qquad 0\le t\le1,\\
 z_i&=0 &&(i\notin S),\\
 w_i(z)&\ge-t &&(i\in[N]),\\
 w_i(z)&\le t &&(i\in S).
\end{aligned}                                                     \tag{4}
\]

The inequalities and equalities available to all these LPs come from a single list with \(O(N)\) rows. Multiply each possible row by the product of its denominators, including the right side. Take \(D\) to be the maximum of one and the absolute values of the resulting integer entries. With \(Q=(N+1)!\,D^{N+1}\), Cramer's rule gives denominator at most \(Q\) for any coordinate of a vertex of any such LP. In particular, if the minimum is positive, compactness gives a minimizing vertex with \(t\ge1/Q\).

Choose \(\varepsilon=1/(2KQ)\) and call P-LCP once on \((M_\varepsilon,b)\). Its unique rational solution has polynomial bit length since its positive coordinates solve a nonsingular principal system of \(M_\varepsilon\). Take \(S=\{i:z^\varepsilon_i>0\}\). The pair \((z^\varepsilon,\varepsilon K)\) satisfies (4). In fact \(w(z^\varepsilon)\ge-\varepsilon z^\varepsilon\), with equality on \(S\). Since \(\varepsilon K<1/Q\), the exact optimum of (4) is zero. Solve this one LP on the returned support. At \(t=0\) every residual is nonnegative, every residual on \(S\) vanishes, and every coordinate outside \(S\) vanishes. The recovered point solves the original LCP, even when some coordinates on \(S\) drop to zero. All determinant bounds, the oracle input and the rational LP computation use polynomially many bits. [Rational linear programming, Grötschel, Lovász and Schrijver, §6.5](https://www.zib.de/userpage/groetschel/pubnew/paper/groetschellovaszschrijver1988.pdf)

For \(k\) types and \(n\) goods or targets, the respective LCP dimensions are \(kn+k+n\) and \(kn+k+2n+1\). Markets with an empty side and games with a forced coverage can be answered directly. Equivalently, these cases may issue a fixed one-dimensional P-LCP and return the directly computed answer. On all other inputs the constructed P-matrix satisfies the promise for every right side. Fearnley, Gordon, Mehta and Savani's reduction therefore produces a UniqueEOPL instance satisfying its single-line promise. [Theorem 39 and Appendix G.3 in the full version](https://arxiv.org/pdf/1811.03841#page=37) · [Journal publication](https://doi.org/10.1016/j.jcss.2020.05.007)

## Recovering the minimum market price

Before constructing the P-LCP for (1), increase each capacity to \(c'_j=c_j+\delta\), where \(D_0\) is the product of denominators of the original masses and capacities and \(\delta=1/(2nD_0)\). Let \(P=\rho+p\) clear at \(c'\). At those prices each buyer can send her fixed mass to demanded goods or outside. Connect the options back to the source with capacities \(c_j\) on goods and total buyer mass on outside. Give each good above reserve a lower bound equal to its capacity. A feasible circulation in this network gives a clearing allocation at \(c\).

To see feasibility, use the circulation cut criterion that the sum of incoming lower bounds is at most the sum of outgoing upper bounds at every cut. Buyer-to-option arcs can have total buyer mass as their upper bound. All original cut bounds are multiples of \(1/D_0\). When passing from \(c'\) to \(c\), incoming lower bounds can only decrease and outgoing upper bounds decrease by at most \(n\delta<1/D_0\). Since the allocation at \(c'\) satisfies all cuts, none can have a positive deficit at \(c\). This argument includes original capacities equal to zero.

If another original clearing price \(P'\) lowered any coordinates, let \(J=\{j:P'_j<P_j\}\). All goods in \(J\) are above reserve at \(P\). Buyers demanding at least one good in \(J\) therefore have total mass at least \(c'(J)>c(J)\), where \(c(J)=\sum_{j\in J}c_j\). At \(P'\) each such buyer strictly gains on a previously best good in \(J\), and every option outside \(J\) is weakly worse. All that mass must fit inside \(J\), a contradiction. Thus \(P\) is the original componentwise minimum. Solve the original circulation at \(P\) to return its compatible flow. This preprocessing and decoding preserve the single P-LCP call. [A4c, one-call proof](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

## A two-by-two obstruction to monotonicity

Even the unperturbed market matrix can fail the quadratic-form condition \(v^{\mathsf T}Mv\ge0\) required for a monotone LCP. In a two-buyer, two-good market take \(d_{11}=d_{12}=d_{21}=1,\ d_{22}=2\). Use the original unsigned \(A,B\) in the block matrix, list the four edges in row order, and list both buyers before the two goods. Put

\[
 f=(1,-1,-1,1),\qquad y=(5,7,-6,-4),\qquad v=(f,y).
\]

Every row and column sum of \(f\) is zero, so \(Af=0\). Direct substitution gives \(B^{\mathsf T}y=-f\). Thus \(v_i(Mv)_i=-1\) on each edge and zero on every node. After arbitrary positive diagonal row and column scaling \(L M R\), testing with \(R^{-1}v\) multiplies these coordinate products by positive factors. Their sum stays negative. For the unscaled regularized matrix, \(v^{\mathsf T}M_\varepsilon v=-4+130\varepsilon<0\) whenever \(0<\varepsilon<2/65\). Thus the P-matrix proof permits genuine failure of monotonicity in the very systems submitted to the oracle. A polynomial-time solver for this particular structured family would settle the equilibrium search question. [Borzechowski et al., §1 on the general P-LCP problem](https://drops.dagstuhl.de/storage/00lipics/lipics-vol297-icalp2024/LIPIcs.ICALP.2024.32/LIPIcs.ICALP.2024.32.pdf)
