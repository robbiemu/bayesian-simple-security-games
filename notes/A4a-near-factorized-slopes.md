# A4a. Exact minimum prices near factorized slopes

**Theorem.** A fractional unit-demand assignment market with \(n\ge1\) goods admits a polynomial-bit-time minimum-price oracle if its pair-specific slopes satisfy

\[
 \left|\frac{d_{ij}}{\alpha_i\beta_j}-1\right|\le\frac{1}{4n}
 \qquad\text{for some positive row and column factors }\alpha_i,\beta_j .
 \tag{1}
\]

The algorithm finds the factors, the componentwise least clearing prices and a compatible allocation. Buyer masses \(m_i>0\), capacities \(c_j\ge0\), reserves \(r_j\), outside utilities \(o_i\), intercepts \(a_{ij}\) and slopes \(d_{ij}>0\) are binary rationals. Buyers may split their mass among tied best options. Every good priced strictly above reserve sells out.

A sharper algorithm below allows the uniform bound \(1/(2n-1)\), including equality, and gives a column-specific condition that covers an arbitrarily heterogeneous single good. The near-factorized case already includes A4's superpolynomial auction example. In that construction \(\alpha_i=\beta_j=1\) and the largest slope error is at most \(1/(64nM)\), with \(M\ge1\). The minimum prices on those instances can therefore be computed in polynomial bit time. L3 keeps the slope matrix fixed across its oracle calls and transfers the algorithm to Bayesian security games. If a defender gain is zero, A1 perturbs that gain and recovers an exact original equilibrium by LP. This preserves the slope condition. The exactly factorized rescaling appears in Oki and Sato. [A4 auction lower bound](A4-minimum-price-markets.md#lower-bound-for-the-directional-ascending-auctions) · [L3 oracle reduction](L3-prior-partials.md#conditional-exact-reduction-to-a-minimum-price-oracle) · [A1 exact repair](A1-threshold-transport.md#4-transfer-an-exact-positive-coefficient-solver-to-weak-inequalities) · [Oki and Sato, Assumption 4.1 and Theorem 6.4](https://arxiv.org/html/2604.10563v3#S4.SS1)

## Normalization and a transferable-utility oracle

For prescribed rational error bounds \(e_j\ge0\), suitable factors exist precisely when the following rational system is feasible.

\[
 x_i,y_j\ge1,\qquad
 (1-e_j)x_i\le d_{ij}y_j\le(1+e_j)x_i\quad(i,j).
\]

Positive factors give a solution by multiplying \(x_i=\alpha_i,\ y_j=1/\beta_j\) by the same sufficiently large scalar. A feasible rational solution of polynomial encoding length gives factors \(\alpha_i=x_i,\ \beta_j=1/y_j\). Write

\[
 z_j=\beta_j(p_j-r_j),\qquad
 b_{ij}=\frac{a_{ij}-d_{ij}r_j-o_i}{\alpha_i},\qquad
 s_{ij}=\frac{d_{ij}}{\alpha_i\beta_j}=1+\eta_{ij}.
\]

The normalized utility for good \(j\) is \(b_{ij}-s_{ij}z_j\), the outside option is zero and \(z\ge0\). The transformation preserves demands, clearing flows and price order. Below the outside option is denoted by \(0\).

At a trial vector \(t\in\mathbb R^n\), set \(B_{ij}(t)=b_{ij}-\eta_{ij}t_j\). Define \(F(t)\) as the least prices in the transferable-utility (TU) market with buyer utilities \(B_{ij}(t)-z_j\). For any fixed intercept matrix \(B\), the allocation LP and its price dual are

\[
\begin{aligned}
 \max_{X\ge0}\ &\sum_{ij}B_{ij}X_{ij}
 &\quad \min_{u,z\ge0}\ &\sum_i m_i u_i+\sum_j c_j z_j\\
 \sum_j X_{ij}&\le m_i,\quad \sum_i X_{ij}\le c_j
 & u_i+z_j&\ge B_{ij}.
\end{aligned}
\]

Unallocated buyer mass takes the outside option. By complementary slackness the projected optimal dual prices are exactly the clearing prices, and any optimal allocation clears at each of them. To select the least prices, minimize \(\sum_j z_j\) on the dual optimal face. Given two optimal pairs, taking their componentwise maximum in \(u\) and minimum in \(z\) preserves feasibility, as does the opposite choice. The two new objectives sum to the two old objectives, so both new pairs are optimal. If any optimum lowered a coordinate of a sum-minimizer, the coordinatewise minimum of their prices would improve its sum. The bounded allocation LP has an optimum, and the secondary price objective is bounded below by zero on the nonempty dual optimal face. Hence both optima are attained, including with zero capacities. This computes \(F(t)\) by rational LP for every rational \(t\), with the input masses and capacities as given. [Shapley and Shubik, assignment-game price duality](https://doi.org/10.1007/BF01753437) · [Grötschel, Lovász and Schrijver, rational polyhedra, §6.5](https://www.zib.de/userpage/groetschel/pubnew/paper/groetschellovaszschrijver1988.pdf)

## Stability of least TU prices

Let \(p,q\) be the least prices at two intercept matrices \(B,B'\) with all other data fixed. Write \(\delta_j=\max_i|B_{ij}-B'_{ij}|\) and \(\delta_0=p_0=q_0=0\). Then for each good \(j\),

\[
 |q_j-p_j|\ \le\ \delta_j+2\sum_{k\ne j}\delta_k .
 \tag{2}
\]

At a clearing price \(q\), let \(I_q(S)\) be the set of buyers who demand at least one member of \(S\). If \(q\) is the least TU price, then for every nonempty \(S\subseteq\{j:q_j>0\}\),

\[
 m(I_q(S))>c(S). \tag{3}
\]

Indeed all goods in \(S\) are full. In case of equality every buyer touching \(S\) uses all her mass there. Lower every price in \(S\) by the same sufficiently small amount. These buyers' assigned options still maximize their utilities, and buyers with no old demand in \(S\) retain their assignments by strict slack. This would give a lower clearing price. Conversely, for **any** strictly decreasing pair utilities, (3) at a clearing price implies it is least. If a second clearing price lowered a nonempty set \(S\) of coordinates, take \(S\) to be the whole set of decreases. Every buyer in \(I_q(S)\) would then strictly prefer \(S\) to its complement and the outside option, violating its capacity. [A4 weighted minimum-price certificate](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

For the proof of (2), put \(h_j=q_j-p_j\) and take any allocation clearing at \(p\). Draw \(j\to k\) if some buyer demands \(j\) at \(q\) in the second market and receives positive mass on \(k\) at \(p\) in the first. The two utility comparisons on that arc give

\[
 h_j-h_k \le \delta_j+\delta_k .
\]

Every nonempty set of goods with \(h_j>0\) has an outgoing arc. Otherwise, every buyer demanding that set at \(q\) would use all her mass inside it at \(p\), contradicting (3), since \(q_j>p_j\ge0\) there. Starting from any \(h_j>0\), take a simple path to \(0\) or a good with \(h_k\le0\). Summing the arc inequalities counts the start once, each internal good twice and the endpoint at most once. This proves the upper bound in (2). Interchanging the markets proves the lower bound. In particular the sup-norm Lipschitz constant is at most \(2n-1\). A direct \(2n\) estimate also follows by sorting the positive \(h_j\) together with zero. A consecutive gap larger than \(2\max_j\delta_j\) would leave the upper set with no outgoing arc. Solymosi gives exact sensitivity results for uniform changes in one participant's reservation value in a unit assignment market. [Solymosi, §§3–4](https://unipub.lib.uni-corvinus.hu/9034/1/Sensitivity_of_fair_prices_in_assignment_market_ST_23.pdf)

**Sharpness.** Take unit masses for buyers \(0,\ldots,n\) and unit supplies for goods \(1,\ldots,n\). Buyer 0 values good 1 at 1. Each buyer \(j\ge1\) values her own good at \(H=4n+1\) and also the next one at \(H\) when \(j<n\). Every other entry is \(-H\). The least prices are all 1. Assign buyer \(j\ge1\) her own good and buyer 0 outside. Each nonempty set is demanded by all its owners and by the predecessor of its least index, proving (3). For \(0<\delta<1\), raise buyer 0's good-1 value by \(\delta\), and for \(1\le j<n\) lower the own value by \(\delta\) and raise the next value by \(\delta\). At \(q_j=1+(2j-1)\delta\) the same allocation and ties certify the new minimum. The last price changes by \((2n-1)\delta\). These two matrices can also be \(B(0),B(\mathbf1)\) of a single normalized market, by setting \(\eta_{ij}=B_{ij}(0)-B_{ij}(\mathbf1)\). Thus the same example attains the bound for the frozen map in the specified price coordinates.

## The contraction and exact recovery

Write \(E=\max_{ij}|\eta_{ij}|\). By (2), \(F\) is a contraction with constant at most \((2n-1)E\le1/2\) under (1). At every fixed point \(q=F(q)\) the frozen utilities \(B_{ij}(q)-q_j\) equal the original normalized utilities. The frozen flow clears in the original market and (3) transfers exactly. The fixed point is therefore the least original price. Banach's theorem gives its existence and uniqueness under (1).

For use also in the extension below, \(F\) always has a fixed point in a known box. Take

\[
 R=\max\left(1,\ \max_{ij}\frac{\max(0,b_{ij})}{\min(1,s_{ij})}\right).
\]

For \(0\le t\le R\mathbf1\), each \(B_{ij}(t)\le R\). For \(\eta_{ij}\ge0\) this follows from \(b_{ij}\le R\), and for \(\eta_{ij}<0\) it follows from \(b_{ij}\le s_{ij}R\). By (3) for a singleton, every positively priced good in \(F(t)\) is demanded by some buyer, even if its capacity is zero. That buyer weakly prefers it to the outside option, so \(F\) maps the box into itself. Its continuity follows from (2), and Brouwer gives existence on the box even for arbitrary positive slopes. The least-price certificate at a fixed point gives uniqueness. This identifies the general search problem with finding the fixed point of an explicit continuous map.

**Exact recovery from a small residual.** At a rational trial point \(t\) let \(q=F(t)\). Compute all frozen demand sets \(D_i\) at \(q\), including outside ties, and a clearing flow. Write \(U_{ij}(z)=b_{ij}-s_{ij}z_j,\ U_{i0}(z)=0\). Solve

\[
\begin{aligned}
 \min_{z\ge0,\ v\ge0}\quad &v\\
 z_j&=0 &&(q_j=0),\\
 U_{ij}(z)+v&\ge U_{ik}(z) &&(j\in D_i,\ k\in\{0,\ldots,n\}).
\end{aligned} \tag{4}
\]

Choose a common multiple \(D\) of all denominators of \(b,s\), for example their product. Let \(H\ge1\) be an integer bounding all coefficients and right-hand sides in the full template (4) after multiplication by \(D\). Set

\[
 Q=(n+1)!\,H^{\,n+1},\qquad \tau=\frac1{4(1+E)Q}.
\]

These constants have polynomial encoding length and are computed before querying \(F\). It suffices that \(|q_j-t_j|\le\tau\) for every column with a nonzero \(\eta_{ij}\). Changing from frozen to true utilities at \(q\) changes each entry by at most \(E\tau\). Thus \(z=q,\ v=2E\tau\) is feasible in (4). The polyhedron is pointed because all its variables are nonnegative. The optimum is attained at a vertex and any positive optimal \(v\) would be at least \(1/Q\) by Cramer's rule. Since \(2E\tau<1/Q\), the optimum is zero.

At an exact optimum \(z\), every frozen demand edge remains an original demand edge. All slack goods in the stored flow had \(q_j=0\) and are still at zero, so this flow clears at \(z\). Every nonempty positive-price set at \(z\) was positive at \(q\), and its old neighboring buyers are still neighbors. This transfers (3), certifying that \(z\) is the least original price. Keeping every old tie in (4) is what transfers the strict inequality. Return \(r_j+z_j/\beta_j\) and the stored flow.

**Binary running time for (1).** Start at \(t^0=0\), evaluate \(F\) exactly by LP, and round each output to the nearest multiple of a fixed dyadic mesh \(h\le\tau/4\) with \(\log_2(1/h)=O(1+\log(1/\tau))\). For the fixed point \(z^*\), the error after \(k\) steps is at most \(2^{-k}R+h\), since one rounding changes a coordinate by at most \(h/2\). Choose \(k\) so \(2^{-k}R\le\tau/4\). At this point \(\|t^k-F(t^k)\|_\infty\le(1+1/2)\|t^k-z^*\|_\infty<\tau\). All trial points have polynomial-bit dyadic coordinates by the error bound, all frozen LPs have polynomial size, and \(O(1+\log R+\log(1/\tau))\) exact evaluations suffice.

## A wider region by a weighted Euclidean norm

**Theorem.** Suppose rational bounds \(e_j\ge\max_i|\eta_{ij}|\) obey

\[
 2\sum_j\frac{e_j}{1+e_j}\ \le\ 1 . \tag{5}
\]

The exact minimum-price oracle runs in polynomial bit time, including on the boundary of (5). For supplied rational \(e_j\), the LP above recognizes whether suitable factors exist. In particular \(e_j=1/(2n-1)\) is admissible uniformly.

Let \(J=\{j:e_j>0\}\). If \(J\) is empty, a single TU computation suffices. Otherwise the frozen intercepts depend only on \(t_J\). Evaluate \(f(t_J)=F(t)_J\) with the remaining trial coordinates zero. A fixed point of \(f\) exists by the box argument. The full \(q=F(t)\) can be used in (4) as soon as the residual on \(J\) is small.

By (2), with coordinatewise absolute values,

\[
 |f(x)-f(y)|\le K|x-y|,\qquad
 K_{jj}=e_j,\quad K_{jk}=2e_k\quad(j\ne k,\ j,k\in J).
\]

For \(w_j=1/(1+e_j)\), (5) gives \(Kw\le w\), so \(K\) has spectral radius at most one by the induced \(w\)-weighted sup norm. For \(W=\operatorname{diag}(e_j:j\in J)\), the matrix \(W^{1/2}KW^{-1/2}\) is symmetric. Its Euclidean operator norm is its spectral radius, at most one by similarity. Hence \(f\) is nonexpansive for \(\|v\|_W^2=v^\top Wv\). Only rational entries of \(W\) are needed by the algorithm.

At a rational ellipsoid center \(x\), evaluate \(g=x-f(x)\). For a fixed point \(x^*\), expanding \(\|f(x)-x^*\|_W^2\le\|x-x^*\|_W^2\) gives

\[
 (Wg)^\top(x-x^*)\ \ge\ \tfrac12\|g\|_W^2 .
\]

If \(\|g\|_\infty\le\tau\), finish by (4). Otherwise use the central cut \((Wg)^\top(z-x)\le0\). It contains a Euclidean ball around \(x^*\) of rational radius

\[
 \rho=\frac{\tau}{2}\,\frac{\min_{j\in J}e_j}{\max_{j\in J}e_j}.
\]

Indeed its center-to-plane distance is at least \(\|g\|_W^2/(2\|Wg\|_2)\ge \|g\|_\infty\sqrt{\min e_j/\max e_j}/2\). The initial ball of radius \(|J|(R+1)\) about the origin contains this entire ball. The rational central-cut ellipsoid method reduces volume below that of a radius-\(\rho\) ball in polynomially many cuts in \(|J|\) and \(\log(|J|(R+1)/\rho)\). Every unsuccessful cut preserves that ball, so some query must meet the stopping test. In dimension one, interval bisection gives the same guarantee. Rational ellipsoid centers and cut coefficients have polynomial encoding length, since \(f\) is computed by rational LP on those centers. The bound uses the binary encoding of \(e_j\) and permits equality in (5). [Grötschel, Lovász and Schrijver, central-cut ellipsoid method, §3.2](https://www.zib.de/userpage/groetschel/pubnew/paper/groetschellovaszschrijver1988.pdf)

For a given row scaling \(\alpha\), put \(l_j=\min_i d_{ij}/\alpha_i,\ h_j=\max_i d_{ij}/\alpha_i\). Choosing \(\beta_j=(h_j+l_j)/2\) gives \(2e_j/(1+e_j)=1-l_j/h_j\), using the actual maximum error in the column. Thus \(\sum_j(1-l_j/h_j)\le1\) is a directly checkable sufficient condition. If all columns except one factor exactly, choose their common row scaling and use this midpoint for the exceptional column. Its contribution is strictly less than one, irrespective of its slope ratio. Such an exceptional column can be found by trying each deletion and testing exact factorization on the remainder. A4b's elimination of a good extends this base case to any fixed number of unrestricted additional columns. [A4b one-good elimination](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)
