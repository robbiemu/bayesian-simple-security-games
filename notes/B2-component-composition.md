# B2. Composing viable-choice components under one defender budget

**Theorem.** For rational explicitly enumerated Bayesian simple security games, an exact Bayes–Nash equilibrium can be found in polynomial bit time for each fixed maximum number \(K\) of positive-prior types in a connected component of the viable-choice graph defined below. The number of components, the number of targets, the bit lengths of the rational priors, and the number of distinct payoff slopes may grow. All components share one defender budget. The result includes zero attacker slopes and zero defender gains. This is a structural subclass of the stated open problem. [Conitzer, problem statement](https://arxiv.org/pdf/2610.08796)

## The graph and the common threshold

Remove the zero-prior types temporarily. Write \(u_{it}(x_t)=a_{it}-d_{it}x_t\), with \(d_{it}\ge0\), and let \(m_i=\max_s(a_{is}-d_{is})\). Join type \(i\) to target \(t\) exactly when \(a_{it}\ge m_i\). This tests whether the target can maximize that row anywhere in the full box. An omitted target always gives utility strictly below \(m_i\), while a maximizer at full coverage always gives at least \(m_i\). For a retained target, setting its coverage to zero and all others to one witnesses viability. Thus every row has a retained neighbor, and *every* local best response on its retained neighbors is a global best response for any completion of the coverage vector. Keep isolated targets as components.

In a component \(C\) with targets \(T_C\), a certificate at threshold \(\lambda\ge0\) consists of coverage \(x\in[0,1]^{T_C}\) and row masses \(q_{it}\) totaling \(p_i\) on the maximizing neighbors of each type. The component retains its original, unnormalized priors. Write \(y_t=\sum_i q_{it}\), \(s_t=\beta_t y_t\). Impose \(s_t\le\lambda\) when \(x_t=0\), \(s_t=\lambda\) when \(0<x_t<1\), and \(s_t\ge\lambda\) when \(x_t=1\). The local budget is \(b=\sum_{t\in T_C}x_t\). For a common \(\lambda\), concatenating local certificates gives a global equilibrium precisely when the local budgets sum to \(r\). Conversely a global equilibrium supplies such certificates, since an optimal linear allocation over the capped simplex has a common marginal-reward threshold. One may restrict the search to \([0,B]\), where \(B=1+\max_t\beta_t\), since every score is at most \(\max_t\beta_t\).

## Budget intervals at a common threshold

For this section assume all retained \(d_{it}>0\) and all \(\beta_t>0\). The threshold ordering appears in the prior collection. Applying it to local certificates gives the budget intervals used for composition. [Prior research collection, physical p. 11](../sources/prior-collection.md#part-ii)

**Order across thresholds.** For certificates \((x^1,q^1)\) and \((x^2,q^2)\) at \(\lambda_1<\lambda_2\) in one component, \(x^1_t\ge x^2_t\) at every target. Indeed, suppose \(S=\{t:x^1_t<x^2_t\}\) is nonempty. A row sending mass into \(S\) at \(x^2\) sees the utility of one such maximizer strictly rise at \(x^1\), while the utilities of all its neighbors outside \(S\) weakly fall. Its entire supply must go to \(S\) at \(x^1\). Consequently \(\sum_{t\in S} y^1_t\ge\sum_{t\in S}y^2_t\). On \(S\) we have \(x^1_t<1\) and \(x^2_t>0\), giving

\[
\sum_{t\in S} y^1_t\ \le\ \lambda_1\sum_{t\in S}1/\beta_t
\ <\ \lambda_2\sum_{t\in S}1/\beta_t\ \le\ \sum_{t\in S}y^2_t .
\]

This contradiction also works at \(\lambda_1=0\).

**A necessary condition for different coverages at one threshold.** At equal positive thresholds the same inequalities, now weak throughout, must all be equalities. Given two distinct coverage vectors at this threshold, orient the pair so that \(S=\{t:x^1_t<x^2_t\}\ne\varnothing\). Let \(A\) consist of the rows sending any mass to \(S\) at \(x^2\). Then
\[
y^2(S)\le\sum_{i\in A}p_i\le y^1(S)\le\lambda\sum_{t\in S}1/\beta_t\le y^2(S).
\]
In particular \(\lambda=(\sum_{i\in A}p_i)/(\sum_{t\in S}1/\beta_t)\). This arithmetic restriction on thresholds with multiple coverage vectors is independent of the payoff slopes. With uniform \(p_i=1/k\) and common \(\beta_t=\beta\), there are at most \(k|T|\) distinct positive candidates \(\beta h/(k j)\) for such thresholds globally. It gives a necessary condition and supplies no strategy for a specified budget by itself.

**Interval at a fixed threshold.** If \(b_-<b_+\) are attainable at \(\lambda\), take any \(b\) strictly between them. A local equilibrium with that budget exists, even for a nonintegral \(b\). To see this, use the coverage polytope \(X_b=\{0\le x\le1:\sum x=b\}\) and the product of row simplexes of masses \(p_i\). Make these the two players' strategy polytopes, with payoffs \(\sum_t x_ts_t\) and \(\sum_{it}q_{it}u_{it}(x_t)\). The payoffs are affine in each strategy separately. A mixed Nash equilibrium of the finite game on both vertex sets therefore gives mutual best responses at their means. The defender's linear best response has a threshold \(\mu\in[0,B]\). If \(\mu<\lambda\), comparison with the certificate at \(b_+\) gives \(b\ge b_+\). If \(\mu>\lambda\), comparison with the one at \(b_-\) gives \(b\le b_-\). Hence \(\mu=\lambda\). The endpoints of any nonempty budget slice are attained, since the certificate conditions at fixed \(\lambda\) define a closed subset of the product of compact strategy polytopes. The interval proof only uses existence of the intermediate equilibrium. The algorithm below recovers it by rational LP.

## Enumerating the local budget and threshold pairs

First consider a component with at least one type. At \(\lambda>0\), a covered target receives positive mass. If \(v_i\) is the type's attained maximum, the inequalities \(u_{it}(x_t)\le v_i\) on its neighbors and a tight incoming edge whenever \(x_t>0\) imply

\[
x_t=L_t(v)=\max\bigl(\{0\}\cup\{g_{it}(v):i\sim t\}\bigr),\qquad
g_{it}(v)=(a_{it}-v_i)/d_{it}.
\]

In the \(k_C\)-dimensional space of row values, enumerate all relatively open faces of the arrangement \(g_{it}=0,\ g_{it}=1,\ g_{it}=g_{jt}\) for incident edges at each target, using distinct row pairs for the last family. Skip faces where some \(L_t>1\). On each remaining face \(F\), the affine expression for each \(L_t\), the coverage classes \(Z,I,O\) (zero, interior, full), and the tight graph \(D_F=\{it:g_{it}=L_t\}\) are fixed. The face enumeration includes lower-dimensional ties. [(A1), Section 3](A1-threshold-transport.md)

Build two independent rational polytopes for each face.

- On the coverage side, take the sign constraints of \(F\) with weak inequalities in place of strict signs, impose \(x_t=L_t(v)\) using its chosen affine expression, and impose \(0\le x_t\le1\). Bound each \(v_i\) by the minimum full-coverage utility and maximum uncovered utility among its neighbors. These bounds contain all attained row values.
- On the flow side, take \(0\le\lambda\le B\), the nonnegative row flows with sums \(p_i\) supported on \(D_F\), and the threshold inequalities for the classes \(Z,I,O\) on the face. These constraints are linear and contain no \(v\) or \(x\).

Discard the pattern if either polytope is empty. The projection onto \((\lambda,b)\) is exactly the product of two closed intervals \(J_F\times I_F\). Compute their four extrema by LP. Every point of this rectangle certifies a valid pair. On the closure of \(F\), each chosen envelope formula remains correct and every previously tight edge remains tight. A formerly interior coordinate that reaches zero or one still meets the threshold condition because its flow-side constraint is equality. Every row sends positive total mass, so the tight edges carrying that mass certify its stated maximum. Conversely every positive-threshold certificate occurs in the rectangle from the relatively open face containing its actual \(v\). The ordering lemma further implies that each rectangle has a singleton threshold interval or a singleton budget interval. Otherwise a smaller budget at a smaller threshold and a larger budget at a larger threshold would contradict the lemma.

At threshold zero all positive-flow targets must be full. Every attacked target then gives its row at most \(m_i\), and every row's maximum is at least \(m_i\). Thus necessarily \(v_i=m_i\), and \(x_t\ge L_t(m)\). Conversely each full-coverage maximizer for row \(i\) satisfies \(L_t(m)=1\) by strictness of its slope. Any \(x\in[L(m),\mathbf1]\) componentwise permits every row to send all its mass to such a maximizer. Include the closed rectangle

\[
\{0\}\times [\textstyle\sum_{t\in T_C}L_t(m),\ |T_C|].
\]

For an isolated target the entire relation consists of \([0,B]\times\{0\}\) and \(\{0\}\times[0,1]\). These rules give exactly the full local relation on \([0,B]\), with an LP witness or an explicit construction attached to each rectangle.

## Sweeping the common threshold and recovering strategies

Collect 0, \(B\), and all rational endpoints of the local threshold intervals. Inspect each distinct endpoint and one rational midpoint between each consecutive pair. Inside an open gap, every component has the same active rectangles as it does at the midpoint. At an inspected threshold discard the candidate if any component has no active rectangle. Otherwise take the smallest lower budget endpoint \(l_C\) and largest upper budget endpoint \(u_C\) among its active rectangles. The interval lemma shows that every number in \([l_C,u_C]\) is attainable, including when its two endpoints use different rectangles. The exact global test is

\[
\sum_C l_C\le r\le\sum_C u_C .
\]

For a passing candidate start with \(b_C=l_C\) and distribute the residual \(r-\sum_C l_C\) successively up to \(u_C-l_C\) in each component. Choose an active rectangle containing the selected \(b_C\) in each component. Solve its two LP feasibility problems with the chosen \(b_C\) and \(\lambda\) fixed, or use its explicit zero-threshold or isolated-target construction. Concatenating these certificates solves the game. A passing candidate exists by equilibrium existence in the global game and constancy of the active sets on each open gap.

Let \(H_C=\sum_{t\in T_C}(2\deg(t)+\binom{\deg(t)}2)\). The number of arrangement faces, including the work to enumerate their prefixes, is bounded by \((1+H_C)^{O(k_C+1)}\) in a component with positive-prior types. Vertex denominators, interval endpoints and decoded solutions have polynomial bit length by rational LP bounds. A sum of one endpoint per component has bit length at most the sum of their bit lengths plus a logarithmic term. If a component total prior \(P_C=\sum_{i\in C}p_i\) is materialized, it lies in \([0,1]\) and its denominator divides the product of the input prior denominators, hence has at most their total binary length. The row LPs need no division by \(P_C\). In the chosen component order, a partially filled budget is exactly \(r-\sum_{D<C}u_D-\sum_{D>C}l_D\), and all other budgets are endpoints from the rectangles. This gives a polynomial bit bound and recovers the original resource sum exactly. In a direct implementation with \(M\) local rectangles, \(O(M^2)\) endpoint and interval comparisons suffice for the sweep, in addition to polynomial-size rational arithmetic. An event sweep reduces the sweep cost to \(O(M\log(M+1))\) exact comparisons and arithmetic operations. Maintain the multisets of active lower and upper budget endpoints in each component, the two global sums of their extrema over nonempty components, and the number of empty components. At each threshold endpoint insert all starting rectangles, test that endpoint, then remove all ending rectangles and test the following open gap at its midpoint if it exists. Each insertion or removal updates one component's contribution in logarithmic time, including zero-width intervals. After the first passing test a single scan retrieves the active rectangles for reconstruction. Reduced rational sums have the same polynomial bit bounds as in the direct sweep.

Thus the algorithm is polynomial for fixed \(K=\max_C k_C\). The enumeration sums over components. It never forms the product of their face counts.

## Preserving the component bound under weak inputs

If some \(d_{it}\) or \(\beta_t\) is zero, use the perturbation and exact certificate repair of A1. Let \(\varepsilon_0\) be its determinant-bound perturbation. Among omitted edges compute the smallest positive gap \(\gamma=\min_{it\text{ omitted}}(m_i-a_{it})\). Use \(\varepsilon=\min(\varepsilon_0,\gamma/2)\) when that set is nonempty, and \(\varepsilon=\varepsilon_0\) otherwise. Replace only zero coefficients \(d_{it},\beta_t\) by \(\varepsilon\). For each row, its perturbed full-coverage maximum lies in \([m_i-\varepsilon,m_i]\). Every retained edge still meets the viability test, and every omitted edge still fails it. The positive-coefficient solver therefore operates on exactly the original components.

Record the positive-flow support and the coverage classes of its output. With the original data, optimize A1's linear program minimizing the maximum violation on this support and these classes, using the original global budget. The perturbed strategies are feasible at violation \(\varepsilon\), whereas every positive basic optimum is strictly greater than \(\varepsilon_0\) by the determinant bound. The exact optimum is therefore zero. This single global LP has polynomial size and does not enumerate joint patterns. Dividing row masses by \(p_i\) gives conditional strategies. Give each discarded zero-prior type a maximizing target, and decompose the rational coverage vector into a distribution over \(r\)-target sets if an explicit defender mixture is required. [(A1), Section 4, including the determinant bound and decomposition](A1-threshold-transport.md)

The residual interval and order lemmas above concern the strictly positive game. The repair establishes an exact search algorithm under weak inequalities without needing those lemmas to hold in the original weak game.
