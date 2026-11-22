# A3. Arbitrary common target offsets admit exact polynomial-time search

**Theorem.** Suppose the attacker utilities have the form
\[
u_{it}(x_t)=a_{it}-d_{it}x_t=A_i-d_{it}(x_t-c_t).
\]
The row constants \(A_i\) and target constants \(c_t\) are rational. The targets may have offsets below zero, at either boundary, inside the unit interval, or above one in the same instance. There is an exact polynomial-bit-time equilibrium algorithm for arbitrary positive slopes \(d_{it}\), arbitrary positive defender gains \(\beta_t\), and binary rational type probabilities. The factorization can be recognized and recovered in polynomial time. The final section extends the result to nonnegative slopes and gains on the same factorized class. The result concerns a subclass of [Conitzer’s open problem](https://arxiv.org/pdf/2610.08796).

Remove zero-prior rows until conditional strategies are recovered. Let \(q_{it}\) be the prior-weighted attack mass with row sum \(p_i>0\), normalized to total mass one. Write \(y_t=\sum_i q_{it}\). At a defender threshold \(\lambda\), a column below full coverage has score \(\beta_t y_t\le\lambda\), and a column with positive coverage has score \(\beta_t y_t\ge\lambda\). A *certificate* in this note satisfies both conditions and all row best responses. Unless specified, its coverage budget is free. Adding \(\sum x_t=r\) certifies an equilibrium.

## Selecting the sign from the given budget

First test \(\lambda=0\). Set \(m_i=\max_t(a_{it}-d_{it})\) and \(L_t=\max(0,\max_i(a_{it}-m_i)/d_{it})\). A zero-threshold equilibrium exists exactly when \(\sum_t L_t\le r\). In that event augment \(L\) coordinatewise up to total \(r\) within the box and give each row any full-coverage maximizer. Every chosen maximizer is full by construction. Conversely, every attacked target at threshold zero is full, so each row obtains \(m_i\). [A1, §2](A1-threshold-transport.md)

For \(\lambda>0\), every positively covered target receives attack mass. Define the baseline \(b_t=\min(1,\max(0,c_t))\) and \(R_0=\sum_t b_t\). All types rank every negative signed gap \(x_t-c_t<0\) ahead of every nonnegative gap, and every zero gap ahead of every positive gap. This gives two coordinatewise comparisons.

- If any gap is negative, every positive-coverage target has a negative gap. All \(c_t\le0\) targets have zero coverage and zero flow. Every target with \(c_t>0\) has a strictly negative gap, whether covered or uncovered. Then \(x\le b\) coordinatewise.
- If no gap is negative, the box implies \(x\ge b\). If \(x_t>b_t\) for even one target, that target has a positive gap, positive coverage and positive attack mass. Every target must then have a strictly positive gap. In particular, \(c_t<1\) for every target.

For \(r<R_0\) there is a negative gap, so use the first branch. For \(r>R_0\) use the strictly positive branch. After the zero-threshold test failed, existence of equilibrium guarantees its necessary condition \(c_t<1\) for all \(t\). For \(r=R_0\) either componentwise comparison forces \(x=b\). At this fixed rational coverage, restrict each row’s flow to its maximizers and solve the linear threshold inequalities above for \(q,\lambda\ge0\). This handles the entire equality case, including offsets equal to zero or one. [Fixed-coverage LP](A1-threshold-transport.md)

## A fixed positive threshold

Write \(D\) for the live targets and \(h_t=\lambda/\beta_t\) for \(t\in D\). For either strict branch, type \(i\) maximizes \(w_{it}-z_t\) over \(D\), where \(z_t\) strictly increases with \(x_t\). The bounds in the table are inclusive when finite. An infinite endpoint means the variable ranges over finite real numbers on that side.

| Branch | Live targets \(D\) | \(w_{it}\) | \(z_t\) | Lower endpoint \(l_t\) | Upper endpoint \(u_t\) |
| --- | --- | --- | --- | --- | --- |
| Negative | \(c_t>0\) | \(\log d_{it}\) | \(-\log(c_t-x_t)\) | \(-\log c_t\) | \(-\log(c_t-1)\) if \(c_t>1\), else \(+\infty\) |
| Positive | All targets, \(c_t<1\) | \(-\log d_{it}\) | \(\log(x_t-c_t)\) | \(\log(-c_t)\) if \(c_t<0\), else \(-\infty\) | \(\log(1-c_t)\) |

In the negative branch the omitted targets are fixed at zero and receive zero mass. The table follows by taking the log of the positive utility increment in the negative branch, or minus the log of the positive utility loss in the positive branch. Finite lower and upper endpoints correspond exactly to \(x_t=0\) and \(x_t=1\), respectively. A missing endpoint precludes the associated flow slack.

Maximize the following transportation objective with flow variables \(q_{it},f_t,g_t\ge0\).
\[
\sum_i\sum_{t\in D} w_{it}q_{it}+\sum_{t:l_t\text{ finite}}l_tf_t
                 -\sum_{t:u_t\text{ finite}}u_tg_t,
\qquad
\sum_{t\in D}q_{it}=p_i,\quad y_t+f_t-g_t=h_t .
\]
Omit \(f_t\) at an infinite lower endpoint and \(g_t\) at an infinite upper endpoint. These are ordinary flow equations with a dummy node sending \(f_t\) to a target and receiving \(g_t\) from it, with net supply \(\sum_{t\in D}h_t-1\).

The real dual minimizes \(\sum_i p_i v_i+\sum_{t\in D} h_t z_t\) subject to \(v_i+z_t\ge w_{it}\) and the finite bounds on \(z_t\). Finite feasible dual points always exist. For a feasible transport instance, both optima are attained. Complementarity gives tight row inequalities on positive \(q_{it}\), \(z_t=l_t\) on positive deficit \(f_t\), and \(z_t=u_t\) on positive excess \(g_t\). Inverting finite optimal prices therefore gives a strict branch certificate. Conversely, any strict branch certificate gives an optimal pair by its log prices and row maxima, with \(f_t=(h_t-y_t)_+\) and \(g_t=(y_t-h_t)_+\). A required slack always has the corresponding finite endpoint. Any primal optimum is complementary to *every* dual optimum, since the duality gap decomposes into nonnegative products. Thus one optimal transport flow suffices for all coverages in this branch at this threshold.

The infeasible cases give explicit search directions. In the negative branch every deficit is allowed. If any excess is allowed the columns can accommodate all row supply. Otherwise feasibility is exactly \(1\le\sum_{t\in D}h_t\). Failure means that the trial \(\lambda\) and all smaller values are too small. In the positive branch every excess is allowed. Columns with \(c_t\ge0\) prohibit deficits, so feasibility is exactly \(\sum_{t:c_t\ge0}h_t\le1\). Failure means the trial \(\lambda\) and all greater values are too large. For sufficiency in both cases, choose nonnegative column totals obeying these individual lower or upper bounds and summing to one, then use \(q_{it}=p_i y_t\). These feasibility statements concern the transport polyhedron before optimization.

## Rational cost and coverage computations

Every arc cost is a signed logarithm of a positive rational, including the costs at finite bounds. Let \(V\) count all network vertices and choose \(B\) so that numerator and denominator of each such rational are at most \(2^B\). Along a simple residual cycle the exact signed cost is \(\log(P/Q)\) with \(P,Q\le 2^{VB}\). If it is nonzero, its absolute value is at least \(2^{-VB}\), by \(\log(s/t)\ge(s-t)/s\) for \(s\ge t>0\). Approximate each arc cost to absolute error less than \(2^{-VB}/(2V)\), taking reverse costs by negation. Every nonzero exact cycle cost retains its sign. Some exact zero cycles may receive a nonzero cost. An optimum of the approximate rational objective still maximizes the exact objective. An exact improvement would give a positive simple residual cycle at that flow, by decomposing the flow difference into cycles, and that cycle would improve the approximate objective as well.

The rational approximate transport has a finite optimum. The only directed cycles in its forward network run from the dummy node to a column and back, and their exact cost is strictly negative since finite \(l_t<u_t\). Thus approximation cannot create an improving unbounded circulation. Standard rational LP returns an optimal flow of polynomial bit length. For explicit log approximation, normalize a positive rational by a power of two to \([1,2)\) and evaluate \(\log v=2\sum_{j\ge0}((v-1)/(v+1))^{2j+1}/(2j+1)\) for the normalized argument and for \(v=2\). The ratio inside the powers is at most \(1/3\), the exponent of two has size \(O(B)\), and a polynomial number of terms gives the stated error with rational arithmetic.

Take the resulting exact-optimal flow and extend it by zero on omitted targets. Recover coverage directly in original variables. In a rational LP require
\[
0\le x_t\le1,\qquad M_i\ge a_{it}-d_{it}x_t\quad(\text{all }i,t),\qquad
M_i=a_{it}-d_{it}x_t\quad(q_{it}>0).
\]
Fix \(x_t=0\) when \(\beta_t y_t<\lambda\) and \(x_t=1\) when \(\beta_t y_t>\lambda\). In the negative branch fix omitted coordinates to zero and impose \(x_t\le c_t\) on live columns. In the positive branch impose \(x_t\ge c_t\) everywhere. This LP is nonempty by the existence of an optimal finite dual point. It contains every strict branch coverage, because log prices from each such equilibrium are complementary to the chosen flow. Its weak bounds may admit a zero-gap limit. Every feasible point still satisfies the actual game certificate with this same flow. In particular there are no spurious budget solutions. No logarithm is exponentiated in the algorithm.

Minimize and maximize \(\sum_t x_t\) in this bounded coverage polytope to get \(b_-,b_+\). If \(b_-\le r\le b_+\), add \(\sum_t x_t=r\) and solve. Otherwise a smaller threshold is needed when \(r>b_+\), and a larger one when \(r<b_-\). To see this, recall the cross-threshold order. Any certificate at \(\lambda_1<\lambda_2\) has \(x^1\ge x^2\). If \(S=\{t:x^1_t<x^2_t\}\) were nonempty, every row sending mass into \(S\) at \(x^2\) would send its entire mass into \(S\) at \(x^1\), by strict positive slopes. But on \(S\), \(x^1_t<1\) and \(x^2_t>0\), which gives \(y^1(S)\le\lambda_1\sum_{S}1/\beta_t<\lambda_2\sum_{S}1/\beta_t\le y^2(S)\). At equal thresholds all budget-\(r\) certificates belong to the selected strict branch by the sign argument above. The recovered interval therefore suffices even when the LP includes a boundary certificate. [B2, cross-threshold order](B2-component-composition.md)

## Finite threshold search and recognition

Put \(H=1+\max_t\beta_t\). An equilibrium has a threshold in \([0,H]\), including at extreme budgets. There is a computable polynomial-bit denominator bound \(D_*\) for at least one such threshold at the requested budget. Indeed, fix the support and coverage classes of an existing equilibrium. Form the closed rational pattern LP in \(x,M,q,\lambda\), with the row best-response inequalities and support equalities, zero flow off that support, nonnegative row masses with sums \(p_i\), original budget, \(0\le\lambda\le H\), and the appropriate threshold inequalities or equalities from its classes. Zero and full coordinates are fixed, and former interior coordinates may reach either endpoint while retaining threshold equality. Bound the row values by the minimum full-coverage and maximum uncovered utility in each row. Every feasible point certifies an equilibrium, and a vertex exists. A uniform bound follows by letting \(N\) be the number of variables and \(C\) an upper bound for absolute values of cleared integer coefficients and right-hand sides in any possible pattern row. One can take \(D_*=(N\max(1,C))^N\). Clearing with the product of input denominators has polynomial binary length. The patterns are used only for this bound. [A1, rational certificate bounds](A1-threshold-transport.md)

After zero and the baseline have been treated, bisect \([0,H]\) by the rational positive-threshold oracle. On a failure keep the indicated side, which retains every equilibrium threshold in the search interval at the requested budget. Stop on success or once the interval has width below \(1/(2D_*^2)\). It then contains at most one rational of denominator at most \(D_*\), and existence guarantees that this rational is a solution. Recover it among the continued-fraction convergents of the midpoint (its error is less than \(1/(2D_*^2)\)) and call the oracle at that rational. This takes polynomially many polynomial-bit LP solves. Divide by \(p_i\) to report conditional attacks and give discarded zero-prior rows any maximizer. If an explicit defender mixture is required, decompose the rational marginal vector by the unit-interval construction. [A1, §4](A1-threshold-transport.md)

Recognition only requires solving the rational linear equations \(A_i+d_{it}c_t=a_{it}\) in \(A_i,c_t\). A consistent system has a polynomial-bit rational solution by elimination, including when its constants are nonunique. The algorithm works with any such solution.

## Extension to nonnegative slopes and gains

For a factorized weak instance, choose a rational representation as above. Replace each zero \(d_{it}\) by \(\varepsilon\), set \(a'_{it}=A_i+d'_{it}c_t\), and replace each zero \(\beta_t\) by \(\varepsilon\). The altered instance belongs to the proved positive class. For any \(x\in[0,1]^n\), the original and perturbed utilities differ coordinatewise by at most \(K\varepsilon\), for \(K=1+\max_t|c_t|\). Scores differ by at most \(\varepsilon\).

Use the rational minimum-violation LP on the returned attack support and returned coverage classes, with original data and original budget. Its variable \(0\le\eta\le1\) relaxes row best-response inequalities, support equalities in the missing direction, and threshold inequalities, each by \(\eta\). At the perturbed strategies choose row values equal to the original row maxima. A supported edge then has row gap at most \(2K\varepsilon\). Choose the perturbed defender threshold bounded by \(1+\max_t\beta_t\) for \(\varepsilon\le1\), for example the largest perturbed score below full coverage, or zero if none. All score violations are at most \(\varepsilon\). The original box, budget, support and class constraints hold exactly.

By the same cleared-coefficient determinant bound, including \(\eta\) as one additional variable, every strictly positive vertex optimum is at least \(1/D'\) for a computable polynomial-bit integer \(D'\) depending only on the original rational LP data. Take \(\varepsilon=1/(4KD')\). The perturbed certificate gives a feasible violation at most \(1/(2D')\), so the original optimum is zero. An optimal basic solution is an exact original equilibrium. This change to both the slope and intercept preserves the shared-offset representation throughout the positive solve. [Original pattern repair LP](A1-threshold-transport.md)
