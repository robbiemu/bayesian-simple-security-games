# B3d. Composing components that share targets

**Theorem.** Fix integers \(s,K\ge0\). Form the bipartite graph of positive-prior attacker types and viable targets. If deleting at most \(s\) target vertices leaves at most \(K\) types in each connected component, an exact Bayes–Nash equilibrium can be computed in polynomial bit time. The separating targets can be found as part of the algorithm. The components may contain arbitrarily many private targets, and the number of components and the number of neighbors of a separating target may grow. The rational model allows arbitrary positive priors and weak payoff inequalities. The polynomial bound is for the algorithm below. [Conitzer, problem statement](https://arxiv.org/pdf/2610.08796)

For a single shared target, fixing its coverage and the defender threshold makes the feasible pairs *(private budget, attack mass on the shared target)* a Cartesian product of two closed intervals whenever feasible. For several shared targets the second factor is a convex polytope. The proof lets the algorithm retain the full correlation among the masses on different shared targets in one linear program.

## Local certificates

Write \(p_i\) for the type prior, \(u_{it}(x_t)=a_{it}-d_{it}x_t\) for attacker utility, and \(\beta_t\) for the defender gain from covering an attacked target. First assume \(p_i,d_{it},\beta_t>0\). Put \(m_i=\max_t(a_{it}-d_{it})\). An edge \(it\) is viable exactly when \(a_{it}\ge m_i\). An omitted choice always pays strictly less than \(m_i\), and a full-coverage maximizing choice always pays at least \(m_i\). Thus row best responses can be computed using viable edges alone. [B2, viable-choice components](B2-component-composition.md#the-graph-and-the-common-threshold)

Let \(H\) be a separating set of targets, \(|H|\le s\). In a component \(C\) of the graph after deletion let \(R_C\) and \(U_C\) be its rows and private targets. Include isolated vertices. Fix shared coverages \(\alpha\in[0,1]^H\) and a threshold \(0\le\lambda\le M=1+\max_t\beta_t\). A local certificate consists of private coverages \(x\in[0,1]^{U_C}\) and nonnegative flows \(q_{it}\) summing to \(p_i\) in each row. Positive flows use maximizing neighbors in \(U_C\cup H\), evaluated at \((x,\alpha)\). For each private target write \(y_t=\sum_{i\in R_C}q_{it}\). Require

\[
 \beta_t y_t\le\lambda\quad(x_t=0),\qquad
 \beta_t y_t=\lambda\quad(0<x_t<1),\qquad
 \beta_t y_t\ge\lambda\quad(x_t=1).
\tag{1}
\]

Record the private budget \(b=\sum_{t\in U_C}x_t\) and shared masses \(w_h=\sum_{i\in R_C}q_{ih}\), with absent edges contributing zero. The local certificates concatenate into a global certificate at this threshold exactly when \(\sum_C b_C+\sum_h\alpha_h=r\) and (1) holds on each shared target with coverage \(\alpha_h\) and total inflow \(\sum_C w_{Ch}\). These are the optimality conditions for the defender's linear objective on the capped simplex. Every equilibrium admits a threshold in \([0,M]\), including at \(r=0\) and \(r=|T|\). [A1, threshold and transport conditions](A1-threshold-transport.md#1-fixed-coverage-gives-an-exact-flow-test)

## Why the budget and shared masses separate

**Switching lemma.** For two local certificates \((x^1,q^1)\), \((x^2,q^2)\) at the same \((\alpha,\lambda)\), there is a local certificate at \(x^1\) that preserves all the shared-target flows of \(q^2\), even row by row.

Let \(S=\{t:x^1_t<x^2_t\}\), \(T'=\{t:x^1_t>x^2_t\}\), and put all remaining targets, including \(H\), in \(E\). A row sending any mass to \(S\) under \(q^2\) has a maximizer there whose utility strictly increases at \(x^1\). Every neighbor outside \(S\) has weakly lower utility at \(x^1\). Each such row must therefore send its entire supply to \(S\) under \(q^1\). For their set \(A_S\), (1) gives

\[
 y^2(S)\le\sum_{i\in A_S}p_i\le y^1(S)
 \le \lambda\sum_{t\in S}\frac{1}{\beta_t}\le y^2(S).
\tag{2}
\]

Equality throughout forces the same rows to send their entire supplies to \(S\) in both certificates. All other rows send zero there in both. Reverse the certificates and apply the argument to \(T'\). Its exclusive rows \(A_{T'}\) are disjoint from \(A_S\). Every remaining row sends its entire supply to \(E\) in both certificates and hence attains its maximum on \(E\) in both. The utilities on \(E\) agree. Use \(q^1\) on \(A_S\cup A_{T'}\) and \(q^2\) on the remaining rows. All flows now best respond to \(x^1\). Columns in \(S\cup T'\) have their first-certificate flows. Private columns in \(E\) have their second-certificate flows and the same coverage in both. Every shared-target flow comes from \(q^2\). This proves the lemma.

**Budget interval.** With \(\alpha\) fixed, take certificates at \(\lambda_1<\lambda_2\). If \(S=\{t:x^1_t<x^2_t\}\) is nonempty, the first two inequalities of (2) still hold, while (1) implies

\[
 y^1(S)\le\lambda_1\sum_{t\in S}1/\beta_t
 <\lambda_2\sum_{t\in S}1/\beta_t\le y^2(S).
\]

Thus \(x^1\ge x^2\) coordinatewise. Suppose budgets \(b_-<b_+\) occur at \(\lambda\). For any intermediate real \(b\), consider the local game with private defender strategies \(0\le x\le1,\ \sum x=b\) and attacker strategies the product of the row flow simplexes on viable neighbors, including the shared options at fixed \(\alpha\). Use defender payoff \(\sum_{t\in U_C}x_t\beta_ty_t\) and attacker payoff \(\sum_{it}q_{it}u_{it}\). Both are affine in each player's strategy. A Nash equilibrium on the two finite vertex sets yields mutual best responses at the means and a private defender threshold \(\mu\in[0,M]\). If \(\mu<\lambda\), comparing against the certificate at \(b_+\) gives \(b\ge b_+\). If \(\mu>\lambda\), comparison at \(b_-\) gives \(b\le b_-\). Hence \(b\) occurs at \(\lambda\). The certificate conditions at fixed \((\alpha,\lambda)\) are closed in a compact set, so both budget extrema are attained. This extends the private-budget argument with fixed outside options. [B2, threshold order and interval proof](B2-component-composition.md#budget-intervals-at-a-common-threshold)

Fix any one feasible private coverage \(x\). The flows allowed at this \(x\) form a compact polytope given by its maximizing edges, row sums, and (1). The projection onto \(w\) is a compact convex polytope \(W_C(\alpha,\lambda)\). By the switching lemma this is the full attainable shared-mass set at *every* feasible private coverage. Hence the local relation is

\[
 [b_C^-(\alpha,\lambda),b_C^+(\alpha,\lambda)]\ \times\ W_C(\alpha,\lambda).
\tag{3}
\]

When \(|H|=1\), \(W_C\) is a closed interval whose endpoints can be found by two flow LPs at any such \(x\). An isolated private target has zero inflow. It can receive arbitrary coverage at threshold zero and must have zero coverage at a positive threshold. For a component with no private targets the budget is zero and the rows can split among their maximizing shared choices. Both cases satisfy (3).

For example, one row of prior \(p\) tied between two shared targets as its only choices has \(W_C=\{(z,p-z):0\le z\le p\}\). The shared coordinates can therefore be correlated even when their joint vector is independent of the private budget.

## Enumerating local price patterns

The algorithm for positive \(\lambda\) uses the row values \(v_i\). For a private target let

\[
 g_{it}(v)=(a_{it}-v_i)/d_{it},\qquad L_t(v)=\max\bigl(\{0\}\cup\{g_{it}(v):i\sim t\}\bigr).
\]

Every private coverage satisfies \(x_t\ge L_t\). If \(x_t>0\), (1) forces some positive incoming flow, and that edge is tight. Consequently \(x_t=L_t(v)\) for all private targets. Shared options give inequalities \(v_i\ge a_{ih}-d_{ih}\alpha_h\). [A1, coverage envelopes](A1-threshold-transport.md#2-eliminate-coverage-through-type-values)

In \((v,\alpha)\)-space arrange the hyperplanes \(g_{it}=0,1\) and \(g_{it}=g_{jt}\) at each private target, and \(v_i=a_{ih}-d_{ih}\alpha_h\) on each viable shared edge. Include the boundary hyperplanes of the shared unit box and of a rational box containing the row values. For each row, the minimum full-coverage utility minus one and maximum uncovered utility plus one suffice as bounds. Enumerate all relatively open faces in the boxes, including lower-dimensional faces. Retain those satisfying \(L_t\le1\) and all shared inequalities. The signs determine affine formulas for the envelopes, private coverage classes, and the entire tight graph \(D_F\) on each such face \(F\).

1. \(P_F\) is the image of \(\overline F\) under \((v,\alpha)\mapsto(\alpha,\sum_{t\in U_C} L_t(v))\), using the affine formulas on \(F\). It is a compact rational polytope in the shared coverages and private budget. Write \(A_F\) for its projection onto \(\alpha\).
2. \(Q_F\) is the polytope in \((q,\lambda)\) of nonnegative row flows on \(D_F\) with supplies \(p_i\), the private score constraints (1) for the classes of \(F\), and \(0\le\lambda\le M\). Compute its projected threshold interval \(J_F\) by LP. Discard a face with empty \(Q_F\).
3. The projection of the **relatively open** price face \(F\) onto \(\alpha\) is \(\operatorname{relint} A_F\). Indeed a relative-interior point of a polytope is a convex combination with all vertices given positive weight. The image of such a combination is in the relative interior of the image. Conversely a relative-interior point of the image has a representation using every projected vertex of \(\overline F\) with positive weight, allowing duplicates. Lifting the combination gives a point of \(F\).

For every \((\alpha,b)\in P_F\) and \((q,\lambda)\in Q_F\) at \(\lambda>0\), a price preimage gives a local certificate. Chosen envelope formulas and tight edges persist on the closure. A formerly interior private coverage can reach a box boundary, where its flow-side score equality still suffices. Row sums certify the stated values. Conversely each actual certificate occurs on its own relatively open price face. At any fixed feasible \((\alpha,\lambda)\), the union of the slices of \(P_F\) over \(F\) with \(\lambda\in J_F\) is therefore precisely the closed budget interval in (3).

For the shared flows, choose *one* face \(F_*\) with \(\alpha\in\operatorname{relint}A_{F_*}\) and \(\lambda\in J_{F_*}\). There is an actual coverage in this face over \(\alpha\). At that coverage the recorded tight graph and private classes are exact, so its full feasible flow polytope is \(Q_{F_*}\) sliced at \(\lambda\). By (3), its projection onto the shared masses is exactly \(W_C(\alpha,\lambda)\). The use of a relatively open price preimage here accounts for any extra ties or newly relaxed boundary scores present at a face boundary.

## The common parameters and the global LP

All local price calculations have dimension at most \(K+s\). The number of local hyperplanes is polynomial in the input size. Fixed-dimensional hyperplane arrangements have polynomially many relatively open faces, which can be enumerated by incremental sign tests with rational LP. Compute the vertices of each bounded \(\overline F\) by testing independent sets of active constraints. Map the vertices to obtain \(P_F,A_F\), and obtain rational facet inequalities and affine-hull equations by enumerating vertex subsets in their fixed dimensions. These operations include points and lower-dimensional polytopes. [A1, arrangement enumeration](A1-threshold-transport.md#3-exact-search-with-a-fixed-number-of-types)

For \(\alpha\in A_F\), write a facet and affine-hull description of \(P_F\) as linear inequalities, treating each equation as two inequalities. Inequalities with nonzero coefficient of \(b\) give affine lower and upper bounds on \(b\). The slice endpoints are the maximum of the lower bounds and minimum of the upper bounds. Boundedness supplies both for a nonempty slice. Form a common arrangement in \((\alpha,\lambda)\) using

- the facet and affine-hull hyperplanes of each \(A_F\), including point and lower-dimensional projections,
- the endpoints of all \(J_F\), together with \(\lambda=0,M\) and the shared coverage box boundaries,
- the comparisons of every pair of affine budget bounds within each component, across its faces.

Identically equal forms can be tied throughout. This arrangement has polynomially many faces since \(s+1\) is fixed. On a relatively open parameter face with \(\lambda>0\), membership in \(A_F\), \(\operatorname{relint}A_F\) and \(J_F\) is constant. For each component take the minimum lower slice endpoint and the maximum upper slice endpoint over its closed active faces, meaning \(\alpha\in A_F,\ \lambda\in J_F\). Each chosen bound is one affine function throughout the parameter face. These are \(b_C^-\) and \(b_C^+\) by (3). Choose one \(F_*(C)\) meeting the relatively open preimage test in the preceding section. Discard a parameter face if a component has no such witness. Every feasible pair has one in each component.

For this parameter face solve one rational linear program in \(\alpha,\lambda,(b_C),(q^C)\). Require the parameter-face signs, \((q^C,\lambda)\in Q_{F_*(C)}\), the bounds \(b_C^-\le b_C\le b_C^+\), and

\[
 \sum_C b_C+\sum_{h\in H}\alpha_h=r.
\]

For each \(h\in H\) impose (1) using its known coverage class on the parameter face and total inflow \(\sum_C\sum_{i\in R_C}q^C_{ih}\). Each strict sign can use a common slack \(0\le\delta\le1\), maximized and required to have positive optimum. Thus rational LP also tests lower-dimensional parameter faces and open intervals exactly. Any global certificate passes the test on its parameter face by (3). Conversely a passing LP supplies local budgets and shared masses that can be realized together, again by (3).

To reconstruct the strategies, find in each component a closed active face whose budget slice contains the chosen \(b_C\). Solve for a price preimage in its closure at \((\alpha,b_C)\) to obtain private \(x\). At this actual \((x,\alpha)\) compute all best-response edges. Solve the row-flow LP on these edges with (1) and the per-component shared totals just obtained from the global LP. The switching lemma guarantees feasibility. Concatenate the private coverages, the one vector of shared coverages, and the reconstructed row flows.

The global arrangement combines lists of hyperplanes and the global LP combines one flow formulation per component. Both sizes are polynomial even when the number of components grows. Every projection in the price variables uses fixed-dimensional rational vertex and facet calculations. The remaining projections are extrema of rational LPs. Affine budget formulas sum at most one term per private target, so the bit lengths of their denominators are bounded by sums of polynomial input bit lengths. LP vertex bounds, fixed-dimensional determinants and the constant number of successive projection and reconstruction stages give polynomial bit lengths throughout. For an unspecified separator, test all \(\sum_{j=0}^s\binom{|T|}{j}\) target sets by connected-component searches.

## Threshold zero and weak inequalities

In the strictly positive game at \(\lambda=0\), every attacked target must be full. Hence each row attains \(m_i\). On the full target set compute \(L_t(m)\) with all viable incident rows as above. Every full-coverage maximizer for a row has \(L_t(m)=1\). The zero-threshold test is exactly \(\sum_tL_t(m)\le r\). When it succeeds, fill any remaining budget up to the unit caps and send each row to a full-coverage maximizer. Run this single test before enumerating the positive thresholds. Equilibrium existence for the finite game ensures that one of the two searches succeeds. [A1, zero-threshold test](A1-threshold-transport.md#2-eliminate-coverage-through-type-values)

For the single shared target \(h\) there is also an explicit local zero-threshold formula. Write \(c_i\) for the best full-coverage payoff on viable private choices and \(e_i=u_{ih}(\alpha)\), assigning \(-\infty\) to an absent option. The value is \(v_i=\max(c_i,e_i)\), since any attacked private choice must be full. Permitted private coverages satisfy \(L(v)\le x\le\mathbf1\). A private maximizing option with full-coverage utility \(v_i\) then has \(x_t=1\) by its positive slope. Thus \(b\) ranges from \(\sum_{t\in U_C}L_t(v)\) to \(|U_C|\), independently of the shared mass, which ranges from \(\sum_{i:e_i>c_i}p_i\) to \(\sum_{i:e_i\ge c_i}p_i\).

For the original weak inequalities, first remove zero-prior rows. Let \(\varepsilon_0\) be the rational determinant tolerance in A1. Replace all zero slopes and gains by \(\varepsilon=\min(\varepsilon_0,\gamma/2)\), where \(\gamma\) is the smallest positive gap \(m_i-a_{it}\) on an omitted edge. Use \(\varepsilon_0\) when all edges are viable. Each full-coverage row maximum falls by at most \(\varepsilon\). Original viable edges remain viable and all omitted edges retain a strictly positive gap, preserving the separator and its component sizes. Solve the perturbed game, record the positive-flow support and the three defender coverage classes, and solve A1's single global LP minimizing the original equilibrium violations on this pattern. The perturbed solution witnesses violation at most \(\varepsilon\). The determinant bound forces the exact optimum to be zero. Divide the recovered row flows by \(p_i\), give each zero-prior row any best response, and decompose coverage into a rational mixture of \(r\)-target sets if required. [A1, exact repair and defender decomposition](A1-threshold-transport.md#4-transfer-an-exact-positive-coefficient-solver-to-weak-inequalities)

## A connected example

Let there be \(m\ge2\) equally likely types, a shared target \(h\), and private targets \(t_1,\ldots,t_m\). Type \(i\) has uncovered payoff zero on \(h,t_i\) and \(-2\) on all other targets. Set every loss and defender gain to one and take \(r=1\). The viable graph is connected with \(m\) types, and deleting \(h\) leaves one type in each component. Cover every target by \(1/(m+1)\). Type \(i\) sends prior-weighted mass \(1/(m+1)\) to \(t_i\) and \(1/[m(m+1)]\) to \(h\). Every target receives total mass \(1/(m+1)\) and both choices tie in every row. Thus all \(m\) components contribute to the shared-target constraint in one equilibrium. Formula (3) permits arbitrary rational priors, gains and slopes under the same graph restriction.
