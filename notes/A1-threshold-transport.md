# A1. Payoff thresholds and capacitated transport

**Result.** With \(k\) positive-prior types and \(n\) targets, an exact equilibrium can be found in \((1+nk^2)^{O(k)}\operatorname{poly}(L)\) time, where \(L\) is the binary input length. The proof covers zero utility slopes and zero defender gains. At any specified coverage vector, a flow test finds the full interval of admissible defender thresholds. Deciding whether *some* equilibrium admits threshold zero is NP-complete on a class where finding an unrestricted equilibrium is easy. The prior collection gives a fixed-type algorithm and the rent correspondence. The perturbation below gives a separate way to extend exact solvers to weak signs. [Conitzer, *Open problem: Computing Bayes-Nash equilibrium in simple security games*](https://arxiv.org/pdf/2610.08796) · [Prior research collection, physical pp. 13–15 and 29–32](../sources/prior-collection.md)

## 1. Fixed coverage gives an exact flow test

Discard zero-prior rows until the final conditional strategies are reported. Assume \(n,k\ge1\), \(p_i>0\), \(\sum_i p_i=1\), and rational input. For a proposed \(x\in[0,1]^n\) with \(\sum_t x_t=r\), set

\[
 v_i=\max_t(a_{it}-d_{it}x_t),\quad
 N_i=\{t:a_{it}-d_{it}x_t=v_i\}.
\]

Write \(Z,I,O\) for the target sets with \(x_t=0\), \(0<x_t<1\), and \(x_t=1\), respectively. For a best response of the defender, each covered coordinate has score \(s_t=\beta_t\sum_i q_{it}\) at least as large as any coordinate below its cap. Moving a small amount of coverage proves necessity. Sorting the scores proves sufficiency. Thus a nonnegative threshold always suffices, including \(r=0,n\).

Send supply \(p_i\) from row \(i\) along edges to \(N_i\). For \(\beta_t>0\) impose the following bounds on column inflow \(y_t=\sum_i q_{it}\).

| Coverage | Lower bound \(\ell_t\) | Upper bound \(u_t\) |
| --- | --- | --- |
| \(t\in Z\) | 0 | \(\lambda/\beta_t\) |
| \(t\in I\) | \(\lambda/\beta_t\) | \(\lambda/\beta_t\) |
| \(t\in O\) | \(\lambda/\beta_t\) | \(+\infty\) |

If \(\beta_t=0\) and \(\lambda>0\), positive coverage there is impossible. A zero-gain target at zero coverage can accept any inflow. At \(\lambda=0\), every zero-gain target accepts any inflow, as does every full target. All positive-gain targets below full coverage must receive zero. These rules give a bounded-flow feasibility test with rational data, solved by one ordinary max-flow reduction. Infinite upper capacities can be implemented as 1.

For positive \(\beta_t\), the test also yields an exact description of the feasible thresholds. For \(J\subseteq T\) let

\[
 h(J)=\sum_{t\in J}\beta_t^{-1},\qquad
 A(J)=\sum_{i:N_i\subseteq J}p_i,\qquad
 B(J)=\sum_{i:N_i\cap J\ne\varnothing}p_i .
\]

Then all feasible \(\lambda\ge0\) form the interval

\[
 \left[
   \max_{\varnothing\ne J\subseteq Z\cup I}\frac{A(J)}{h(J)},\
   \min_{\varnothing\ne J\subseteq I\cup O}\frac{B(J)}{h(J)}
 \right] .
\]

An empty lower family contributes 0 and an empty upper family contributes \(+\infty\). The interval is empty if its lower endpoint exceeds its upper endpoint. \(B\) is a weighted coverage function and hence submodular. Its complement \(A(J)=1-B(T\setminus J)\) is supermodular.

**Proof.** With arbitrary column intervals \(\ell\le u\) and nonempty row neighborhoods, feasibility is equivalent to \(A(J)\le u(J)\) and \(\ell(J)\le B(J)\) for every \(J\). To check sufficiency, make a circulation with arcs of fixed flow \(p_i\) from the source to each type, unbounded type-to-neighbor arcs, column-to-sink arcs in the stated intervals, and a sink-to-source arc of fixed flow 1. In the lower-bound cut criterion, a finite outgoing cut containing a type must contain all of its neighbors. For a fixed column set \(J\) on the cut's inside, the largest mass of such included rows is \(A(J)\). When the sink is outside the cut, the cut inequality is bounded by \(A(J)\le u(J)\). When it is inside, it is bounded by \(A(J)\le1-\ell(T\setminus J)\). The latter equals the lower-bound test on the complement. In the threshold table only \(J\subseteq Z\cup I\) can constrain upper capacities. In a lower-bound test, removing members of \(Z\) leaves \(\ell(J)\) unchanged and can only decrease \(B(J)\). This proves the interval formula. The endpoints can be found by rational LPs minimizing and maximizing \(\lambda\) on the flow formulation.

## 2. Eliminate coverage through type values

For proposed values \(v\), the inequalities \(a_{it}-d_{it}x_t\le v_i\) require \(a_{it}\le v_i\) whenever \(d_{it}=0\). On every target define

\[
 L_t(v)=\max\bigl(\{0\}\cup
 \{(a_{it}-v_i)/d_{it}:d_{it}>0\}\bigr).
\]

Reject \(L_t>1\). Feasible coverage must satisfy \(x_t\ge L_t\). A positive-slope edge can carry mass only at \(x_t=L_t=(a_{it}-v_i)/d_{it}\). A zero-slope edge with \(a_{it}=v_i\) stays tight for every feasible \(x_t\). Actual row values are certified when every row sends its entire positive supply along tight edges.

Assume for the moment \(d_{it},\beta_t>0\). At \(\lambda>0\), every target with \(x_t>0\) receives positive mass, including full targets. Some incoming edge is then tight and has positive slope. At \(x_t=0\) the lower bound is automatically attained. Consequently **\(x_t=L_t(v)\) for every target**. Given \(v\), check \(\sum_t L_t=r\) and use the tight graph at \(L\) in Section 1. An LP verifies existence of \(\lambda>0\) and returns \(q\). If a target has \(\beta_t=0\), it must have \(x_t=L_t=0\) at a positive threshold.

At \(\lambda=0\) with all \(d_{it},\beta_t>0\), put \(m_i=\max_t(a_{it}-d_{it})\). Every actual \(v_i\ge m_i\). Every attacked target must be full, so its utility is at most \(m_i\). Hence necessarily \(v_i=m_i\) for every row. At these values, \(L_t(m)\le1\). Every target attaining the maximum in \(m_i\) has \(L_t(m)=1\) by its positive slope. Thus the exact feasibility criterion is \(\sum_t L_t(m)\le r\). If it holds, augment \(L(m)\) arbitrarily up to total \(r\) within the unit box, and send each row to any of its maximizers under full coverage. All those targets remain full and the certificate has \(\lambda=0\).

## 3. Exact search with a fixed number of types

Use the preceding zero-threshold test first on the positive-coefficient game. For the positive-threshold case, let \(g_{it}(v)=(a_{it}-v_i)/d_{it}\). In \(\mathbb R^k\) form the hyperplanes \(g_{it}=0\), \(g_{it}=1\), and \(g_{it}=g_{jt}\) for each \(t\) and \(i<j\), with the first two families taken for all \(i\). There are at most \(H=n(2k+\binom{k}{2})\). The sign pattern on any relatively open face determines an affine expression for each \(L_t\), its status relative to 0 and 1, and the entire equality graph. This includes ties on lower-dimensional faces.

One explicit enumeration starts with the empty sign pattern and inserts the hyperplanes one at a time. For each surviving pattern, try all three signs of the next hyperplane. For equations use \(f(v)=0\). For every strict sign use \(\sigma f(v)\ge\delta\), where \(\sigma\in\{-1,1\}\), and maximize the same \(0\le\delta\le1\). Keep the extension exactly when its optimum is positive. A finite family of strict inequalities has a positive common margin at each strictly feasible point. The total number of nonempty faces at stage \(h\) is bounded by \(\sum_{j=0}^k2^j\binom hj\). Indeed, a new hyperplane that cuts an old face replaces it by three faces, and the cuts inject into the faces of its induced \((k-1)\)-dimensional arrangement. Duplicates do not increase the count.

On a completed face discard \(L_t>1\), then solve another rational LP. Retain the sign constraints, set \(x_t=L_t(v)\), require \(\sum x_t=r\), impose \(q\ge0,\ \sum_tq_{it}=p_i\), and fix \(q_{it}=0\) off the equality graph. Impose the threshold table in Section 1 and add \(\lambda\ge\delta\). Maximize \(\delta\). A positive optimum returns an equilibrium on this face. Conversely every positive-threshold equilibrium determines a face that passes. A bound \(0\le\lambda\le 1+\max_t\beta_t\) is harmless when searching for one certificate, including at \(r=0\).

This costs \((1+H)^{O(k)}\) polynomial-size rational LPs. Division by an input slope and the margin LPs take polynomial bit length. Basic feasible output has polynomially many bits by determinant bounds. This proves a bit-polynomial algorithm for constant \(k\). The exponent depends on \(k\).

## 4. Transfer an exact positive-coefficient solver to weak inequalities

The following reduction also applies to algorithms other than the arrangement search. It allows exact output in the weakly monotone model while retaining the original number of types and targets.

Let \(Q\) be the product of the denominators of all entries \(a,d,\beta,p\), written as reduced rationals. Choose \(b\ge2\) so that the magnitudes of their numerators and denominators, and \(n,r\), are at most \(2^b\). Put

\[
 B_0=2^{b+2},\quad N=kn+n+k+2,\quad
 \Delta=(NQB_0)^N,\quad \varepsilon=1/(2\Delta).
\]

Here \(N\) counts \(q,x,v,\lambda\) and one violation variable \(\eta\). The bit lengths of \(\Delta\) and \(\varepsilon\) are \(O(N(\log N+\log Q+b))\). Replace only the zero \(d_{it}\) and \(\beta_t\) by \(\varepsilon\), solve the strictly positive instance exactly, and record its positive-flow support \(S\) and coverage classes \(Z,I,O\). If only the strategies are returned, recover \(v_i\) by maximizing the perturbed row utilities and take \(\lambda=\max\{s_t:x_t<1\}\), with the empty maximum 0, using perturbed scores.

For the original inputs solve this LP on that pattern. Hard constraints are the row sums, nonnegativity and zero off-support of \(q\), the coverage box and budget, \(x_t=0\) on \(Z\), \(x_t=1\) on \(O\), \(-B_0\le v_i\le B_0\), \(0\le\lambda\le B_0\), and \(0\le\eta\le1\). Minimize \(\eta\) subject also to

\[
\begin{aligned}
 a_{it}-d_{it}x_t-v_i&\le\eta &&(\text{all }i,t),\\
 v_i-a_{it}+d_{it}x_t&\le\eta &&((i,t)\in S),\\
 s_t-\lambda&\le\eta &&(t\in Z\cup I),\\
 \lambda-s_t&\le\eta &&(t\in I\cup O).
\end{aligned}
\]

The perturbed solution with \(\eta=\varepsilon\) is feasible, since \(x_t,y_t\in[0,1]\). The LP is compact. Multiply every row by \(Q\) to obtain integer coefficients and right-hand sides bounded in absolute value by \(QB_0\). Every vertex denominator is at most \(\Delta\) by Cramer's rule and Hadamard's bound. Any strictly positive optimal \(\eta\) would be at least \(1/\Delta\), contradicting feasibility at \(\varepsilon\). Therefore the optimum is zero. Return any optimal basic solution. A previously positive edge may now carry zero, and a coordinate labeled \(I\) may reach an endpoint. Equality \(s_t=\lambda\) still certifies either endpoint. The repaired strategies are an exact equilibrium of the original instance.

Conditional probabilities are \(q_{it}/p_i\). For a zero-prior row, choose any maximizer at the returned \(x\). A mixed defender strategy can be constructed by placing intervals of lengths \(x_t\) consecutively on \([0,r)\). For \(u\) uniform on \([0,1)\), take the targets whose intervals contain one of \(u,u+1,\ldots,u+r-1\), with half-open intervals. They are \(r\) distinct targets and target \(t\) has inclusion probability \(x_t\). Sort the fractional parts of the interval endpoints to obtain at most \(n+1\) explicit pure strategies and rational weights with polynomial bit length. At \(r=0\) use the empty set.

## 5. Threshold-zero selection with flat utilities

Consider Hitting Set with nonempty sets \(D_i\subseteq T\) and budget \(r\le n\). Use positive uniform priors, \(\beta_t=1\), \(d_{it}=0\) everywhere, \(a_{it}=1\) on \(D_i\) and \(a_{it}=0\) elsewhere. The row's best-response set is always \(D_i\). In any equilibrium admitting \(\lambda=0\), the full targets hit each \(D_i\) because any positive-flow column must be full. Their number is at most \(r\). Conversely, pad a hitting set to \(r\) targets, cover them fully, and assign each row to one of its selected favorites. This gives a threshold-zero certificate. Membership in NP follows on this subclass from the hitting-set certificate and on the full model from the closed pattern LP in Section 4 with \(\eta=\lambda=0\). Thus the property is NP-complete. Finding an unrestricted equilibrium on the reduction class takes one choice of favorite per row followed by sorting the column masses and covering the largest \(r\).

A two-target example illustrates the envelope issue. With one row, \(r=1\), \(a=d=(0,0)\), and \(\beta=(1,1)\), take \(x=q=(1/2,1/2)\). Then \(\lambda=1/2\) although \(L(v)=(0,0)\). This example also has the two pure equilibria in which both players choose the same single target. Crossing their strategies violates the defender's best response. Interchangeability in a strict-slope formulation therefore needs an assumption when stated for the weak inequalities in the problem description. [Conitzer, problem statement and interchangeability discussion](https://arxiv.org/pdf/2610.08796)

## 6. A fixed-total assignment reduction

Exact fixed-total fair rent division with affine strictly decreasing preferences reduces to this game even when \(r=1\), there are \(n\ge2\) uniformly likely types and \(n\) targets, and \(\beta_t=1\). Let the utility for room \(t\) at rent \(P_t\) be \(h_{it}-b_{it}P_t\), \(b_{it}>0\), with prescribed \(\sum_tP_t=C\) and possibly negative individual prices. Put \(c_{it}=h_{it}-b_{it}C/n\). Choose a rational \(K>n\max_i(\max_t c_{it}-\min_t c_{it})/\min_{it}b_{it}\), for example the displayed bound plus 1. Set

\[
 a_{it}=c_{it}+K b_{it}/n,\quad d_{it}=K b_{it},\quad
 P_t=C/n+K(x_t-1/n).
\]

This preserves every row's preferences exactly and \(\sum_tP_t=C\). If any equilibrium has \(x_j=0\), each row strictly prefers \(j\) to every \(t\) with \(x_t\ge1/n\). All positive flow then goes to targets with \(x_t<1/n\), and some target with positive coverage \(x_t\ge1/n\) has zero score. Moving a little coverage from the latter to any positive-flow target is a strict improvement, a contradiction. All \(x_t>0\), hence also \(x_t<1\) as \(n\ge2,r=1\). All column masses equal \(1/n\). The matrix \(nq\) is doubly stochastic, so its positive support has a perfect matching by Hall's theorem. Assigning the rooms by this matching gives an exact envy-free solution. All constructed coefficients have polynomial binary length. This one-way search reduction establishes neither a complexity lower bound beyond rent division nor an algorithm for general security games. Arunachaleswaran, Barman and Rathi prove an FPTAS for fixed-total rent division and exact polynomial algorithms under additional slope restrictions. [*Fully Polynomial-Time Approximation Schemes for Fair Rent Division*, Sections 4.1 and 6](https://arxiv.org/pdf/1807.04163)

## Next research nodes

- **A1a.** In the strict-slope problem, fix \(\lambda>0\), temporarily release \(\sum x_t=r\), and give target \(t\) a market supply \(\lambda/\beta_t\), price floor zero, and row \(i\) an outside option \(m_i=\max_t(a_{it}-d_{it})\). For a game certificate, trim excess flow on full targets to the outside option. Any row using a full target has utility \(m_i\). In the reverse direction a clearing price above 1 attracts no row and cannot sell its positive supply, and every row on its outside option has a full target attaining \(m_i\). Restoring its mass there gives the cap inequality. This proves an exact fixed-\(\lambda\) market equivalence before reinstating the resource equality. The augmentation rule must handle binary-encoded masses \(p_i,\lambda/\beta_t\), since replicating units can take exponentially many copies. L3 also finds a skipped demand event in the printed unit-market algorithm, and shows how an exact minimum-price oracle would suffice for the resource equality. [*An Expressive Mechanism for Auctions on the Web*, Theorem 3.9](https://paulduetting.com/pubs/teac15b.pdf) · [L3 market review and reduction](L3-prior-partials.md)
- **A1b.** For the same market, study the interval of attainable total prices as \(\lambda\) changes. A prospective oracle must deliver \(\sum x_t=r\) even at a threshold where the extremal clearing-price vectors differ. The fixed-coverage cut functions in Section 1 change when the tight graph changes.
- **A1c.** Determine whether a fixed number of distinct slope values gives a bound on the number of weighted-transport pivots with arbitrary binary priors and gains. In the unit assignment problem a matching's slope-product weight is determined by its integer histogram. A fractional flow's histogram can have many rational values, so transferring the unit proof requires another invariant. [Arunachaleswaran, Barman and Rathi, Section 4.1](https://arxiv.org/pdf/1807.04163)
