# B3f · A superpolynomial number of forced attack assignments

**Theorem.** There are explicitly enumerated, strictly signed rational security games with \(n\) targets, \(n\) equally likely attacker types, unit defender gains and one defender resource for which every equilibrium continuation from budget \(0\) to \(1\) that holds the attack flow fixed during each budget increase needs \(n^{\Omega(\log n)}\) positive-length segments. On that many disjoint budget intervals, every equilibrium has the same prescribed attack flow throughout the interval, and the prescribed flows are pairwise distinct. Their log costs strictly decrease in budget order.

All of these intervals lie in a single phase with every coverage interior, every target on the open defender boundary and every target receiving attack mass \(1/n\). The lower bound applies to every seed choice and min-cost tie rule of the published algorithm and to the greatest fixed-flow jumps in B3a. For this family the equilibrium at the final integer budget can be computed directly in polynomial time. [Li, Conitzer and Korzhyk, Algorithms 1–4 and Lemma 4](https://arxiv.org/pdf/1602.01896#page=7) · [B3a, greatest coverage extensions](B3a-fixed-flow-jump.md)

## A parametric assignment with separated optima

Fix \(h\ge4\) and \(m=\lfloor\log_2 h\rfloor\). Gajjar and Radhakrishnan construct a rationally weighted directed acyclic graph with source \(o\), sink \(t\), and affine arc costs in a parameter \(\lambda\). On \(K=h^m\) disjoint intervals of positive length, \(K\) distinct \(o\)-to-\(t\) paths are respectively uniquely shortest. On each entire interval every other path costs at least one more. The graph has at most \(6h^8+1\) vertices, and each coefficient has \(O((\log h)^3)\) bits. The intervals have integer endpoints in \([0,(h^2)^{m+1}]\). Their first and last midpoints can be computed by \(m\) iterations of the endpoint recurrence in §3.1, taking the smallest and largest digit at each stage. [Gajjar and Radhakrishnan, §3.1, Lemma 14(iii),(vi) and proof of Theorem 1](https://arxiv.org/pdf/1811.05115#page=12)

If a graph representation uses parallel arcs, subdivide each such arc through a private vertex, putting its original cost on the first half and zero on the second. This preserves the paths, their costs and their gaps. The explicit graph has polynomially many arcs in \(h\). Each recursive call joins three smaller graphs and a planarization of polynomially many line segments, and the recursion has depth \(O(\log h)\). Add isolated vertices if needed so the resulting vertex count \(n\) is at least \(h\). Then \(h\le n\le h^{O(1)}\) and \(K=n^{\Omega(\log n)}\). [Gajjar and Radhakrishnan, §§2.1, 3.3](https://arxiv.org/pdf/1811.05115#page=8)

Use the vertices as the rows and columns of a square assignment. Allow every original arc, a zero-weight loop at every vertex except \(t\), and the zero-weight closing arc \(t\to o\). The closing arc is the only allowed outgoing arc at \(t\), so every allowed permutation uses it. The other arcs of its permutation cycle form an \(o\)-to-\(t\) path. Every other cycle is a loop by acyclicity. Conversely, each path, its closing arc and the off-path loops give exactly one allowed permutation. Weighting each original arc by the negative of its cost thus turns shortest paths into maximum-weight assignments. [Related path-to-perfect-matching reduction in Gajjar and Radhakrishnan, Appendix B](https://arxiv.org/pdf/1811.05115#page=36)

Write \(b\) for defender budget and \(s=b/n\) for mean coverage. Let \(\lambda_-\) and \(\lambda_+\) be the midpoints of the leftmost and rightmost path intervals. With \(S_h=\sum_{\ell=1}^m(h^2)^\ell\), the endpoint recurrence gives \(\lambda_-=S_h+h^2/2\) and \(\lambda_+=hS_h+h^2/2\). Make the increasing affine substitution

\[
  \lambda(s)=\lambda_-+
    \frac{4ns-1}{3}\,(\lambda_+-\lambda_-),
  \qquad \frac1{4n}\le s\le\frac1n.
\]

This maps budgets \(1/4\) and \(1\) to those two midpoints. Intersect each path interval with \([\lambda_-,\lambda_+]\) and pull it back to a budget interval \(J_j\). Even the two clipped end intervals retain positive length. Order the \(J_j\) by increasing budget and denote their assigned permutations by \(\pi_j\).

Write the resulting allowed weights as \(B_{iv}-C_{iv}s\). Take

\[
  H=\left\lceil1+\max_{\text{allowed }iv}(|B_{iv}|+|C_{iv}|)\right\rceil,
  \qquad M=(2n+1)H.
\]

Give every missing pair the constant weight \(-M\), so \(B_{iv}=-M\) and \(C_{iv}=0\) there. On the chosen range each allowed weight lies in \([-H,H]\). A permutation using a missing pair has weight at most \(-M+(n-1)H=-(n+2)H\), while every allowed permutation weighs at least \(-nH\). Consequently, with \(W_\pi(s)=\sum_i(B_{i,\pi(i)}-C_{i,\pi(i)}s)\),

\[
 W_{\pi_j}(s)-W_\rho(s)\ \ge\ 1
 \quad\text{for every }\rho\ne\pi_j\text{ and every } ns\in J_j. \tag{1}
\]

## Why every equilibrium uses the prescribed assignment

Set \(p_i=1/n\), set the defender's uncovered and covered utilities to \(0,1\), and use attacker uncovered utility \(a_{iv}\) and covered utility \(a_{iv}-d_{iv}\), where

\[
 \varepsilon=\frac1{64nM^2},\qquad
 a_{iv}=\varepsilon B_{iv},\qquad
 d_{iv}=1+\varepsilon C_{iv}>0 .
\]

For an intermediate budget \(b\), a coverage \(x\) satisfies \(0\le x_v\le1\) and \(\sum_v x_v=b\). The prior-weighted attack flow \(q\) has row sums \(1/n\) and column sums \(z_v\). Positive entries require row-maximal utility \(u_{iv}(x)=a_{iv}-d_{iv}x_v\). The defender maximizes \(\sum_v x_vz_v\). Equilibria exist at every \(0<b\le1\), since the coverage polytope is the convex hull of the finite action set \(\{b e_v\}_v\) and each attacker type has a finite action set. At \(b=1\) this is the original one-resource game. [Conitzer, model in §1](https://arxiv.org/pdf/2610.08796#page=1)

**Coverage and margins.** For every pair and every coverage,

\[
 |u_{iv}(x)+x_v|=\varepsilon|B_{iv}-C_{iv}x_v|\le\varepsilon M .
\]

If \(\max_v x_v-\min_v x_v>2\varepsilon M\), every type strictly prefers a least-covered target to every most-covered target. All most-covered targets receive zero attack mass. Any target receiving positive mass then has strictly lower coverage and room to receive more. Moving a small amount of coverage to it from a most-covered target strictly improves the defender's payoff. Thus every equilibrium satisfies \(|x_v-s|\le2\varepsilon M=1/(32nM)\). For \(1/4\le b\le1\) and \(n\ge2\), this puts every \(x_v\) strictly between zero and one, including at \(b=1\). Feasible transfers in both directions force all defender scores \(z_v\) to agree. Their sum is one, so every \(z_v=1/n\), the defender threshold is \(1/n\) and the open boundary contains every target throughout this whole budget range.

**Assignment.** Write \(x_v=s+\varepsilon y_v\), so \(|y_v|\le2M\). The exact utility identity is

\[
  \frac{u_{iv}(x)+s}{\varepsilon}
    = B_{iv}-C_{iv}s-y_v-\varepsilon C_{iv}y_v .
\]

The matrix \(nq\) is doubly stochastic. Its Birkhoff decomposition uses only permutations supported on positive entries, so each such permutation \(\rho\) attains a row maximum in every row. Sum the row inequalities comparing \(\rho\) with any permutation \(\pi\). The \(-y_v\) summands cancel because each permutation uses every column exactly once. With \(D_\pi=\sum_i C_{i,\pi(i)}y_{\pi(i)}\), this gives

\[
 W_\rho(s)-\varepsilon D_\rho\ \ge\
 W_\pi(s)-\varepsilon D_\pi,\qquad
 \varepsilon|D_\rho-D_\pi|\le4n\varepsilon M^2=\tfrac1{16}.
\]

For \(b\in J_j\), taking \(\pi=\pi_j\) rules out every \(\rho\ne\pi_j\) by (1). Hence every equilibrium has exactly \(q_{i,\pi_j(i)}=1/n\) and all other entries zero. The same comparison shows that the entire row-maximizer graph at any such equilibrium admits just this one perfect assignment. Individual rows may have additional tied targets.

## Number of changes and strict log-cost decreases

Consider a traversal whose positive-length segments cover the budget range from \(0\) to \(1\). If there are finitely many such segments, choose a budget in the interior of each \(J_j\) away from their endpoints. Its segment must have the corresponding forced \(q\), so a segment with fixed \(q\) can contain at most one selected budget. This gives at least \(K\) positive-length segments. With infinitely many positive-length segments that bound holds immediately. In either case the \(K\) prescribed flows occur in order and require at least \(K-1\) flow changes. Reroutings at a single budget preserve the argument. The published Algorithm 3 keeps \(q\) fixed while moving coverage, and B3a's fixed-flow jump maintains equilibrium all along its segment by the linear best-response inequalities and its choice of movable defender targets. [Li, Conitzer and Korzhyk, Algorithms 2–4 and Lemma 4](https://arxiv.org/pdf/1602.01896#page=7) · [B3a, coverage jump and threshold reset](B3a-fixed-flow-jump.md#coverage-jump-and-threshold-reset)

The decrease in \(\ell(q)=\sum_{iv}q_{iv}\log d_{iv}\) is strict between each pair of prescribed flows in budget order. Choose \(s_1<s_2\) so that budgets \(ns_1,ns_2\) belong to distinct \(J_j\), with winners \(\pi,\rho\) respectively. Write \(C_\pi=\sum_i C_{i,\pi(i)}\). At \(s_1\), \(W_\pi-W_\rho\ge1\), and at \(s_2\), \(W_\pi-W_\rho\le-1\). Subtracting these inequalities and using the parameter range yields

\[
 (C_\pi-C_\rho)(s_2-s_1)\ge2,\qquad
 C_\pi-C_\rho\ge\frac{8n}{3}.
\]

For \(|v|\le1/2\), integrating \(-t/(1+t)\) between \(0\) and \(v\) gives \(|\log(1+v)-v|\le v^2\). Here \(|\varepsilon C_{iv}|<1/2\), so the total error for the difference of two sums of \(n\) logs is at most \(2n\varepsilon^2M^2\). For \(q^\pi\) equal to \(1/n\) on \(\pi\), this proves

\[
 n\bigl(\ell(q^\pi)-\ell(q^\rho)\bigr)
 \ \ge\ \varepsilon\left(\frac{8n}{3}-2n\varepsilon M^2\right)
 \ =\ \varepsilon\left(\frac{8n}{3}-\frac1{32}\right)>0.
\]

During this phase the column margins and open boundary are fixed. After min-cost normalization, every target reachable from any boundary seed is still on the boundary and below cap, so the published Algorithm 3 can take a positive step at every state below the terminal budget. The same residual direction gives a positive feasible extension for B3a. At the next normalization the previous flow remains feasible, and min-cost reallocation can only lower or preserve its cost. Each bracket between consecutive selected budgets therefore contains a strict cost decrease. B3a's consecutive-jump lemma also gives \(K-O(1)\) distinct negative simple residual cycles consumed on this single fixed-margin stretch, allowing for the two end cuts. [Published residual directions](https://arxiv.org/pdf/1602.01896#page=7) · [B3a, the cycle consumed at fixed margins](B3a-fixed-flow-jump.md#the-cycle-consumed-at-fixed-margins)

## Binary input size and the one-resource endpoint

The midpoints and the integer \(n\) add \(O((\log h)^2+\log n)\) bits to the affine substitution. Each \(B_{iv},C_{iv}\) uses a constant number of rational operations on these quantities and one edge's coefficients, so its numerator and denominator have \(O((\log n)^3)\) bits. Taking the maximum and ceiling for \(H\), forming \(M,\varepsilon\) and producing the covered and uncovered utilities preserve that bound per entry. The dense payoff table therefore has binary length \(L=O(n^2(\log n)^3)\), with \(L=\Omega(n^2)\) for the explicit encoding. The \(K\) path intervals serve as witnesses and require no entries in the input. Hence \(K=\exp(\Omega((\log L)^2))=L^{\Omega(\log L)}\), superpolynomial in the full input length.

At a specified rational budget \(b\in\bigcup_j J_j\), including \(b=1\), maximize an ordinary assignment with weights \(a_{iv}-d_{iv}(b/n)\). These equal \(-s+\varepsilon(B_{iv}-C_{iv}s)\), so its unique optimum is the required \(\pi\). Solve the rational feasibility LP

\[
 0\le x_v\le1,\quad \sum_v x_v=b,\quad
 a_{i,\pi(i)}-d_{i,\pi(i)}x_{\pi(i)}
 \ \ge\ a_{iv}-d_{iv}x_v\quad\text{for all }i,v.
\]

Existence of an equilibrium and the forced-flow result guarantee feasibility. Every solution makes the assigned row choices optimal, and their uniform column masses make the defender indifferent over feasible coverages. Both the assignment and the LP take polynomial bit time. At \(b=1\), \(x_v\) itself is the probability that the defender chooses target \(v\). The general complexity of finding one equilibrium at the requested budget remains open. [Conitzer's computational question](https://arxiv.org/pdf/2610.08796#page=1)

**Small exact check.** Take vertices \(o,a,b,t\) and three paths, direct, via \(a\) and via \(b\), with respective assignment weights \(0,2\lambda-2,4\lambda-8\) placed on their first arcs. Use zero weights on the remaining allowed arcs and \(\lambda=4(4ns-1)/3\). Then \(H=100\), \(M=900\) and \(\varepsilon=1/207360000\). Enumerating all 24 permutations at each displayed budget gives the following results. At uniform coverage the assigned edge is row-maximal in every row, which directly certifies these equilibria.

| Budget | Assigned columns in row order \(o,a,b,t\) | Gap to second assignment | \(\prod_i d_{i,\pi(i)}\) |
| --- | --- | ---: | ---: |
| \(1/4\) | \(t,a,b,o\) | \(2\) | \(1\) |
| \(5/8\) | \(a,t,b,o\) | \(2\) | \(4859999/4860000\) |
| \(1\) | \(b,a,t,o\) | \(2\) | \(2429999/2430000\) |
