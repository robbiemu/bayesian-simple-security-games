# Exact search on supplied unit markets

There are polynomial-time exact algorithms with arbitrary rational slopes when each good has at most two viable buyers, or when each buyer has at most two viable goods. The direct good-side algorithm extends to an efficiently recognizable condition on cycles. A deletion formula for arbitrary unit markets also computes a specified price through finitely many smaller calls, with no price bisection. It gives polynomial time with logarithmically many exceptional goods of bounded degree above a hereditary base class.

Normalize reserves and outsides to zero. Write \(H\) for the bipartite incidence graph of viable offers, those with strictly positive net intercept \(b_{ij}\). An omitted edge can carry flow only in an outside tie at reserve, where it can be replaced by outside. A cycle of \(H\) is balanced if the products of its two alternating sets of slopes are equal. On a graph with every cycle balanced the slopes have a factorization \(d_{ij}=\alpha_i\beta_j\), found by propagating rational ratios along a spanning forest. [Factorized cover](A4e-covering-lp.md#factorized-slopes-and-repeated-covering-solves)

## Identify positive goods and solve their conditional market

Call a set \(A\) of goods eligible for this calculation if \(|N_H(S)|>|S|\) for every nonempty \(S\subseteq A\). At the least clearing prices \(p^*\), the actual positive-price set satisfies this condition by strict minimality Hall. If each good has at most two viable buyers, every positive good has exactly two. Both demand it at the minimum. View these goods as edges between their two buyers. A cycle would have as many buyers as goods, violating strict Hall on that cycle's goods. Hence the full viable graph induced by the positive goods is a forest, including when the graph on all goods has many cycles. More generally the algorithm only needs balanced slopes on the eligible sets. [Strict minimum-price Hall test](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

Maintain a set \(A\) of certified positive goods, initially empty. Pin all other goods at zero and fold their offers into the outside utility \(w_i=\max(\{0\}\cup\{b_{ij}:j\notin A\})\) of each buyer. On \(A\), divide each row by its factor \(\alpha_i\) and rescale each price by its factor \(\beta_j\). One ordinary assignment LP on bids \((b_{ij}-w_i)/\alpha_i\) and minimization of the original price sum on its optimal dual face give the conditional least prices. Extend them by zero on the omitted goods and call the result \(q\). The restriction of \(p^*\) is buyer-feasible for the conditional market because fixing omitted prices at reserve only strengthens the outside offers. Minimum prices are dominated by all buyer-feasible prices, so \(q\le p^*\). [Buyer-feasible domination](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)

Run a buyer-feasibility test in the full market at \(q\), respecting capacity upper bounds and all outside ties. If it passes, domination in the full market gives \(q=p^*\). Otherwise take the inclusion-minimal goods set \(S\) maximizing \(f_q(S)-|S|\), where \(f_q(S)\) counts buyers with all best options in \(S\). The maximizing deficit is positive. Such a set comes from the source-reachable side of a residual maximum flow. To see that every good of \(S\) has a strictly higher price at \(p^*\), set \(T=\{j\in S:q_j<p_j^*\}\). If \(T\subsetneq S\), strict minimality of the maximizer gives

\[
 f_q(S)-f_q(T)>|S|-|T|.
\]

Those counted buyers have a best option in \(S\setminus T\), its price unchanged at \(p^*\). Every option in \(T\) becomes worse and every option outside \(S\) was already worse. These buyers must all buy in \(S\setminus T\) at \(p^*\), contradicting capacity. Thus \(S\) consists entirely of positive goods at the minimum. It includes at least one good outside \(A\), since the conditional flow passes every upper Hall cut within \(A\). Add \(S\) to \(A\) and repeat. There are at most \(n+1\) conditional solves, followed by one original clearing flow. Each solve starts from original coefficients and products along one spanning forest, with polynomial bit length. [Hall cuts and restricted markets](A4h-alternating-tree.md#hall-cuts-select-a-restricted-market)

### Recognize a broader slope class

The sufficient condition that every eligible set have a balanced induced graph is equivalent to the absence of an unbalanced simple cycle with a neighboring buyer outside that cycle. For a simple cycle with \(r\) goods and \(r\) buyers, every proper subset of its goods already has more neighbors than goods along the cycle. These subsets induce paths when the cycle goods are viewed as edges between buyers. The full set passes strict Hall exactly when an additional buyer touches it. Conversely, any unbalanced cycle in the graph on an eligible set has an eligible set of cycle goods, hence such a neighbor.

This condition is polynomially testable. For each buyer \(i\), delete \(i\) and compute the biconnected blocks of the remaining graph. Reject if an unbalanced block contains a good that had an edge to \(i\). To justify the test, an unbalanced cycle in a biconnected block yields an unbalanced cycle through any specified good in that block. If the good is off the cycle, take two internally disjoint paths from it to distinct vertices of the cycle, with interiors off the cycle. Together with the two cycle arcs they define two cycles through the good. Their directed slope products give the original cycle product as a quotient, up to orientation, so at least one is unbalanced. Test each block by rational factor propagation. The sufficient condition is inherited by removing buyers, goods or viable edges. In particular it includes all markets with at most two viable buyers per good.

The good-side method extends to rational physical masses and capacities when \(m_i\le c_j\) on every viable edge, under the same unbalanced-cycle condition. An unbalanced cycle has no neighboring buyer outside it. Match the buyers of the cycle to its goods along alternating edges. Their total mass is at most the cycle's total capacity, contradicting strict weighted Hall if all its goods were positive. Thus the positive graph is balanced. Use the weighted versions of the conditional assignment and deficit cut above.

## Transfer the good-side solver to the buyer side

In a unit market the reciprocal transpose exchanges the roles of buyer utility and good price. Its offer on the swapped edge is \((b_{ij}-u_i)/d_{ij}\). A clearing pair is characterized by the same feasible cover inequalities, equality on an integral matching and complementary outside/reserve slacks. Least transpose prices give greatest original prices. To see the order, every clearing satisfies

\[
 u_i=\max(0,\max_j(b_{ij}-d_{ij}p_j)),\qquad
 p_j=\max(0,\max_i(b_{ij}-u_i)/d_{ij}).
\]

The second equality uses that every positive-price good is matched. Each formula is order reversing. [Linearly transferable matching](https://arxiv.org/html/2402.12200v2#S2)

For each buyer \(i\), solve the reciprocal transpose of the market with \(i\) deleted. Write \(q^{(-i)}\) for the greatest prices of this smaller original-orientation market. Then the utility of \(i\) at the full-market minimum is

\[
 u_i^*=\max(0,\max_j(b_{ij}-d_{ij}q_j^{(-i)})).                 \tag{1}
\]

Here is a proof of the buyer-removal identity. At the greatest price of the reduced market, every nonempty set of reduced buyers with positive utilities demands more real goods than its cardinality, by strict Hall in the transpose. Insert \(i\) into a clearing matching at those prices. If she cannot take outside, follow alternating paths from her demanded goods through their current owners and those owners' best edges. An unassigned good or a buyer who can take outside ends an augmentation. If neither occurs, the reached goods are in bijection with the reached reduced buyers, whose utilities are positive and whose best options are confined there. This contradicts strict Hall in the transpose. The augmented prices therefore clear the full market and satisfy \(q^{(-i)}\ge p^*\). Put \(S=\{j:q_j^{(-i)}>p_j^*\}\). At \(q^{(-i)}\) the reduced buyers fill \(S\). Those \(|S|\) buyers are all strictly restricted to \(S\) at \(p^*\), as each has a best good whose price was lowered there. If \(i\)'s utility also strictly increased at \(p^*\), she too would be restricted to \(S\), which would exceed stock. This proves (1), including ties to outside. [Alaei, Jain and Malekian, Theorem 2.I](https://arxiv.org/pdf/1006.4696#page=10)

When each original buyer has at most two viable goods, every good of each reciprocal transpose has at most two viable buyers. The good-side algorithm therefore computes all \(q^{(-i)}\) with one such solve per original buyer. Compute the utilities by (1), recover prices by the inverse offer formula, and run one matching at those prices. Each transpose has at most \(k-1\) goods, so there are at most \(k^2\) conditional assignment solves and polynomial bit time. The same reasoning works whenever the reciprocal graph passes the broader cycle test.

## Delete one good without bisection

For any given good \(j\) in a general unit market, the same proof gives

\[
 p_j^*=\min_{i\in N_H(j)} q_j^{(-i)} .                        \tag{2}
\]

If the viable neighbor set is empty, the price is zero. To prove (2), use the set \(S\) of raised goods from the buyer-removal proof. The \(|S|\) reduced buyers who fill \(S\) at \(q^{(-i)}\) must fill it at \(p^*\) too, so \(i\) cannot be matched there at \(p^*\). If \(i\) holds \(j\) in an original minimum matching, this gives \(q_j^{(-i)}=p_j^*\). If \(j\) is unsold in some such matching, it lies in none of the raised sets. At reserve, a nonviable sale can take outside, leaving the good unsold. This gives a witness in the claimed minimum when it is nonempty.

Apply (1) in the reciprocal transpose of \(M-i\) to buyer \(j\) there. Each term \(q_j^{(-i)}\) becomes the maximum of zero and the bids \((b_{aj}-u_a)/d_{aj}\) for \(a\ne i\), where \(u_a\) comes from the least prices in \(M-i-j\). Thus (2) uses at most the viable degree of \(j\) ordinary minimum-price calls, all omitting \(j\). After computing its exact quote, fold it into outside and make one further solve of the remaining market. The A4b equality at the minimum quote gives the rest of the original vector. [Coordinate removal and recovery](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)

If deleting \(h\) specified exceptional goods leaves a hereditary tractable class and their viable degrees are at most \(D\), repeat this procedure for those goods. It uses at most \((D+1)^h\) base solves with polynomial overhead per call. A fixed \(D\) permits \(h=O(\log L)\). Fixed \(h\) also permits unrestricted \(D\). Minimum prices at every level have tight paths to reserve or outside, so each output coordinate is a composition of at most \(k+n\) original-data affine maps from a current anchor. A folded outside offer is one further affine evaluation of the price returned at its level. Thus each recursion level adds a polynomial input-bit bound to the anchor length. Buyer-side exceptions transfer through (1) and reciprocal transposition.

These results still leave arbitrary unit markets open. The deletion formula can branch across the full dimension, and a one-call reduction puts the unrestricted task already at maximum incidence degree three. The separate ascending algorithm has a polynomial bound when logarithmically many slope exceptions remain after factorization. [Degree-three reduction](A4j-unit-degree-three.md) · [Matching-based ascent](A4j-unit-matching-ascent.md)
