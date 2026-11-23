# A4l. Detect markets that reduce to ordinal stable allocation

Local comparisons of the two cutoffs on each offer give an exact support-discovery algorithm with arbitrary binary rational masses and capacities. With unit quantities, one proposer-optimal stable matching and one price LP suffice.

## Recognize the class

Normalize reserves and outside utilities to zero. Retain the viable offers with \(b_{ij}>0\). Such an edge \(e=(i,j)\) has buyer cutoff \(A_e=b_{ij}\) and good cutoff \(B_e=b_{ij}/d_{ij}\). The cover is

\[
 \frac{u_i}{A_e}+\frac{p_j}{B_e}\ge1 .
\]

Rank offers by decreasing \(A_e\) within each buyer and decreasing \(B_e\) within each good. Require strict rankings on both sides. For edge \(e\), let \(r_e\) be the ratio to \(A_e\) of the largest strictly lower buyer cutoff in its row, and \(s_e\) the ratio to \(B_e\) of the largest strictly lower good cutoff in its column, using zero when there is no lower offer. The test is

\[
                   r_e+s_e<1\qquad\text{on every viable edge }e .
\]

Compute the ranks and test with rational comparisons. Domaniç, Lam and Plaxton previously used affine assignment games to represent ordinal matching with indifferences. The test here applies to supplied affine markets with strict rankings and extends the allocation lift to binary quotas. [Tiered-slope markets, §3](https://arxiv.org/pdf/1707.01496#page=10)

The test depends on the local ratios for each edge, so even \(\max_e r_e+\max_e s_e>1\) can pass.

## Recover a clearing from an ordinal stable allocation

The ordinal problem has the same quotas as the physical market. Each side prefers more allocation on any viable edge to unused quota, and prefers to move allocation from a lower-ranked edge to a higher-ranked edge. Edge capacities may be taken larger than the total mass. An edge blocks if both endpoints would accept additional flow on it, through slack or by moving flow from a worse edge. We first use positive quotas on both sides.

**Clearance implies ordinal stability.** If edge \(e\) blocks a clearing allocation, then \(u_i=0\) or buyer \(i\) has a worse used edge \(f\). Tightness on \(f\) gives \(u_i\le A_f\le r_eA_e\). Likewise \(p_j\le s_eB_e\). These bounds violate the cover on \(e\). At a clearing, a purchase on a nonviable edge ties outside at reserve and can be assigned to outside. We compare real allocations after dropping those purchases.

**Ordinal stability implies clearance.** In an ordinal stable allocation let \(w_v\) be the worst used edge at a full vertex \(v\). A positive quota makes this edge well-defined. Write \(T_{v,e}\) for the cutoff of \(e\) at \(v\), put \(W_v=T_{v,w_v}\), and write the quote at \(v\) as \(W_v z_v\). The quote is a utility for a buyer and a price for a good. At a slack vertex use \(W_v=z_v=0\).

Every used edge is the worst used edge of at least one full endpoint. Otherwise both endpoints can add flow there, contradicting stability. For a used edge \(e\) that is worst at both full endpoints, set \(z_i=(r_e+1-s_e)/2\) and \(z_j=1-z_i\). For any other worst edge \(e=w_v\) directed from its full endpoint \(v\) to the other endpoint \(w\), impose

\[
 z_v=1-(W_w/T_{w,e})z_w .
\]

At \(w\) the coefficient is zero if slack. Otherwise \(w_w\) is worse than \(e\), and the coefficient is at most \(r_e\) or \(s_e\) for that side, hence less than one. The equations form paths feeding into assigned endpoints or cycles. All maps send \([0,1]\) into itself. Solve each cycle by composing its affine maps, whose slope magnitude is less than one, then propagate back along the paths. The solution uses polynomial-bit rationals, since all coefficients have polynomial bit length and each propagation uses at most the number of vertices. One can also use an exact linear system on the \(z_v\).

Every used edge is tight by its worst-edge equation. At each full vertex, \(z_v\) strictly exceeds the lower-cutoff ratio of its worst edge at that vertex. For a mutual worst edge this follows from the split. For a one-sided worst edge it follows from \(z_w\le1\) and \(r_e+s_e<1\). Therefore the quote at a full vertex exceeds each cutoff strictly below its worst used cutoff. Every unused viable edge has an endpoint full with all used edges strictly preferred to it, by ordinal stability. The quote at that endpoint alone strictly covers the unused edge. Slack vertices have zero quote. These facts give all covers and complementary conditions for the original physical allocation.

The two directions establish exact equality of the allocation sets on the viable graph, with outside and unsold stock recorded as slack. For example, take all quotas one and

\[
 A=\begin{pmatrix}16&4\\4&16\end{pmatrix},\qquad
 B=\begin{pmatrix}4&16\\16&4\end{pmatrix}.
\]

Flow \(1/2\) on each edge is ordinally stable. The four one-sided worst edges form a cycle with coefficient \(1/4\) on each step. The four normalized quotes are \(4/5\), giving \(u_i=p_j=16/5\) and four exact ties.

## Exact minimum prices and the unit shortcut

Increase capacities as in A4c, which also makes each quota positive when an original capacity is zero. The ordinal instance keeps the original ranks and uses the new quotas. Compute an ordinal stable allocation by a polynomial-time stable-flow algorithm. Use a source arc per buyer, a sink arc per good, and an arc with capacity above total mass per viable edge. Blocking options give blocking walks from a slack or willing buyer to a slack or willing good. Clear denominators in the quotas for polynomial-bit integer arithmetic. The lift above gives a clearing at the enlarged capacities and hence the original minimum. One original-capacity circulation returns a physical equilibrium. [Ordinal allocation with quotas, Baïou and Balinski](https://doi.org/10.1287/moor.27.4.662.302) · [Stable flow, Cseh and Matuschke](https://arxiv.org/pdf/1309.3701#page=12) · [A4c exact recovery](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

With unit quotas one may omit the supply increase. Run buyer-proposing deferred acceptance on the two strict rankings. Let its proposer-optimal stable matching be \(M_0\). Lift \(M_0\) by the mutual-worst splits. At the original minimum, the utilities dominate those of this lift. A buyer matched in \(M_0\) now has utility strictly above every lower cutoff, so every clearing matching at the minimum must give her at least that rank. Such a matching is ordinally stable, and \(M_0\) already gives each buyer her highest stable rank. Consequently every clearing matching at the minimum equals \(M_0\). One original support LP minimizing total price recovers \(p^*\). Deferred acceptance uses at most the number of viable offers in proposals. The rank computations, support LP and flow use polynomial-bit rational data.

The class permits unbalanced slope cycles and multiple ordinal stable matchings. For example, use

\[
 A=\begin{pmatrix}2&10&7\\4&1&16\\4&1&16\end{pmatrix},\qquad
 B=\begin{pmatrix}2&1&16\\10&4&4\\7&16&1\end{pmatrix}.
\]

The largest edgewise sum is \(19/20\), while \(\max r+\max s=7/5\). The two stable matchings, listed by assigned good for each buyer, are \((2,3,1)\) and \((3,1,2)\). Deferred acceptance selects \((2,3,1)\). At \((0,0,3/4)\) it clears and buyers 2 and 3 both demand the only positive-price good. Strict Hall certifies the minimum.

## Checks

The weighted replay compares ordinal stability and original affine clearance by exact vertex enumeration on all 10,304 feasible allocations from its half-unit two-by-two grid. The 282 stable allocations include 98 split supports and 14 supported four-cycles with one-sided worst edges. The unit replay checks the half-cutoff construction on all 46,656 strict three-by-three preference profiles, and checks the proposer-optimal matching against 67 exact minimum-price computations. The proofs of recognition and the lift use arbitrary binary rationals. The replays use small inputs and the polynomial-time allocation call uses the cited stable-flow result. [Weighted replay](../experiments/a4l_weighted_ordinal.py) · [Unit replay](../experiments/a4l_unit_ordinal.py)
