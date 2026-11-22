# A4h8 Comparing partial market completions

At fixed boundary quotes, one conditional least internal price vector preserves every clearing completion. A flow representation retains all boundary allocations supported at those prices. Committing to individual residual loads can require superpolynomially many states at a single supplied market, even when its boundary prices already equal the minimum.

## One price representative at fixed boundary quotes

First consider a separator of goods \(H\) with fixed prices. The local and exterior buyers are disjoint and see each other's goods only in \(H\). Fold the fixed boundary offers into the local buyers' outside options and solve for the least internal prices \(q\). Take any internally clearing price vector \(p\) at the same boundary prices and any flow supporting it, possibly in a full completion. Buyer feasibility after folding the boundary implies \(q\le p\).

Let \(D=\{j:q_j<p_j\}\) on internal goods and let \(I\) be the local buyers whose best utility strictly increases. Every buyer who bought in \(D\) before belongs to \(I\), and every buyer in \(I\) must demand only \(D\) at \(q\). The old prices in \(D\) were above reserve, so those goods sold \(c(D)\). Conditional feasibility at \(q\) implies \(m(I)\le c(D)\), and the old sales imply \(m(I)\ge c(D)\). Equality shows that the old flow of \(I\) was entirely inside \(D\). Reassign those buyers using a conditional flow at \(q\), and retain everyone else's old assignment. This preserves each boundary purchase, every unchanged sale, and all required sell-outs. The new internal price vector is weakly smaller. The argument preserves the original exterior prices and even its particular flow.

The same result holds with **shared buyers** in the separator, provided their global utility quotes are fixed as well. For shared buyer \(i\) let that quote be \(u_i^\partial\). In the local conditional solve, omit shared rows and raise every internal reserve to

\[
 r_j'=\max\{r_j,\max_{\text{shared }i}(a_{ij}-u_i^\partial)/d_{ij}\}.
\]

An old internally clearing part satisfies these floors and is buyer-feasible for the local buyers with folded boundary offers. Hence \(q\le p\). At every changed good, \(p_j>r'_j\), so it was full and no shared buyer could buy there at the old prices. The same mass equality applies to local buyers and keeps every shared buyer's old purchase. The new floors ensure no local offer exceeds her quote. Any newly tied edge merely adds an option. Sales at unchanged goods are retained even when a synthetic reserve exceeds the original one. One conditional solve thus gives a representative per vector of boundary good prices and shared buyer utilities, with exact original recovery by circulation. [Conditional prices](A4b-direct-hall-search.md#removing-one-good-at-a-trial-price)

Without shared-buyer quotes, equally sized residuals need not make two partials interchangeable. A unit buyer has offers \(4-p_a\) at a private good and \(3-p_b\) on the exterior. Both local choices \(p_a=0\) and \(p_a=2\) can clear the private good with her entire mass when considered alone. They leave the same zero unassigned mass. An exterior price \(p_b=0\) preserves the first local assignment and invalidates the second, since the exterior offer strictly wins there.

## Exact dominance of fixed-price flow states

For a goods-only separator, exact local boundary purchases together with the boundary prices are sufficient to test a **particular** exterior allocation once the local allocation has been verified. To compare sets of allowed completions, keep the joint feasible load set, including how ties connect buyers and goods. At positive boundary prices, local plus exterior loads must equal capacity. At reserve they are only upper bounded.

Write \(U\) for private goods and \(H\) for the fixed-price boundary. Let \(f(S)\) count local buyers trapped in \(S\), and let \(g(S)\) count local buyers touching \(S\), using the demand graph of the particular partial state. For an exterior load vector \(y\), the local boundary capacity remaining is \(c_j-y_j\). The two Hall inequalities give an exact description of the exterior loads the state can accept:

\[
\begin{aligned}
 0\le y\le c_H,\qquad
 y(T)&\le c_H(T)+\min_{R\subseteq U}\{c_U(R)-f(R\cup T)\} &&(T\subseteq H),\\
 y(T)&\ge c_H(T)+\max_{R\subseteq U_+}\{c_U(R)-g(R\cup T)\} &&(T\subseteq H_+).
\end{aligned}
\]

Here \(U_+,H_+\) contain goods above reserve. In a state with committed edges, use its admissible demanded edges for these tests. For an uncommitted state, retain all demanded ties. For fixed-width \(H\), compute the subset bounds by constrained cuts, or replace them by the tight extrema of the subset sums over the implied local flow LP with auxiliary coordinates \(y\). One feasibility test checks for an empty set. Tightening the bounds then takes \(O(2^{|H|})\) polynomial-size rational LP calls. Inclusion of one such set in another can be tested by checking the extrema against the other state's subset bounds. This is a sufficient exchange test for the particular exterior market and an exact comparison across abstract exterior loads. A maximum or minimum on each coordinate separately can miss joint bounds. [Fixed-price upper and lower Hall cuts](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

For example, at price 1 on two unit boundary goods, let a local unit buyer bid 1 on both and tie with outside. A support commitment that forbids her outside edge requires local loads to sum to one. With the outside edge allowed they can sum to anything up to one. The per-good intervals are \([0,1]\) in both states. Two exterior unit buyers who strictly prefer their own respective boundary goods leave zero residual supply. Only the state retaining the outside tie admits that continuation. This is one market with two different restrictions on its ties.

### Antichains at the supplied quantities

Take two boundary goods of capacity \(M=2^k-1\) each. On **each** side, \(k\) buyers of masses \(1,2,\ldots,2^{k-1}\) bid 3 on both goods at unit slope. One extra exterior unit buyer bids 1 only on the first good. The minimum is \((1,1)\). At unequal prices with a cheapest price below 1, all \(2M\) core mass strictly prefers the cheap good. At equal prices below 1, this mass plus the extra buyer exceeds total capacity. At \((1,1)\) the groups clear by complementary assignments and the extra buyer takes outside.

At those true minimum prices, choosing an endpoint for each entire local buyer gives \(2^k\) different committed loads \((z,M-z)\). A concrete exterior allocation can require each corresponding complement \((M-z,z)\). A different committed load cannot preserve it, since both goods are above reserve and must sell out. Thus no two load states dominate each other when keeping every concrete completion. The encoding has \(O(k^2)\) bits. One ordinary flow polytope represents all these choices simultaneously.

Different prices can also separate completions at identical reported loads. Use a boundary good of capacity 2 and an exterior good of capacity 1. A local buyer of mass 1 bids \(D+1\) on the boundary, and an exterior buyer of mass 2 bids \(D+1\) on both, all with unit slopes. For every \(1\le t\le D\) the price pair \((t,t)\) clears with local load 1, the exterior buyer taking one unit of each. Freezing the exterior price at \(t\) and changing the boundary quote makes that buyer strictly prefer one good, which cannot take all her mass after the local purchase. The sell-out flags and local load are constant throughout. With binary \(D\) this distinguishes exponentially many quoted states if every exterior price completion must be preserved. The least prices in this example are zero.

## Finding quotes in a bounded separator class

Fixed quotes give one representative. When the quotes are unknown, a tractable subclass follows from coordinate elimination. Suppose deleting a fixed total number of **buyers and goods** from the viable incidence graph leaves factorized slopes. Eliminate the distinguished goods using A4b price queries and conditional smaller markets. In each resulting base market, perturb supplies as in A4c and apply the reciprocal transpose of A4e. The distinguished original buyers are now goods. Eliminate those by the same coordinate procedure. The remaining factorized problem is an assignment LP after normalization. The one perturbation and the transpose recover the original conditional minimum, and the original capacities are used for the final clearing flow.

The deletion set can be found by enumerating a fixed number of vertices and checking factorization by propagation along a forest. Recursion depth is fixed and both bit sizes and the number of LP and flow calls are polynomial by the A4b precision bound. This includes instances with no small deletion set confined to one side, for example unbalanced cycle families sharing a center buyer in one block and a center good in another. The result chooses boundary quotes adaptively. An unrestricted heterogeneous core can still require solving the full market to obtain its quotes. [Coordinate recursion and precision](A4b-direct-hall-search.md#exact-recursion-and-its-precision) · [Reciprocal transpose](A4e-covering-lp.md#factorized-slopes-and-repeated-covering-solves)
