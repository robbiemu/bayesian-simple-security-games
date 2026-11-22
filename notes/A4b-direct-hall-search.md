# A4b. Direct price search by removing a good

**Results.** A test for whether the minimum price of one good is at most a trial value reduces to the minimum-price problem on the remaining goods and one weighted Hall flow. This gives a polynomial-bit algorithm at bounded elimination depth. On a forest of goods that buyers consider together, the algorithm can instead store each branch's required purchases from its parent as a function of the parent price. These functions have polynomially many steps even with binary rational masses and capacities. This gives an exact polynomial-bit algorithm on arbitrary forests, and after deleting any fixed number of goods to obtain a forest. The general dense-market oracle remains open. [Market model and minimum-price certificate](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

## Removing one good at a trial price

Write \(v_{ij}(x)=a_{ij}-d_{ij}x\), with \(d_{ij}>0\). A buyer-feasible vector respects the reserves and admits a flow sending each buyer's mass to best options, subject only to capacity upper bounds. At equilibrium all goods above reserve sell out. At the minimum equilibrium price \(p^*\), every nonempty set \(S\) of above-reserve goods has strictly more mass in buyers demanding at least one good in \(S\) than the total capacity of \(S\). This gives \(p^*\le q\) for every buyer-feasible vector \(q\). Indeed, take \(S=\{j:q_j<p_j^*\}\). Every such good was above reserve. Every buyer previously demanding some good in \(S\) now strictly prefers \(S\) to its complement and outside, so a nonempty \(S\) would exceed capacity. Conversely, at a clearing price the same strict cut characterizes minimality. It depends only on best options, masses, capacities and which coordinates are at reserve. [L3 oracle reduction](L3-prior-partials.md#conditional-exact-reduction-to-a-minimum-price-oracle) · [A4 certificate](A4-minimum-price-markets.md#certifying-a-candidate-minimum-price)

Fix a good \(s\) and \(t\ge r_s\). Delete \(s\), change buyer \(i\)'s outside utility to \(\max(o_i,v_{is}(t))\), and let \(h(t)\) be the remaining market's minimum prices. Reinsert the good at \(t\). At the resulting vector \((t,h(t))\), give \(s\) unlimited capacity and let \(L_s(t)\) be the *least* total flow into \(s\) over buyer-feasible flows. Such a flow exists because the collapsed outside option can be expanded to any original option attaining it. To test \(L_s(t)\le c_s\), one ordinary Hall flow with the actual capacity suffices.

**Coordinate test.** The following are equivalent.

1. \(p_s^*\le t\).
2. Some buyer-feasible vector has coordinate \(s\) exactly \(t\).
3. \(L_s(t)\le c_s\).

At \(t=p_s^*\) one moreover has \(h(t)=p^*_{-s}\).

For 1 to imply 2, the case \(t=p_s^*\) uses the original equilibrium. For \(t>p_s^*\) raise the reserve only on \(s\) to \(t\) and take the new minimum equilibrium. If its price on \(s\) strictly exceeded \(t\), the clearing conditions and the A4 minimum certificate at that vector would be identical for the original reserves. The vector would equal \(p^*\), contradicting \(p_s^*<t\). Thus the new equilibrium has \(p_s=t\) and is buyer-feasible under the original reserves.

For 2 to imply 3, let \((t,q)\) have a buyer-feasible flow. Collapsing \(s\) into outside gives \(h(t)\le q\). Use a feasible flow of the collapsed market at \(h(t)\) for precisely those buyers whose best utility strictly increases from \((t,q)\) to \((t,h(t))\). They use only remaining goods whose price strictly fell. For every other buyer keep the original flow at \((t,q)\). Each of her used options keeps its price, since a strict decrease on one would have increased her best utility. The two groups use disjoint sets of real goods, and only the second can use \(s\). This proves feasibility at \((t,h(t))\). The implication from 3 to 1 is domination by \(p^*\). At \(t=p_s^*\), collapsing the original equilibrium gives \(h(t)\le p^*_{-s}\), while 3 and domination give the reverse inequality.

For a fixed removed market the function \(L_s\) is independent of \(c_s\). For *every* positive rational capacity \(c\) assigned to \(s\), its sublevel set \(L_s(t)\le c\) is the closed ray starting at the corresponding minimum price of \(s\), in the domain \(t\ge r_s\). Thus \(L_s\) is nonincreasing. It has finite range because there are finitely many best-option graphs and the minimum flow value is fixed on each graph. It takes its right-hand value at each jump, by applying the closed-ray property to a rational capacity between distinct flow values. These conclusions include zero as a possible flow value. At \(H_s=\max(r_s,\max_i(a_{is}-o_i)/d_{is})\), every buyer can replace any use of \(s\) by her original outside option, so \(L_s(H_s)=0\). An empty buyer set gives \(H_s=r_s\).

Alaei, Jain and Malekian already use removal of buyers or goods to characterize extremal equilibria in unit markets. Their Theorem 2 alternates between highest and lowest equilibria of smaller markets. Here the smaller market retains the trial good as a buyer-specific outside alternative, and the Hall flow checks the original binary capacity. [Alaei, Jain and Malekian, Theorems 1–2](https://www.cs.cornell.edu/~saeed/archive/competitive_equilibrium_with_general_utilities.pdf#page=9)

## Exact recursion and its precision

Discard an edge if \(v_{ij}(r_j)\le o_i\). It can only be used in a tie with outside at its own reserve, when that mass can take outside instead. This preserves buyer feasibility and the equilibrium prices. Join two goods in the *interaction graph* if some buyer has both remaining edges. Different connected components are independent. An elimination forest chooses one root in each component and repeats in the components left by deleting the root. Its height counts goods on the longest root-to-leaf path.

At a root \(s\), bisect for \(p_s^*\) by the coordinate test, solving the smaller components recursively at each trial. Once the exact coordinate is recovered, solve them once at that value. The coordinate test's equality statement returns all remaining minimum prices. Deleting a good only increases outside utilities, so the graph of the recursive market is a subgraph of the one obtained by deletion. More generally, a fixed number of such deletions above any polynomial-time base class that tolerates the changed outside options preserves polynomial bit time. [Near-factorized base class](A4a-near-factorized-slopes.md)

Here is a uniform precision bound. Let \(N\) be the original number of goods, \(b\) the full original binary input length, and \(A\) the maximum bit length of an ancestor trial price, taking zero at the top. At an interior recursion node each outside utility is the maximum of the original outside and some original offers at fixed ancestor prices. At a minimum price, the A4 graph gives each above-reserve good a simple alternating path to a reserve good or a used outside option. Along each pair of successive goods, equality of a buyer's two utilities expresses the first price as a rational affine function of the second. The final equality expresses the price as a function of an original outside or one fixed ancestor price. A path uses at most \(N+1\) such equalities. After clearing original denominators each step has the form \(z\mapsto(uz+v)/w\) with \(O(b)\)-bit integers. On a rational \(z=P/Q\), the new pair is \((uP+vQ,wQ)\). Consequently every output price has numerator and denominator bit length at most \(A+K\) for an explicitly computable \(K=O((N+1)b)\). For instance, bound each step's bit increase by two plus the maximum bit length of its three integers and multiply by \(N+1\).

Use a common integer lower endpoint strictly below all original reserves and an integer upper endpoint above all original \(H_j\). Return false below the chosen good's reserve. Both endpoints have \(O(b)\) bits and remain valid throughout recursion. With \(D=2^{A+K}\), a bisection bracket narrower than \(1/(2D^2)\) isolates the threshold among rationals of denominator at most \(D\). Recover it by continued fractions of the midpoint. Distinct such rationals are at distance at least \(1/D^2\), and the desired one is a convergent since the midpoint error is less than \(1/(2D^2)\). There are \(O(A+K+b)\) queries. Their dyadic numerators and denominators have at most \(2A+O(K+b)\) bits. At recursion depth \(d\) the trial prices therefore have \(2^{O(d)}\operatorname{poly}(b)\) bits. For an elimination forest of height \(d\) the number of calls per original forest node is at most \((2^{O(d)}\operatorname{poly}(b))^d\). Thus the algorithm runs in \(2^{O(d^2)}(1+b)^{O(d+1)}\) bit time. For fixed \(d\), a suitable elimination forest can also be found by trying roots recursively and testing each residual component. A star permits arbitrarily many heterogeneous buyers at each leaf.

## Polynomial time on arbitrary forests

**Theorem.** If the interaction graph is a forest, an exact minimum price vector and a clearing allocation can be computed in polynomial bit time. Tree height, the number of types considering a pair of goods, and the numerators and denominators of masses and capacities can all grow with the input. After the edge deletion above, each buyer considers one good, two adjacent goods, or only outside.

Root each tree. For a nonroot good \(j\) with parent \(h\), its subtree includes all its private buyers and the buyers on the edge \(jh\). At price \(t\) on \(h\), remove \(h\) and include its offer in each such buyer's outside option. Use minimum prices on the subtree and record the least flow into \(h\) after splitting the collapsed outside into the original options. Denote this function by \(L_{j\to h}(t)\) for \(r_h\le t\le H_h\). Applying the coordinate test to this subtree and a parent good with arbitrary positive capacity shows that each function is a nonincreasing, right-continuous step function. Its value at \(H_h\) is zero.

### Local computation

Let \(E\) be the buyers considering both \(j,h\) and \(I_j\) the buyers considering only \(j\). Write \(m(T)=\sum_{i\in T}m_i\). For a trial price \(x\) on \(j\), the least purchases of \(j\) by its single-good buyers and child subtrees are

\[
B_j(x)=\sum_{k\text{ child of }j}L_{k\to j}(x)+m\{i\in I_j:v_{ij}(x)>o_i\}.
\]

The minima can be attained simultaneously, since these buyers and the child subtrees are disjoint and share only \(j\). A buyer \(i\in E\) strictly requires \(j\) exactly when \(x<b_i(t)\), where

\[
 z_i=(a_{ij}-o_i)/d_{ij},\qquad
 f_i(t)=(a_{ij}-a_{ih}+d_{ih}t)/d_{ij},\qquad
 b_i(t)=\min(z_i,f_i(t)).
\]

The conditional minimum price of \(j\) is therefore

\[
x(t)=\min\{x\ge r_j:B_j(x)+m\{i\in E:b_i(t)>x\}\le c_j\}. \tag{1}
\]

Indeed, the coordinate test on \(j\) in the subtree at parent price \(t\) solves exactly the child submarkets used in \(B_j\). At the least passing \(x\), their conditional minimum prices are the remaining subtree minimum by the equality statement. The functions \(b_i(t)\) are nondecreasing, so \(x(t)\) is nondecreasing. The minimum in (1) can be found by sorting \(r_j\), the jumps of \(B_j\), and the \(b_i(t)\) in \([r_j,H_j]\), with \(H_j\) as a final candidate.

At \(x=x(t)\), the two relevant masses are

\[
P(t,x)=m\{i\in E:v_{ih}(t)>\max(o_i,v_{ij}(x))\},\qquad
U(t,x)=m\{i\in E:\max(v_{ih}(t),v_{ij}(x))>o_i\}.
\]

Then the outgoing function is exactly

\[
L_{j\to h}(t)=\max\{P(t,x),\ B_j(x)+U(t,x)-c_j\}. \tag{2}
\]

Buyers for whom outside attains the maximum can take it. The mass \(U\) of the remaining edge buyers consists of those strictly requiring \(h\), those strictly requiring \(j\), and those tied between the two. Use the child flows attaining \(B_j\), accommodate all the buyers strictly requiring \(j\) by (1), then assign as much tied mass to \(j\) as the remaining capacity permits. This realizes both lower bounds in (2) up to their maximum. Strict comparisons throughout allow all ties with outside to use it.

### The number of steps

Write \(J_j\) for the number of strict drops of \(L_{j\to h}\) on its domain and \(e=|E|\). The function \(B_j\) has at most \(\sum_k J_k+|I_j|\) drops. Along the nondecreasing \(x(t)\), both endpoint utilities of each edge buyer weakly decrease as \(t\) rises. Thus \(U(t,x(t))\) drops at most \(e\) times. The second expression in (2) takes at most \(1+\sum_k J_k+|I_j|+e\) values.

For the first expression, restrict to the buyers with \(v_{ih}(t)>o_i\). Within this set, a buyer counts in \(P(t,x)\) exactly when \(f_i(t)<x\). Between successive crossings of two affine lines \(f_i,f_{i'}\) and successive parent-outside ties, the set and the order of its lines are fixed. Thus the counted buyers form a prefix with at most \(e+1\) possible masses. Counting the crossing points as separate cells handles all ties, including coincident lines. The \(O((e+1)^2)\) cells give \(O((e+1)^3)\) possible values of \(P\), uniformly over \(x\).

The maximum in (2) always equals one of its two arguments. Since the outgoing function is nonincreasing, each of its distinct values occurs on one interval. Therefore

\[
J_j\le \sum_{k\text{ child}}J_k+|I_j|+O((|E|+1)^3).
\]

These bounds add over a subtree. In particular the number of steps of every stored function is polynomial in the number of buyers and goods, regardless of the binary values of masses or capacities.

### Building the functions and recovering prices

Merge the child breakpoints and the single-good outside thresholds to build \(B_j\). Partition \([r_h,H_h]\) at the pairwise crossings of the lines \(f_i\), their intersections with the constants \(r_j,H_j,z_{i'}\) and all breakpoints of \(B_j\), and the parent-outside ties. Include both endpoints. Treat identical lines as permanent ties. In the interior of each resulting interval, all comparisons used by (1) have fixed signs. Its first passing candidate follows the same constant or affine line throughout the interval, and all comparisons in (2) also keep their signs. Evaluate (1) and (2) at the event points and at one rational interior point per interval. Merge equal consecutive values before passing the result to the parent. The preceding bound on the *retained* steps keeps the number of candidate events polynomial at every node.

Each candidate abscissa is an original input comparison, or it solves \(f_i(t)=\nu\) for a child breakpoint \(\nu\) or another original constant. The latter operation is one affine transformation with \(O(b)\)-bit integer coefficients after row clearing. Only computed event abscissas are retained as breakpoints. Tracing their origins to a leaf uses at most \(N\) affine transformations, so all have \(O((N+1)b)\)-bit numerators and denominators. Midpoints used for evaluation and the corresponding \(x(t)\) also have polynomial length. Flow values use the common denominator of all input masses and capacities, whose bit length is at most their combined input length. The values in (2) are bounded by total mass and the local capacity in magnitude. These bounds give polynomial bit time for the bottom-up computation.

At each root, choose the least \(x\ge r_j\) with \(B_j(x)\le c_j\). Descend the tree evaluating (1) at the recovered parent price. Repeated application of the equality case of the coordinate test gives the full minimum price vector. One ordinary flow at that vector, imposing full sales on goods above reserve, recovers a clearing allocation. This also gives polynomial bit time when deleting at most a fixed number of goods makes the graph a forest. Try all such fixed-size deletion sets to find one, use the coordinate recursion on its goods, then use the forest algorithm. Augmenting outside options can only remove viable edges.

For a worked example, take the chain \(h,j,k\) with capacities \((1,3/2,1)\) and all reserves and outside utilities zero. A buyer of mass two values \(j,k\) at \(2-p_j,2-p_k\). Two unit buyers on \(h,j\) have utilities \((4-p_h,4-p_j)\) and \((3-p_h,3-2p_j)\). The leaf sends one unit to \(j\) if \(p_j<2\), and zero if \(p_j\ge2\). Formula (1) gives \(x(t)=\min(t,2)\) on \(0\le t\le4\). Formula (2) now gives \(3/2\) on \([0,2)\), one on \([2,3)\), and zero on \([3,4]\). The least root price meeting capacity one is exactly two, and both remaining prices are two. Assign the first unit buyer to \(j\) and the second to \(h\). The mass-two buyer sends one to \(k\), one half to \(j\), and one half outside. Every good above reserve clears.

## What one Hall test can distinguish

Buyer-feasible prices are closed under the coordinatewise minimum. Given two such prices \(p,q\), retain the flow at \(q\) for buyers with strictly larger best utility there, and the flow at \(p\) for all others. The first group can only use goods with \(q_j<p_j\), the second only goods with \(p_j\le q_j\) or outside. At \(p\wedge q\) each buyer obtains the larger of her two best utilities. This proves the claim, including ties and split masses.

Consequently the upper boxes containing a buyer-feasible vector are exactly those whose upper endpoint dominates \(p^*\). A Hall test using the union of all edges individually demandable in a box can nevertheless give the wrong answer. Take two unit-capacity goods, three unit-mass buyers, unit slopes, zero outside options and reserves, and the upper price bound \((2,0)\). The intercepts are

| Buyer | Good 1 | Good 2 |
| --- | ---: | ---: |
| A | 2 | −10 |
| B | 2 | 1 |
| C | −10 | 2 |

The union permits A outside, B on 1 and C on 2. Both B and C strictly prefer some real good throughout the box, so any feasible assignment requires A entirely outside, forcing \(p_1=2\). Then B and C both strictly require good 2. A fixed-price Hall test also supplies no convex separation of all buyer-feasible prices. With a single buyer of mass two, two unit-capacity goods, utilities \(2-p_j\) and zero outside and reserves, both \((0,0)\) and \((2,4)\) are buyer-feasible. Their midpoint \((1,2)\) forces both units onto the first good.

The coordinate test needs the conditional minimum in the market with the trial good removed. In a dense component this market can still contain nearly the full instance. The forest algorithm uses the fact that a subtree shares precisely one good with its complement. Its boundary demand is then a single nonincreasing function. Extending the step count to several shared goods requires controlling their joint feasible flow and price dependence.
