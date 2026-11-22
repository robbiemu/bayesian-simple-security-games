# A4h10 Search several shared vertices through certified quotes

At fixed shared good prices and buyer utilities, a private conditional solution preserves the joint boundary flow set. B3d uses this fact at shared game targets. If the unknown quotes are certified to move together, there is a further reduction. Sum purchases onto shared goods and subtract purchases by shared buyers. This signed quantity is monotone in the common quote parameter. It can locate the least physical prices even though it forgets which shared vertex receives or sends the flow. [B3d switching](B3d-shared-target-separator.md#why-the-budget-and-shared-masses-separate) · [Market switching](A4h-boundary-dominance.md#one-price-representative-at-fixed-boundary-quotes)

## A signed load at fixed shared quotes

Call the shared goods $H$ and the shared buyers $I$. Fix quotes $p_h(t)$ strictly increasing and $u_i(t)$ strictly decreasing in $t$. A private buyer can buy from a shared good without checking the shared capacity. A shared buyer can buy at her fixed utility from a private good without checking her shared row mass. Keep all private buyer row sums, private good capacities, original private reserve sell-outs, and cover inequalities with fixed quotes. Direct trades between shared vertices are treated outside the branch.

Fold shared goods into the private buyers' outside offers and raise private reserves to prevent offers to shared buyers from exceeding their quotes. Solve that private market at its minimum. Split a folded outside choice among its attaining original options. A private good with slack at its synthetic reserve above its original reserve can fill its remaining capacity from a shared buyer tight there. This gives a local flow with all physical private constraints. At the representative prices, minimum-cost flow finds the smallest signed load

$$
 D_{\min}(t)=\min\{x(\text{private buyers},H)-x(I,\text{private goods})\}.
$$

For any other internally clearing prices at these quotes, the A4h8 switch moves their flow to the representative while preserving boundary flows edge by edge. A private good whose price falls in the switch could have had no purchase from a shared buyer at its old price, since her offer would exceed her unchanged quote at the lower price. A maximum-cost flow at the same representative gives the largest load $D_{\max}(t)$. The attainable signed loads form the full closed interval between the optima. Dividing by a common quantity unit makes the private flow bounds integral. Both endpoints are multiples of that unit.

For $t<t'$, compare two locally clearing outcomes. Let $S$ contain the private goods whose prices rise, together with $H$. Every private buyer using $S$ at $t'$ is restricted to it at $t$. Every shared buyer purchase at $t$ lies in $S$, since her lower quote at $t'$ could not cover the old offer at an unchanged or cheaper good. The private goods of $S$ sell out at $t'$ and can receive at most that quantity at $t$. Subtracting their private purchases from the comparison gives $D(t)\ge D(t')$ for every choice of loads at the two quotes.

On a bounded range the private minima and their flows stay in compact boxes. Limits preserve local clearance. The right and left limits of the minimum load are therefore $D_{\min}(t)$ and $D_{\max}(t)$, respectively, by monotonicity and the limit of minimizing flows. For this local calculation, extend the quote functions past the boundary of the core domain. The local problem imposes floors and outside bounds only on private vertices. There are finitely many private demand graphs and reserve statuses, so the minimum load is a finite step function.

## One parameter can replace an arbitrarily large separator

**Theorem.** Suppose supplied certificates guarantee that at the physical minimum the shared goods and buyers lie on a rational affine family with the strict monotonicity above. Assume $H\ne\varnothing$ and that the private conditional markets can be solved in polynomial bit time. Then the full market can be solved in polynomial bit time with no factorization assumption on the direct shared offers.

The domain of $t$ consists of the shared reserve and outside bounds, direct shared cover inequalities, and finite quote ceilings. These give a rational interval containing the unknown $t^*$. Sum the minimum signed loads of the private components. The upper-bracket test is

$$
 \sum_C D_{C,\min}(t)\le
 c(H)-m(I)+\sum_{i\in I:\,u_i(t)=o_i}m_i .
$$

The allowance for outside flow of shared buyers can only appear at the upper endpoint. At $t^*$, the physical clearing flow satisfies the inequality, since direct shared trades cancel. The predicate is monotone.

For $t<t^*$, take $S$ to be the goods with trial prices strictly below their minima. It contains $H$, and every member is above reserve at the minimum. Any private buyer touching $S$ there must spend her entire mass in $S$ at the trial. Every trial purchase by a shared buyer goes into $S$, by her higher quote. The private capacities in $S\setminus H$ imply

$$
 \sum_C D_C(t)\ge m(N^*(S)\setminus I)-c(S\setminus H)>c(H)-m(I),
$$

where $N^*(S)$ is the set of buyers demanding some good of $S$ at the minimum. The last inequality is the strict minimum Hall bound. Every shared buyer quote at $t<t^*$ is strictly above outside. Thus the first passing parameter is exactly $t^*$.

Each trial uses one conditional minimum and one flow per component. The original tight-price determinant bound and one affine shared quote give a polynomial-bit denominator bound for $t^*$, so exact bisection and reconstruction take polynomially many trials. At $t^*$, the switch applied to a physical minimum shows that the conditional representatives have the true minimum prices. Reimpose every shared margin by one original flow.

A connected tree of certified tight buyer–good equalities supplies such a family. Start with one shared good price as $t$ and propagate the equalities. Positive slopes make other good quotes increase and buyer quotes decrease, and edge substitutions give polynomial-bit coefficients. One way to certify the equalities is to show that particular edges must carry positive flow.

The final flow cannot be replaced by the net-load test. Take two unit boundary goods with quotes $p_1=p_2=t$, and two unit buyers each with offers $6-p_1,6-2p_2$, outside zero. The minimum at $t=0$ clears by splitting. For every $0<t<3$, the signed load is still two, but both buyers demand only the first good.

## Many groups on a factorized core

Suppose the core edges normalize to unit slopes. Partition core vertices into groups $g$, with buyers $I_g$ and goods $H_g$ in each. Assume supplied certificates at the physical minimum give normalized quotes

$$
 U_i=B_i-z_g\quad(i\in I_g),\qquad Z_j=A_j+z_g\quad(j\in H_g).
$$

Allow each private branch to touch any number of core vertices within one group. The branches are internally disjoint and the different group parameters can vary independently. Direct core offers give difference inequalities $z_{g(j)}-z_{g(i)}\ge b_{ij}-A_j-B_i$. Core reserves and outsides give bounds on the individual $z_g$. Work in a finite rational box with any artificial bounds beyond the physical minimum's quote ceilings. By contracting tight edges of a unit-slope core, a connected collection of certified tight quotes has exactly the stated form.

Enlarge the original physical supplies as in A4c before making any conditional calls. The original minimum is the unique clearing price at the enlarged margins, and strict minimum Hall persists since the total increase is less than an original quantity unit. Let $q$ be a common unit of the enlarged margins. Write $C_g=c(H_g)$, $M_g=m(I_g)$ for the actual shared supply and mass. For each branch $C$, take a convex piecewise-affine function $\phi_C$ whose right derivative is $-D_{C,\min}$. Its subgradient interval is $[-D_{C,\max},-D_{C,\min}]$. On the core domain consider

$$
 F(z)=\sum_g\left((C_g-M_g)z_g+\sum_{C\text{ attached to }g}\phi_C(z_g)\right).
$$

No breakpoint list is needed. The physical solution $z^*$ minimizes $F$. Its branch loads give allowed subgradients. Trades on tight direct core edges are nonnegative multipliers of the difference constraints. Its unused capacity at reserve and unused buyer mass at outside give the lower and upper bound multipliers.

**Least relaxed minimizer.** At any minimizer $z$, convex optimality gives signed branch loads and nonnegative transfers on tight core edges, with net inflow $n_g$ to group $g$ satisfying

$$
 n_g=C_g-M_g-\ell_g+u_g.
$$

Here $\ell_g,u_g\ge0$ are supported on active lower and upper bounds, respectively, and transfers inside a group cancel. Choose the local representative prices and flows realizing these loads. They can violate individual core margins.

Let $G=\{g:z_g<z_g^*\}$. If it is nonempty, it has no active upper bounds, so $\sum_{g\in G}n_g\le\sum_{g\in G}(C_g-M_g)$. Let $S$ be all physical goods priced below their true minima at this trial. The core goods in $S$ are exactly the goods of $G$. All trial purchases by core buyers of $G$ go into $S$ because their quotes are higher than at the minimum. Every core buyer touching $S$ at the minimum belongs to $G$. A buyer from a group outside $G$ would face a strictly improved offer in $S$ while her quote has not risen, contradicting cover. Every private buyer touching $S$ at the minimum is restricted to $S$ at the trial.

If $S\ne\varnothing$, count that necessary private flow into $S$, subtract the private goods' capacity there, and cancel internal core trades of $G$. This gives

$$
 \sum_{g\in G}n_g\ge m(N^*(S)\setminus I_{\rm core})-c(S\setminus H_{\rm core})
 >\sum_{g\in G}(C_g-M_g)
$$

by strict minimum Hall. If $S$ is empty, $G$ consists of buyer groups, whose higher quotes allow no purchases. The balance then requires $0\le-\sum_{g\in G}M_g<0$, again impossible. Thus $z^*\le z$ at every minimizer.

### Exact solution from load queries

For $k\ge1$ groups minimize $F_\epsilon(z)=F(z)+\epsilon\sum_g z_g$ with $\epsilon=q/(2k)$. To bound its growth from $z^*$, normalize a nonzero feasible direction to sup norm one. Fix its orthant and one coordinate at $1$ or $-1$. The active difference rows with this signed box are totally unimodular, so vertices of the direction polytope have entries in $\{-1,0,1\}$. The directional derivative is linear in that orthant. If the derivative of $F$ is positive at a vertex, it is at least $q$ and the tilt subtracts at most $q/2$. If zero, a sufficiently short step is another relaxed minimizer, so its direction is nonnegative and its coordinate sum at least one. Therefore

$$
 F_\epsilon(z)-F_\epsilon(z^*)\ \ge\ \epsilon\|z-z^*\|_\infty .
$$

Each subgradient query takes one conditional minimum and one signed flow per branch. If the box has lower dimension, find universally tight rows by rational LP. These are fixed coordinate differences and coordinate equalities. Substitute their offsets and work in the free coordinates, where the domain has an interior ball of radius with polynomial encoding length. An infeasible rational ellipsoid center gives a violated domain inequality. A feasible center farther than a reconstruction tolerance $\tau$ gives a subgradient cut preserving the feasible part of the ball of radius $\epsilon\tau/(2M)$ about $z^*$, for a rational subgradient norm bound $M$ from the physical margins. Convex combinations of $z^*$ with the interior ball give a scaled ball in that intersection. Its radius has polynomial bit length, so rounded ellipsoid volume decrease forces a center within $\tau$ in polynomially many queries. The original tight-price determinant bound and the normalized relations give the required $\tau$ and polynomial encoding lengths. Extend reconstructed candidates by conditional minimum prices and check enlarged physical clearance. Supply perturbation makes the first passing candidate exact. Use one final flow at original capacities. [A4h9 sharpness and reconstruction](A4h-mixed-port-composition.md#polynomial-bit-choice-of-queries)

### A family with two-vertex attachments

For $m\ge2$, use home buyers $i$, home goods $h_i$, $m$ connector buyers of total mass $1/4$, and $m$ connector goods of total capacity $1/4$. All connector margins are positive. The core has unit slopes. Each home buyer has mass two and bids $9+t_i$ at $h_i$ and nine at every connector good, for rational $1\le t_i\le2$. Each connector buyer bids $2+t_i$ at every $h_i$. Give each home good capacity $9/4$. Attach one branch to each home buyer and its home good. It has a private good $k_i$ of capacity one, a private unit buyer bidding $2+t_i$ on $h_i$ and one on $k_i$ at unit slopes, and the home buyer's offer $9-2p_{k_i}$. Reserves and outside utilities are zero.

At $p_{h_i}=t_i$, $p_{k_i}=0$, and zero connector prices, each private buyer uses one unit on $h_i$. The connector buyers divide their $1/4$ evenly over the home goods. Each home buyer fills its home good and sends its remaining $3/4+1/(4m)$ to $k_i$. This clears, so the home buyer's minimum-price utility is at least nine. The private good and all connector goods together cannot take two units, forcing each home purchase. The equality $U_i+Z_{h_i}=9+t_i$ supplies its group's certificate. A home price below $t_i$ would attract both its home buyer and its private buyer strictly, exceeding capacity. The displayed prices are the minimum.

Each private branch meets both ends of a certified home edge. The four-cycle through that edge has unequal alternating slope products. Two dense connector blocks are joined by at least two disjoint home edges, so the incidence graph has no single-vertex separator. The grouped algorithm handles the branch with one quote parameter while the final circulation preserves the separate buyer and good margins.

## Where certificates come from

A4h6 jumps and A4h9 signed Hall screens can propose and sometimes certify the required equalities on a supplied instance. The results above give a polynomial-time use for them once supplied. Their existence and efficient discovery remain open on unrestricted markets. In L4b, a price relation needs a proof that covers the particular perturbed or reserve-shifted query. Even a tie forced at both extremes can disappear in between. [Relation tests](A4h-hybrid-jumps.md#relaxations-that-screen-a-proposed-relation) · [Endpoint structure and reuse](L4-structured-endpoints.md)

### Select from an already certified menu

There is no subset search if the desired quotient is a forest of the raw viable goods graph and all available pair relations join adjacent goods in that graph. Contract every certified relation, and delete pinned groups. If some subset of this menu would make that raw quotient a forest, the full quotient is a minor of it, and hence a forest as well. The actual viable envelope graph is a subgraph of the raw quotient, because the group reserve respects every physical reserve. A4h7's envelope forest algorithm then finishes. The same argument handles a fixed number of vertex deletions to a forest, using A4b after grouping. The graph premise uses raw edges before pruning. It does not apply to arbitrary identifications of nonadjacent vertices.

### Certify ties across all capacities in a proportional family

Partition buyers into classes $I$ and goods into classes $G$. Suppose their outside utilities and reserves are constant within their respective classes. Let $M_I=\sum_{i\in I}m_i$, and let the capacities in $G$ have common form $\lambda a_j$ with $A_G=\sum_{j\in G}a_j$. For every nonempty block and every affine offer label $(b,d)$ occurring there, test for an unweighted transport on the edges carrying that label, with row fractions $m_i/M_I$ and column fractions $a_j/A_G$. The test uses one rational flow per label. In the quotient use mass $M_I$, capacity $\lambda A_G$, and each block's maximum over its affine offer labels. Every quotient flow lifts by choosing an attaining label and distributing that purchase according to its certified fractions. All rows see the same maximum label because their fractions are positive.

Increase or decrease physical capacities by small positive amounts in the same fractions $a_j/A_G$, with total shift below one quantity unit. This preserves the coupling certificates. The lifted quotient clearance at the shifted margins equals the unique physical price extreme of the original market by the two-sided Hall argument of L4b. Thus each physical price extreme is constant on goods classes. This works throughout the capacity family and at any floors constant within the classes. In particular, the L4b reserve path to a classwise constant greatest price uses the same couplings. Applying the method needs no adjacent pair already forced to trade. A tractable quotient, such as an envelope forest, supplies the resulting clearing oracle. [Envelopes on forests](A4h-forced-price-relations.md#exact-contraction-after-certification) · [Two-sided supply shift](L4-newton-and-continuation.md#the-market-endpoints-of-one-threshold)
