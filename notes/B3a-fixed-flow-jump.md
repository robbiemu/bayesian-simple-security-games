# B3a. Greatest coverage extensions and irreversible cycle breakpoints

At fixed defender boundary and attack totals, each positive jump after the first destroys a distinct simple alternating cycle. All edges of the cycle are best responses at the jump's start. Its slopes determine a unique coverage on each of its targets. Those coverages all increase during the jump, so the cycle can never be tight again. An individual attack edge can still leave and return. Across changes of attack totals or boundary, a moving target instead consumes a price fixed by a tight path to a box endpoint or a tight path to such a cycle.

Let \(h=\max_C(|E_C|-|V_C|+1)\) over connected components of the bipartite graph of viable type–target pairs, including isolated targets. The resulting exact solver takes \(O(n(n+k)4^h+n)\) iterations of polynomial bit cost for \(n\) targets and \(k\) positive-prior types. This gives polynomial time for \(h=O(\log(n+k))\), with arbitrary rational priors, defender gains and pair-specific slopes. A diamond construction below has exponentially many tight cycle certificates even with one common assignment and fixed target totals. B3f gives a separate construction that forces superpolynomially many consumed cycles in an actual fixed-margin stretch. [Conitzer's problem, §1](https://arxiv.org/pdf/2610.08796) · [Forced flow switches](B3f-forced-flow-switches.md)

## Coverage jump and threshold reset

Initially assume \(d_{it},\beta_t>0\). Write \(p_i\) for row \(i\)'s prior, \(q_{it}\) for its attack mass, \(z_t=\sum_iq_{it}\), \(s_t=\beta_t z_t\), \(u_{it}(x)=a_{it}-d_{it}x_t\) and \(v_i(x)=\max_tu_{it}(x)\). At the current intermediate budget \(\sum_t x_t\), attacks are supported on the tight graph \(A(x)=\{it:u_{it}(x)=v_i(x)\}\). The defender allocates only to targets scoring at least \(\lambda=\max_{t:x_t<1}s_t\). Let \(B=\{t:x_t<1,\ s_t=\lambda\}\). Every target outside \(B\) has coverage zero or one. Initialize at zero coverage with any pure best response in each row. Return at the requested budget \(r\) before computing an open boundary.

**Normalize at the current coverage.** Choose a minimum-cost transportation flow on \(A(x)\) with margins \(p,z\) and costs \(\log d_{it}\). Call the result \(q\). A residual forward arc \(i\to t\) exists for every tight pair and has cost \(\log d_{it}\). A reverse arc \(t\to i\) exists for every positive entry and has the opposite cost. The optional individual caps \(p_i\) are redundant. True optimality can be obtained by rational approximations to log costs preserving strict simple-cycle signs. This is the normalization from the published continuation. In the unit-assignment rent problem, Arunachaleswaran, Barman and Rathi use a fixed-matching price LP and a strict log-weight change when decreasing rents. The arguments here cover fractional transport, increasing coverage and changing margins. [Li, Conitzer and Korzhyk, §6.2](https://arxiv.org/pdf/1602.01896#page=7) · [Arunachaleswaran, Barman and Rathi, §4, Lemmas 3–5](https://arxiv.org/pdf/1807.04163#page=11) · [Exact log costs in L2](L2-exact-arithmetic-audit.md#bit-length-bound-and-exact-lp-outputs)

**Maximize coverage with this flow.** On the whole box impose \(y_t=x_t\) outside \(B\) and, for every \(s\) with \(q_{is}>0\) and every \(t\), impose

\[
 y_t\ \ge\ \frac{d_{is}}{d_{it}}y_s+
                 \frac{a_{it}-a_{is}}{d_{it}}.
\]

These inequalities say precisely that every used edge remains best. They also enforce equality between used options. All coefficients of \(y_s\) on the right are positive, so the compact, nonempty polytope is closed under componentwise maximum. Taking the maximum of individual coordinate maximizers proves it has a greatest point \(y^*\), the unique maximizer of \(\sum_t y_t\). In particular \(y^*\ge x\) without putting the old fractional coverage in the LP. If the requested budget lies on the segment from \(x\) to \(y^*\), interpolate linearly to it and return. Otherwise make the entire positive jump if \(y^*\ne x\). The segment keeps all used edges best by convexity. All increasing coordinates have the highest open defender score, so every intermediate profile is an equilibrium for its attained budget. Recompute the boundary at the endpoint.

**Reset the threshold if \(y^*=x\).** At this fixed \(x\), minimize \(\lambda'\ge0\) over \(q'\ge0\) supported on \(A(x)\), with row sums \(p_i\). Write \(z'_t=\sum_iq'_{it}\) and impose

\[
\begin{aligned}
 \beta_t z'_t &=\lambda' &&(t\in B),\\
 \beta_t z'_t &\le\lambda' &&(t\notin B,\ x_t<1),\\
 \beta_t z'_t &\ge\lambda' &&(x_t=1).
\end{aligned}
\]

Use a vertex optimum and retain its margins for the next normalization. The freedom to reassign outside loads makes this a modification of published Algorithm 4. These three score conditions preserve defender optimality and every current member of \(B\).

To check the reset, let \(R_b(q)\) be the vertices reachable from target \(b\) in the residual graph. If the reachable targets lie in \(B\) and no reachable directed cycle has negative cost, put \(\gamma_w=\exp(-\operatorname{dist}_b(w))\) on reachable vertices and zero elsewhere. Then \(\gamma_i\le d_{it}\gamma_t\) for all tight pairs, with equality on \(\operatorname{supp}q\). Raising \(x_t\) at rate \(\gamma_t\) lowers the used payoff of row \(i\) at rate \(\gamma_i\). This preserves every used best response for a sufficiently short interval, since inactive comparisons have strict slack. All movable targets are below cap and \(\gamma_b=1\). Normalization excludes negative cycles. Therefore if \(y^*=x\) every \(b\in B\) has a path to an outside target. Also \(\lambda>0\), since zero load on all open targets would leave them without reverse arcs.

For each \(b\) send \(\delta/\beta_b\) along one such path, ending at its first outside target. Choose \(\delta>0\) small enough for all reverse capacities and open outside score slacks. All members of \(B\) then have score \(\lambda-\delta\), and full targets can receive the mass. Hence the reset strictly lowers \(\lambda\). At an optimum the actual open maximum is \(\lambda'\), since \(B\) is nonempty and its equalities hold. If no target joins \(B\), a failure after normalization at the new margins would permit the same small decrease in the very LP just minimized. Consequently each reset either adds a previously absent target to \(B\) or is immediately followed by a positive jump. An open member of \(B\) can leave only at saturation. A target can enter at most once and leave at most once. This proves the failure count, including simultaneous optima and threshold zero. [Compare the residual path arguments in L2](L2-exact-arithmetic-audit.md#state-and-exact-steps)

## The cycle consumed at fixed margins

Consider two consecutive positive jumps within one fixed \(B,z\) stretch. Let \(x^*\) be the completed endpoint of the first jump and \(q^-\) its flow. Let \(q^+\) be the flow normalized at \(x^*\) for the next jump, and choose a target \(b\) that increases in that jump.

1. **Reachability agrees at \(q^-\) and \(q^+\).** Their difference is a circulation because their margins agree. Decompose it into positive multiples of cycles in the residual graph of \(q^-\). If a new reverse arc \(t\to i\) appears at \(q^+\), one such cycle contains the forward arc \(i\to t\). Its remaining arcs already give a path \(t\leadsto i\) at \(q^-\). Replace each new arc in this way, and use symmetry. This argument uses feasibility alone.
2. **Every reachable target moves.** Put \(w_t=x^{\rm next}_t-x^*_t\ge0\) and \(\delta_i=v_i(x^*)-v_i(x^{\rm next})\). On each pair tight at \(x^*\), \(\delta_i\le d_{it}w_t\). Equality holds on \(\operatorname{supp}q^+\), which stays best. Starting from \(w_b>0\), positivity passes from a target to its used rows and from those rows to every tight target. Thus every target in the common reachable set increases, and all of them belong to \(B\).
3. **The old reachable set contains a negative simple cycle.** Otherwise the preceding shortest-path construction, applied just on \(R_b(q^-)\), increases \(b\) while keeping \(q^-\) best at \(x^*\). This contradicts greatestness of the first jump. In particular normalization at \(x^*\) strictly lowers the optimum relative to the feasible old flow. Equality of the two log costs would force \(q^-\) already to be optimal and the second jump to fail.
4. **That cycle is permanently lost.** On a simple alternating tight cycle, traversing a row from target \(s\) to target \(t\) gives \(x_t=(d_{is}/d_{it})x_s+(a_{it}-a_{is})/d_{it}\). Following the cycle gives \(x_s=Gx_s+H\), where \(G\) is the exponential of the negative residual cycle cost. Here \(G>1\), so \(x_s=H/(1-G)\) is fixed by the input. The same holds at every cycle target. All these coverages become strictly larger in the second jump, and no coverage ever decreases. The undirected cycle can never again be tight, even after a threshold reset or a boundary change.

Thus a fixed-margin stretch has at most one initial positive jump plus the number of simple cycles of nonunit gain in its viable graph. The cycles consumed in different stretches are distinct globally. Each simple cycle lies within one biconnected block, so for this fixed-margin count one may sum \(2^{h_D}-1\) over the blocks \(D\), with \(h_D=|E_D|-|V_D|+1\). For example, a cactus graph contributes at most its number of cycle blocks, however many cycles its largest connected component contains. The case with no subsequent positive jump spends no such certificate. In particular the number of steps with a given individual edge can exceed one.

## Paths to a fixed coordinate across margin changes

There is a source-specific charge for *every* positive jump. At initialization, any chosen moving coordinate \(b\) has \(x_b=0\). Later let \(x^*\) be the last completed greatest extension, \(B^-\) its movable targets at that jump's start, and \(q^-\) its flow. Any intervening resets leave \(x^*\) unchanged. For any \(b\) that increases in the new jump, one of the following certificates determines its old value.

- If \(b\notin B^-\), it was frozen at zero. A unit coordinate cannot increase.
- If \(b\in B^-\), search the residual graph at \(x^*,q^-\). A path to a target outside \(B^-\), or one that has reached its cap at \(x^*\), ends at value zero or one. The first such target gives a simple tight path. Along each edge \(v_i=a_{it}-d_{it}x_t\) is an invertible affine relation between its endpoint variables. The fixed terminal value therefore determines \(x_b^*\) from the path.
- If there is no such target, a reachable negative simple cycle must exist. In its absence the old flow could increase \(b\) at its claimed maximum. The cycle determines all its target coverages and row values. A simple tight path from \(b\) to its first vertex on that cycle determines \(x_b^*\).

The chosen value of \(x_b^*\) can be charged only once for that \(b\). The new jump strictly exceeds it, even if the budget cuts the jump short. This proof allows both the margins and \(B\) to change and uses no sign assumption on the intercepts.

For the count, retain an edge \(it\) precisely when \(a_{it}\ge m_i=\max_s(a_{is}-d_{is})\). Every tight pair is retained. In a connected component with cycle rank \(h_C\), any two fixed vertices admit at most \(2^{h_C}\) undirected simple paths. Relative to one reference path, their distinct edge incidence vectors differ by elements of the binary cycle space of dimension \(h_C\). Simple cycles inject into the nonzero elements of that space. For each \(b\) there are consequently at most \(2n\,2^h\) endpoint-path values, counting both endpoint values and also the length-zero path. There are at most \((2^h-1)(n+k)2^h\) cycle-path values, allowing any cycle vertex as the path endpoint. Across all \(b\), this bounds positive jumps by

\[
 J\ \le\ n\big[2n\,2^h+(2^h-1)(n+k)2^h\big].
\]

At most \(J+2n\) threshold resets occur by the failure count. The bound sums over targets and uses the maximum component rank. Arbitrarily many independent cyclic components are allowed. [Viability on the coverage box in B1](B1-classify-run-lengths.md#counting-the-signatures-two-ways)

**Bit complexity.** Every completed extension is the vertex of a rational polytope specified by original slopes, intercepts, support, and outside values zero or one. Its bit length is polynomial in the input length, independent of the number of jumps. The threshold reset also has input-only coefficients and right-hand sides. Its vertex supplies new margins of polynomial bit length. Normalization at fixed margins returns a transportation vertex of polynomial bit length, including at the initial pure assignment. Its rational cost approximations have polynomial bit length by the simple-cycle sign argument. Budget interpolation uses two input-size coverages and one rational scalar. Thus each iteration takes polynomial bit time in the original input length.

For weak payoffs, first omit zero-prior rows. Take the positive perturbation from A1, reducing it further to less than the smallest positive gap \(m_i-a_{it}\) on omitted pairs, when there are any. Replacing zero slopes by \(\varepsilon\) lowers each \(m_i\) by at most \(\varepsilon\), and gains have no role in viability. The viable graph is unchanged. On the output support and coverage endpoint classes, minimize the common violation with the original rational data. The perturbed result witnesses violation at most \(\varepsilon\), and A1's determinant separation forces zero optimum. Its decomposition supplies explicit defender mixtures, and omitted zero-prior rows can take a best response at the recovered coverage. [A1, §4](A1-threshold-transport.md#4-transfer-an-exact-positive-coefficient-solver-to-weak-inequalities) · [B2, weak inputs](B2-component-composition.md#preserving-the-component-bound-under-weak-inputs)

## Exact checks and the remaining count

**Fixed-phase edge revisit.** On L1's four-row example, maximizing for the initial assignment \(A,B,C,A\) gives
\((11/122,543/3782,5/61)\). The \(A,C\) ties of rows 1 and 3 determine \(x_A,x_C\), and row 2's \(A,B\) tie determines \(x_B\). Normalization swaps rows 1 and 3, giving \(C,B,A,A\). The next maximum is \((169/618,107/618,1)\). Both former cycle targets increased. A second swap gives \(C,A,A,B\), whose maximum is \((1,1,1)\). Cutting that last segment at budget two uses fraction \(57/160\) and returns \((511/960,449/960,1)\). Exact rational vertex enumeration of each three-coordinate polytope and enumeration of unit row assignments give slope products \(265236,4278,570\) for the three successive normalizations. Uniform row masses make these products order the log costs. The modification takes three positive jumps and no threshold reset. [Instance and published path in L1](L1-published-algorithm.md#exact-edge-revisit-instance)

**Exponentially many possible tight cycles with fixed \(B,z\).** Take targets \(t_0,\ldots,t_m\), two rows for each link \((t_{j-1},t_j)\), and one closing row. A link row with offset \(e\in\{0,2^{-j-2}\}\) has utilities \(e-x_{j-1}\) and \(-x_j\) on that link. The closing row has utilities \(-x_0\) and \(1/4-2x_m\). All other utilities are \(-4-x_t\). Use equal positive priors. Assign each positive-offset row to its left target, each zero-offset row to its right target, and the closing row to \(t_m\). Every column total \(z_t\) is positive. Set \(\beta_t=1/z_t\).

Choose one offset \(e_j\) per link, write \(W=\sum_j e_j\), and take

\[
 x_j=\tfrac14+W+\sum_{\ell>j}e_\ell\qquad(0\le j\le m).
\]

All coverages are strictly inside the box. At link \(j\), the chosen row ties because \(x_{j-1}=x_j+e_j\). The positive-offset row always weakly prefers the left target, and the zero-offset row always weakly prefers the right one. The closing row ties because \(2x_m=x_0+1/4\). The very same assignment is therefore an equilibrium attack flow at all \(2^m\) vectors, and every defender score is one. Each vector has its own tight gain-two cycle through the chosen rows and closing edge, with distinct root value \(x_0=1/4+2W\). These are intermediate equilibria for their respective coverage sums. With independently chosen margins each cycle can be oriented as a negative residual cycle by assigning each chosen link row left and the closing row to \(t_m\).

The explicit payoff table and binary offsets use polynomially many bits in \(m\), so the static pool is superpolynomial in input length. At the common margins, tightness alone does not supply the positive reverse allocations along the chosen cycle. The example certifies the same support through different price vectors. In B3f's separate family, every budget in the lower-bound range lies in the same fixed-margin stretch, and a superpolynomial number of distinct flows is necessary. The cycle-consumption lemma then gives a superpolynomial number of cycles actually consumed by the greatest jumps. [Forced flow switches](B3f-forced-flow-switches.md) · [Compare the fixed-matching weight count in Arunachaleswaran, Barman and Rathi, §4.1](https://arxiv.org/pdf/1807.04163#page=14)
