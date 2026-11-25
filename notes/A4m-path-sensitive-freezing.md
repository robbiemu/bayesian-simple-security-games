# A4m · Exact price search from a path bound on the frozen assignment

**Conditional polynomial-time result.** A polynomial-size linear program can certify that A4a's frozen transferable-utility price map is nonexpansive in the sup norm of the original prices. The November 24 max-norm oracle theorem then gives a deterministic polynomial-bit-time solver for the certified market. The certificate permits equality and arbitrary binary masses and capacities. It can pass with many heterogeneous rows and columns even when A4a's older column condition fails under every scaling. [A4a frozen assignment and recovery](A4a-near-factorized-slopes.md) · [November manuscript, approximation in max norm](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Strongly-polynomial-linear-programming-November-24-2026/build/contractions.tex#L1-L41)

## The path inequality

Start with prices above reserve, utilities above outside and net bids $b_{ij}$. An edge with $b_{ij}\le0$ can be omitted because its only possible best tie at nonnegative prices can be assigned outside. Scale buyer $i$'s utility by $x_i>0$, and write the scaled price of good $j$ as $\beta_j p_j$, $\beta_j>0$. The slope in these coordinates is $s_{ij}=d_{ij}x_i/\beta_j$. Define
\[
 a_{ij}=d_{ij}x_i-\beta_j,\qquad
 B_{ij}(t)=x_i b_{ij}-a_{ij}t_j .
\]
At physical trial quotes $t$, let $Q(t)$ be the vector of least prices in the ordinary unit-slope market with bids $B(t)$, original quantities and zero floors. The physical price map is $F_j(t)=Q_j(t)/\beta_j$. Two rational LPs suffice to compute $Q(t)$ exactly by optimizing the ordinary assignment and then selecting its least dual prices. [Transferable-utility oracle and strict Hall test](A4a-near-factorized-slopes.md#normalization-and-a-transferable-utility-oracle)

Fix $t,t'$ and put $h=Q(t)-Q(t')$. From a real good $j$ with $h_j>0$, there is a simple directed alternating path ending at outside or at a good with $h_k\le0$. Its forward arcs from a good to a buyer use demand at $Q(t)$ and its arcs back to a good or outside use positive assigned flow at $Q(t')$. In fact, any nonempty reached set $S$ of positive-difference goods has strictly more neighboring buyer mass than its total capacity, by the strict Hall test at $Q(t)$. The other clearing cannot allocate all this mass within $S$. Hence the search can reach a new good or outside. Taking a simple path in the bipartite graph makes both its buyers and goods distinct.

For a hop $j\to i\to k$, let the outside option have price and bid zero. Comparing the two best-option inequalities gives
\[
 h_j-h_k
 \ \le\ [B_{ij}(t)-B_{ij}(t')]-[B_{ik}(t)-B_{ik}(t')]
 \ =\ -a_{ij}(t_j-t_j')+a_{ik}(t_k-t_k') .
\]
Sum down the path and drop the nonpositive endpoint $h_k$. The coefficient at the initial real good and at a real terminal good has magnitude $|a_{ij}|$ for its sole path buyer. At an interior good $k$, the two coefficients combine before taking absolute values, giving $|a_{ik}-a_{i'k}|$ for its two path buyers. Swapping the markets handles the negative difference at $j$.

## An LP to certify the whole map

For each starting good $j$, bound the largest possible sum of these path coefficients as follows. At each real good $k$ allow an option with one adjacent buyer $i$ and cost $|a_{ik}|$, or with an unordered pair of distinct adjacent buyers $i,i'$ and cost $|a_{ik}-a_{i'k}|$. Give each option a nonnegative LP variable. Use at most one option in total at each good, at most two buyer incidences in total at each buyer, and at most two singleton options in total. At the starting good $j$ allow only singleton options. These inequalities hold on the integral options selected by every simple path, including a path to outside. Let $M_j$ be the optimal total cost of this LP. The path argument proves
\[
 |F_j(t)-F_j(t')|\le (M_j/\beta_j)\,\|t-t'\|_\infty .
\]
Thus the inequalities $M_j\le\beta_j$ certify sup-norm nonexpansiveness.

The factors and bounds can be found simultaneously. Introduce cost upper bounds for each option and impose the two linear inequalities for its absolute value. In the pair case $\beta_k$ cancels from $a_{ik}-a_{i'k}$. For each $j$, require a nonnegative feasible dual for the options LP with dual objective at most $\beta_j$. These are linear constraints in $x,\beta$, the cost bounds and the dual variables. Conversely, if factors satisfying the certificate exist, use the exact costs and LP optimal duals. Everything is homogeneous, so requiring $x_i,\beta_j\ge1$ loses no feasible scaling. The number of options is polynomial in the listed incidence size, and the factor LP has polynomial binary length. A simpler sufficient certificate uses absolute edge weights $|a_{ik}|$ and a degree-two bipartite matching relaxation with degree at most one at the starting good. Splitting the pair options into their two edges proves that this simpler relaxation upper-bounds the options LP.

## Exact recovery and call sizes

For the normalized slopes and bids, A4a gives a rational price box $[0,R]^n$ in scaled units that is invariant under its frozen map. Thus the physical rectangle $\prod_j[0,R/\beta_j]$ is invariant under $F$. Extend the map to a common cube by clipping inputs to that rectangle. Coordinate clipping is sup-norm nonexpansive, and the outputs already lie in the rectangle. A common affine scaling puts the cube in the manuscript's normalization. For an approximate fixed point of the extension, clipping it back cannot increase its coordinate residual, since the map's value lies in the rectangle.

The manuscript takes polynomially many precision queries and polynomial total bit time for a nonexpansive map at binary accuracy. At each query compute the frozen assignment with rational LPs and round the output to the requested dyadics. To obtain scaled-coordinate residual at most A4a's $\tau$, request physical residual at most $\tau/\max_j\beta_j$ after undoing the common cube scaling. All magnitudes and reciprocal tolerances have polynomial bit length. Keep every demand tie detected in the exact frozen market, and invoke A4a's repair LP. Its positive violation gap is determined by the template's binary coefficients, independently of which ties were selected. The retained ties preserve strict Hall at the repaired point. This returns the **least** original price and a clearing allocation, even when the sup-norm factor equals one. [A4a exact repair](A4a-near-factorized-slopes.md#the-contraction-and-exact-recovery)

For a uniform certificate $M_j\le(1-\gamma)\beta_j$, elementary iteration with dyadic rounding already gives polynomial bit time when $1/\gamma$ is polynomial in the input length. The new oracle theorem also handles the boundary $M_j=\beta_j$ and a binary-small strict gap. The market argument uses the manuscript's fixed-point oracle result and ordinary bit-polynomial rational LP. The published Lean scope for rational LP does not certify this oracle theorem. [Manuscript formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/380.md)

## A family separating two certificates

For any $k\ge1$, take $k$ distinguished buyers and $k$ distinguished goods among $17k$ of each. All slopes are one except on designated pairs. For each distinguished buyer choose eight disjoint pairs of ordinary goods, with different pairs also disjoint across buyers, and put slopes $1+\delta,1-\delta$ on each pair, where $\delta=1/(4k)$. Make the transpose construction for each distinguished good and disjoint pairs of ordinary buyers. Set positive bids on all edges. Taking $x_i=\beta_j=1$, every nonzero cost is incident to a distinguished vertex. A degree-two edge bound therefore charges at most $4k\delta=1$, so every starting good passes.

By contrast, take arbitrary row scaling and compare a distinguished buyer to any ordinary buyer on one of the pairs of ordinary goods. The ratio of their two normalized slope ratios is $(1+\delta)/(1-\delta)>(1+\delta)^2$. At least one good in the pair therefore has column maximum divided by column minimum at least $1+\delta$. Its term $1-\min/\max$ in A4a's column condition is at least $\delta/(1+\delta)$. There are $8k$ disjoint pairs, so their contribution alone exceeds one. The transpose argument also applies to reciprocal slopes. Removing a fixed number of vertices destroys only a bounded number of pairs because the pairs are disjoint on ordinary vertices and each distinguished vertex participates in eight pairs. For sufficiently large $k$, the older column tests still fail on the remainder. This separates the two stated certificates, without classifying every alternative solver. [A4a column condition](A4a-near-factorized-slopes.md#a-wider-region-by-a-weighted-euclidean-norm)

Robert Thomas Collins directed the transfer investigation. The GPT-6.2 Astra subagent derived the alternating-path bound and degree-two relaxation. The coordinating Codex session kept the cancellations at interior goods, formulated the joint factor LP, and checked exact recovery and the separating family.
