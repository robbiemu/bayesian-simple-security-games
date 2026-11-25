# A4m · An exact block algorithm for the general market contraction

**Result using the ARRIVAL preprint's block solver.** Let $d$ be the number of buyer and good coordinates and $L$ the full binary input length. Exact affine-market search takes $2^{O(\sqrt d\log(2+L))}$ bit time by discretizing A4f as a map with integer unit increments and recursively solving blocks. The A4c supply adjustment gives the same bound for minimum prices. The existing game reduction and weak-sign repair give $2^{O(\sqrt{n+k}\log(2+L))}$ for a supplied security game with $n$ targets and $k$ positive-prior types. The earlier arrangement bound can still be preferable for unbalanced numbers of targets and types. [A4f node map](A4f-handicap-formulation.md#eliminating-flow-variables) · [Ghorbani, Lopes and Mnich, Theorem 1.2](https://arxiv.org/html/2610.28241v1#S1.Thmtheorem1.2) · [Game reduction to market clearing](A4c-any-clearing-equilibrium.md#transfer-to-the-exact-game)

## Round transfers while preserving unit increments

Write A4f's signed node vector as $h=L_0+W z$ with a common width $W$, $z\in[0,1]^d$, and $L_{0,i}=0$ for buyers, $L_{0,j}=-W$ for goods. Let $q=1-a\varepsilon$, $\rho=a/\varepsilon$ for its rational step $a$. Put $c_v=((q-1)L_{0,v}-a g_v)/W$ and $\beta_e=\rho(b_e-L_{0,i}+d_eL_{0,j})/W$ for $e=ij$. The map in normalized coordinates is the coordinatewise clip of
\[
 q z_v+c_v+\sum_e A_{ve}[\beta_e-\rho z_i+\rho d_e z_j]_+,
 \qquad A_e=e_i-e_j .
\]
It is a strict $\ell_1$ contraction of factor $q$. The A4f step-size condition ensures that $q$ exceeds or equals the total incident share of each node below. Shrinking $a$ by a further polynomial-bit factor would also suffice.

At a buyer, split its amount $z_i$ into $\rho z_i$ for each incident edge, a self share $(q-\sum_{e\ni i}\rho)z_i$, and a leakage share $(1-q)z_i$. At a good use shares $\rho d_e z_j$ on its edges, with the corresponding self and leakage shares. If an edge receives shares $s,t$ from its buyer and good, respectively, its two outputs are
\[
 \bigl(\max(s,\beta_e+t),\ \min(t,s-\beta_e)\bigr).
\]
These have sum $s+t$ and are nondecreasing in both inputs. Merge each node's outputs and self share, add $c_v$, and clip. This reproduces the normalized map exactly.

For the lattice $[0,N]^d\cap\mathbb Z^d$, split each integer amount according to the same rational proportions. Use a balanced binary tree over the output shares. At a split, the left child takes the floor of its proportion of the current count and the right child takes the remainder. A zero-weight subtree receives zero and passes zero to all its leaves. A one-unit increase routes exactly one unit to one leaf. Each leaf error from its unrounded share is at most the tree depth. In the edge comparator and node addition use the nearest integers to $N\beta_e$ and $Nc_v$. A one-unit increase into a comparator increases exactly one output by one because its outputs are integral, monotone and conserve their sum. Signed intermediate outputs do not affect this argument. The merges, leakage and final clipping preserve the property that a one-unit increase in an input increases at most one output by one. Thus the resulting integer self-map $U_N$ is monotone with unit increments, and is nonexpansive in $\ell_1$ on the lattice.

For fixed $\beta$, the comparator is also nonexpansive in $\ell_1$ for real inputs. Apply monotonicity and conservation to the coordinatewise maximum and minimum of two inputs. Changing $\beta$ by at most $1/2$ after scaling causes at most one additional unit of $\ell_1$ error. With $E$ viable edges and maximum degree $\Delta$, let $K=\lceil\log_2(\Delta+2)\rceil$. Split errors, comparator shifts and node constants give the uniform bound
\[
 \|U_N(X)-N F(X/N)\|_1
 \ \le\ C=(2E+d)K+E+d
 \qquad (X\in[0,N]^d\cap\mathbb Z^d).
\]
Here $F$ is the normalized real map. All integer and rational operations in a call have polynomial bit length in the input and $\log N$. Simple separate rounding of the real coordinate outputs need not preserve unit increments. [Exact lattice replay](../experiments/a4m_lattice_replay.py)

## Eliminate blocks and recover the market exactly

Here is the conditional-map fact needed by the preprint's least-fixed-point algorithm. Split the integer coordinates into boundary $B$ and interior $I$. Pin $x$ on $B$, and let $y(x)$ be the least fixed point on $I$. Monotonicity and iteration from zero give $y(x)\le y(x')$ for $x\le x'$. Define $H(x)=U_{N,B}(x,y(x))$. For such a pair, $\ell_1$ nonexpansiveness of $U_N$ gives
\[
 \|H(x)-H(x')\|_1+\|y(x)-y(x')\|_1
 \ \le\ \|x-x'\|_1+\|y(x)-y(x')\|_1 .
\]
After cancellation, $H$ has unit increments. Its least fixed point $x_0$ lifts to a fixed point $(x_0,y(x_0))$. For any full fixed point $(x,y)$, $y(x)\le y$ implies $H(x)\le x$. Iteration from zero gives $x_0\le x$ and then $y(x_0)\le y$. This proves that the lift is the least full fixed point.

Partition into blocks of size at most $k$. Use the solver from Theorem 1.2 for $H$ and evaluate its interior calls recursively. Theorem 1.2 uses $O(k^3\log(kN+2))$ oracle evaluations and $(2k\log(N+2))^{O(k)}$ overhead for a lattice map with unit increments. Each level uses one additional interior solve to lift the answer. All levels use the same cap $N$. With $O(d/k)$ levels, the cost is $2^{O((k+d/k)\log(2+L))}$ when $\log N$ is polynomial in $L$. The choice $k=\lceil\sqrt d\rceil$ gives the stated bound. The cube-root bound for switch graphs in the same paper uses a separate graph-specific base solver. [Block oracle and overhead](https://arxiv.org/html/2610.28241v1#S1.Thmtheorem1.2) · [How the graph-specific bound is obtained](https://arxiv.org/html/2610.28241v1#S9)

For **any** lattice fixed point $X$, the original normalized contraction gives distance at most $C/(N(1-q))$ to the true fixed point. In the original signed coordinates this is at most $WC/(N(1-q))$. The regularized complementarity basis in A4d gives a computable polynomial-bit denominator bound $Q_h$ for each signed coordinate. This is a bound on the regularized solution, separate from the original support-repair gap. Choose dyadic $N> 2WCQ_h^2/(1-q)$ and recover each original signed coordinate by continued fractions. This chooses $N$ with polynomial binary length even if quantities or slope ratios have large numerical values. Recover the regularized flows from the hinge equation, then apply the A4d support repair to get exact clearing, and A4c to select the original minimum when required. The determinant and precision arguments for the adaptive game-to-market calls have uniform polynomial bit size. [A4d exact repair](A4d-p-matrix-complementarity.md#one-exact-p-lcp-call) · [A4c exact transfer to the game](A4c-any-clearing-equilibrium.md#transfer-to-the-exact-game)

## Continuous variant and the scope of the comparison

The same bound follows from the continuous contraction and the paper's deterministic deep-point routine. For exact interior solutions of a strict contraction with factor $q$, additivity gives the sharper inequality
\[
 \|H(x)-H(x')\|_1+(1-q)\|y(x)-y(x')\|_1\le q\|x-x'\|_1.
\]
It requires neither monotonicity nor lattice rounding. Write $\gamma=1-q$ and let $t$ be the desired boundary location accuracy. Use a dyadic candidate grid with $\ell_1$ rounding error at most $b=\gamma^2t/128$, and evaluate $H$ to error at most $b$. At a query $w$, let $v$ be the approximate value. If $\|v-w\|_1\le\gamma t/2$, the residual bound gives location error at most $t$. Otherwise the distance $D$ from $w$ to the boundary fixed point exceeds $\gamma t/5$. For a closest grid point $z$ to that fixed point,
\[
 \|z-v\|_1-\|z-w\|_1\le-\gamma D+3b<0.
\]
Thus $z$ survives removal of the $\ell_1$ half-space through $w$ in direction $w-v$. The defining distance inequality of that half-space would imply $\|z-w\|_1\le\|z-v\|_1$. The removed set is a union of sign boxes of the grid. After $r$ cuts there are at most $(2r+1)^k$ boxes, because each probe adds at most two intervals in each coordinate. The deterministic deep point removes a $1/(2(k+1))$ fraction each round, so $O(k^2\log N)$ calls suffice in $k$ dimensions. To obtain full location error $e$, use $t=\gamma e/2$ and solve the final interior problem to error at most $e/2$. The displayed conditional inequality gives $\|x-x^*\|_1+\|y(x)-y(x^*)\|_1\le\|x-x^*\|_1/\gamma$. During search, solve each interior problem and evaluate the map to error $b/2$ apiece. This adds only $O(\log(1/\gamma)+\log d)$ precision bits per level. Cramer's bound again yields exact recovery for A4f. [Half-space cuts and Lemma 8.16](https://arxiv.org/html/2610.28241v1#S8)

The integer circuit is a conservative flow of unit increments, but an ordinary rotor network need not implement the comparator efficiently. In a terminating network with $s$ binary rotors, the total sent to a specified terminal set differs from a linear function of the source injections by at most $s/2$. To see this, take the harmonic success probabilities of the fair walk. The two arc totals of any rotor differ by at most one, so its correction to the harmonic balance is at most $1/2$ in absolute value. Sum over rotors. A one-edge A4f restriction with $d=1$, $b=3/2$, $m=c=1$, $a=\varepsilon/4$ and signed good coordinate $-1/2$ has buyer output $(1-\varepsilon^2/4)u-\varepsilon/4+[1-u]_+/4$. At $u=1/2,1,3/2$ its second difference is $1/8$. A direct terminal-count encoding at $N$ units of scale therefore needs $s\ge N/16$, up to constant rounding error, even allowing a fixed affine correction. This concerns direct terminal counts. An odometer or encoded-output reduction has different requirements. [Rotor discrepancy method](https://arxiv.org/abs/0904.4507)

Robert Thomas Collins directed the investigation. GPT-6.2 Astra derived the integer split and compare-exchange realization, the conditional cancellation argument, and the continuous adaptation, building on the A4f formulation and the block solver of Ghorbani, Lopes and Mnich. The coordinating Codex session checked their transfer and the bit and dimension counts. The result uses the October ARRIVAL block solver independently of the November max-norm theorem.
