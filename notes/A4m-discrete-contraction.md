# A4m · An exact block algorithm for the general market contraction

**Result using the October ARRIVAL preprint.** Let $L$ be the binary input length and $\tau$ the minimum vertex cover size of the buyer–good graph used by A4f. Exact clearing and minimum prices take $2^{O(\sqrt{\tau}\log(2+L))}\mathrm{poly}(L)$ bit time. The game reduction gives $2^{O(\sqrt{\min(n,k)}\log(2+L))}\mathrm{poly}(L)$ for $n$ targets and $k$ positive-prior types. For explicitly tabulated games, $nk=O(L)$, so the latter is at most $2^{O(L^{1/4}\log(2+L))}\mathrm{poly}(L)$. [A4f node map](A4f-handicap-formulation.md#eliminating-flow-variables) · [Ghorbani, Lopes and Mnich, Theorem 1.2](https://arxiv.org/html/2610.28241v1#S1.Thmtheorem1.2) · [Game reduction to market clearing](A4c-any-clearing-equilibrium.md#transfer-to-the-exact-game)

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

Partition $r$ remaining coordinates into blocks of size at most $b$ and evaluate the conditional map recursively, with one additional interior solve per invocation to lift the answer. In a block, Theorem 1.2 uses $O(b^3\log(bN+2))$ oracle calls and $(2b\log(N+2))^{O(b)}$ additional time. All calls use the same cap. For $\log N$ polynomial in $L$, the total is $2^{O((b+r/b)\log(2+L))}\mathrm{poly}(L)$ with a polynomial-time interior oracle at the bottom. The choice $b=\lceil\sqrt r\rceil$ gives the square-root exponent. Applying this directly to all $d$ variables gives the original $\sqrt d$ bound. The cube-root bound in the same paper uses a separate switch-graph solver. [Block oracle and overhead](https://arxiv.org/html/2610.28241v1#S1.Thmtheorem1.2) · [Switch-graph solver](https://arxiv.org/html/2610.28241v1#S9)

### Pin a vertex cover

Use a bipartite matching to compute a minimum vertex cover $B$ of the graph used by the rounded circuit. Each node splits its own count and each comparator reads only its two endpoints, so an output depends only on the node's own input and its neighbors. For a fixed assignment on $B$, the coordinates outside $B$ are independent. For each such coordinate let $g(t)$ be its scalar update on $\{0,\ldots,N\}$. The integer difference $g(t)-t$ starts nonnegative, ends nonpositive, and decreases by zero or one at each step. The first $t$ with $g(t)\le t$ is therefore the least fixed point, including when there is a plateau. Binary search finds it in $O(\log(N+2))$ calls. This solves the whole interior exactly in polynomial bit time.

The conditional map on $B$ has unit increments by the cancellation argument. Run the block algorithm on $r=|B|=\tau$ and lift the answer through the independent solves. An empty cover needs only the scalar solves. A cover is computed from the circuit graph before any equilibrium support is known. Either side of the graph is a cover, so every market call in the game reduction uses at most $\min(n,k)$ boundary coordinates. The weak-sign repair and exact budget recovery use only polynomially many polynomial-bit calls with these same counts. [Vertex-cover argument by ChatGPT 6 Pro](https://github.com/robbiemu/bayesian-simple-security-games/pull/12#issuecomment-7151840713) · [Exact mixed-cover replay](../experiments/a4m_lattice_replay.py)

### Exact recovery

For **any** lattice fixed point $X$, the original normalized contraction gives distance at most $C/(N(1-q))$ to the true fixed point. In the original signed coordinates this is at most $WC/(N(1-q))$. The regularized complementarity basis in A4d gives a computable polynomial-bit denominator bound $Q_h$ for each signed coordinate. This is a bound on the regularized solution, separate from the original support-repair gap. Choose dyadic $N> 2WCQ_h^2/(1-q)$ and recover each original signed coordinate by continued fractions. This chooses $N$ with polynomial binary length even if quantities or slope ratios have large numerical values. Recover the regularized flows from the hinge equation, then apply the A4d support repair to get exact clearing, and A4c to select the original minimum when required. The determinant and precision arguments for the adaptive game-to-market calls have uniform polynomial bit size. [A4d exact repair](A4d-p-matrix-complementarity.md#one-exact-p-lcp-call) · [A4c exact transfer to the game](A4c-any-clearing-equilibrium.md#transfer-to-the-exact-game)

## Recover a clearing from the integer transfers

The October route also works with regularization only on edge flows. Use the same split and comparison circuit with $q=1$, so there is no node decay. Write $\Theta=2\lceil\log_2(\Delta+2)\rceil+1$. Choose an integer width $W$ at least $1$, every $1+b_e$ and $b_e/d_e$, and every $m_i+\Theta$. Take an integer $\Lambda\ge1$ at least each buyer degree and each sum of incident slopes at a good. Use $\rho=1/\Lambda$ and $a=\varepsilon/\Lambda$, with $\varepsilon$ the reciprocal of an integer chosen below. Let $T$ clear the denominators of the masses and capacities. Set $N=TW/a$, an integer of polynomial bit length. Every comparator still preserves unit increments, so the same solver on a vertex cover finds a fixed point.

Use $X_i$ for a buyer count and $Y_j$ for a good count, giving $u_i=WX_i/N$ and $p_j=W(1-Y_j/N)$. The integer transfer at edge $e=ij$ is
\[
 k_e=[\operatorname{round}(N\beta_e)+t_e-s_e]_+,\qquad
 \beta_e=\rho(b_e-d_eW)/W,
\]
where $s_e,t_e$ are the split buyer and good shares. With $q=1$ the self and edge shares add to the entire input. Thus the buyer and good updates are
\[
 \operatorname{clip}_{[0,N]}\left(X_i+\sum_{e\ni i}k_e-Tm_i\right),
 \qquad
 \operatorname{clip}_{[0,N]}\left(Y_j-\sum_{e\ni j}k_e+Tc_j\right).
\]
The node constants are integral by the choice of $T$.

The comparator argument differs from $(T/\varepsilon)(b_e-u_i-d_e p_j)$ by at most $\Theta$, from two port errors and the rounded offset. At $X_i=N$ the argument is at most $-T/\varepsilon+\Theta\le0$ because $W\ge b_e+1$ and $1/\varepsilon\ge\Theta$. At $Y_j=0$, the good port is zero and $\beta_e\le0$, so again $k_e=0$. Hence the artificial upper bounds on $u_i$ and $p_j$ cannot conceal excess load.

At any lattice fixed point, the flow $x_e=k_e/T$ is therefore exactly feasible for the original masses and capacities. Its buyer and good inequalities are equalities whenever $u_i>0$ or $p_j>0$, respectively. Integer quantities allow $T=1$, so this flow is integral. In a unit market it gives a matching to real goods, with unmatched buyers assigned outside. Write $w_e=u_i+d_e p_j-b_e$. The same comparator error bound gives $w_e\ge-\varepsilon(x_e+\Theta/T)$ on all edges and $w_e\le\varepsilon\Theta/T$ on positive-flow edges. Since $x_e\le m_i$ and $m_i+\Theta\le W$, these violations are bounded by $\varepsilon W$.

Keep the exact flow and solve one LP in $d+1$ variables $(u',p',t)$, minimizing $t$ in $[0,1]$. Require $0\le u',p'\le W$, preserve every zero utility and price of the lattice point, and impose $u'_i+d_e p'_j-b_e\ge-t$ with the reverse bound $\le t$ on every edge with $k_e>0$. Clearing denominators in the common list of possible rows gives a maximum integer coefficient $H\ge1$. Set $Q_p=(d+1)!\,H^{d+1}$ and $\varepsilon=1/(4WQ_p)$. A positive optimum of any such LP is at least $1/Q_p$ by compactness and the determinant bound. The sampled node values show that the optimum is at most $\varepsilon W<1/Q_p$, so it is zero. The flow clears at the repaired prices and utilities since the LP keeps its positive edges tight and retains all zeros at underfilled nodes. Exact rational LP and this mesh construction both use polynomial bit time. A4c still recovers the original componentwise minimum with the usual supply enlargement and circulation. [Support-gap method](A4d-p-matrix-complementarity.md#one-exact-p-lcp-call) · [Supply enlargement](A4c-any-clearing-equilibrium.md#one-call-at-enlarged-capacities)

This proof uses exact integer transfers and a price-and-utility LP. The strictly contractive variant above also gives the exact regularized point, which is used by the continuous and max-norm routes.

## Continuous variant and the scope of the comparison

The same bound follows from the continuous contraction and the paper's deterministic deep-point routine. For exact interior solutions of a strict contraction with factor $q$, additivity gives the sharper inequality
\[
 \|H(x)-H(x')\|_1+(1-q)\|y(x)-y(x')\|_1\le q\|x-x'\|_1.
\]
It requires neither monotonicity nor lattice rounding. Write $\gamma=1-q$ and let $t$ be the desired boundary location accuracy. Use a dyadic candidate grid with $\ell_1$ rounding error at most $b=\gamma^2t/128$, and evaluate $H$ to error at most $b$. At a query $w$, let $v$ be the approximate value. If $\|v-w\|_1\le\gamma t/2$, the residual bound gives location error at most $t$. Otherwise the distance $D$ from $w$ to the boundary fixed point exceeds $\gamma t/5$. For a closest grid point $z$ to that fixed point,
\[
 \|z-v\|_1-\|z-w\|_1\le-\gamma D+3b<0.
\]
Thus $z$ survives removal of the $\ell_1$ half-space through $w$ in direction $w-v$. The defining distance inequality of that half-space would imply $\|z-w\|_1\le\|z-v\|_1$. The removed set is a union of sign boxes of the grid. After $r$ cuts there are at most $(2r+1)^k$ boxes, because each probe adds at most two intervals in each coordinate. The deterministic deep point removes a $1/(2(k+1))$ fraction each round, so $O(k^2\log N)$ calls suffice in $k$ dimensions. To obtain full location error $e$, use $t=\gamma e/2$ and solve the final interior problem to error at most $e/2$. The displayed conditional inequality gives $\|x-x^*\|_1+\|y(x)-y(x^*)\|_1\le\|x-x^*\|_1/\gamma$. During search, solve each interior problem and evaluate the map to error $b/2$ apiece. This adds only $O(\log(1/\gamma)+\log d)$ precision bits per level. Cramer's bound again yields exact recovery for A4f. The continuous search uses the deterministic deep point shared with the lattice route. Its stopping test uses the contraction residual directly, bypassing the discrete selection step for the least point. [Ghorbani, Lopes and Mnich, PDF v1, §8.4, Lemma 8.11, p. 27](https://arxiv.org/pdf/2610.28241v1#page=28)

The integer circuit is a conservative flow of unit increments, but an ordinary rotor network need not implement the comparator efficiently. In a terminating network with $s$ binary rotors, the total sent to a specified terminal set differs from a linear function of the source injections by at most $s/2$. To see this, take the harmonic success probabilities of the fair walk. The two arc totals of any rotor differ by at most one, so its correction to the harmonic balance is at most $1/2$ in absolute value. Sum over rotors. A one-edge A4f restriction with $d=1$, $b=3/2$, $m=c=1$, $a=\varepsilon/4$ and signed good coordinate $-1/2$ has buyer output $(1-\varepsilon^2/4)u-\varepsilon/4+[1-u]_+/4$. At $u=1/2,1,3/2$ its second difference is $1/8$. A direct terminal-count encoding at $N$ units of scale therefore needs $s\ge N/16$, up to constant rounding error, even allowing a fixed affine correction. This concerns direct terminal counts. An odometer or encoded-output reduction has different requirements. [Rotor discrepancy method](https://arxiv.org/abs/0904.4507)

Robert Thomas Collins directed the investigation. GPT-6.2 Astra derived the integer split and compare-exchange realization, the conditional cancellation argument, and the continuous adaptation, building on the A4f formulation and the block solver of Ghorbani, Lopes and Mnich. The coordinating Codex session checked their transfer and the bit and dimension counts. The result uses the October ARRIVAL block solver independently of the November max-norm theorem.
