# B3e · A superpolynomial path for fixed-order resource continuation

**Theorem.** Fix the target order used to select the first eligible seed in Algorithm 3 of Li, Conitzer and Korzhyk. There are rational Bayesian simple security games on which the continuation takes at least $n^{\Omega(\log n)}$ successful outer iterations, where $n$ is both the number of targets and the number of types. In terms of explicit binary input length $L$, the bound is $L^{\Omega(\log L)}$. The games have one defender resource, uniform type priors, unit defender gains, and strictly positive attacker loss slopes. The initial attack assignment, every target's attack load, and the defender threshold stay fixed through termination. During the interval responsible for the bound, every target is reachable from the chosen seed. [Exact continuation in L2](L2-exact-arithmetic-audit.md#state-and-exact-steps) · [Li, Conitzer and Korzhyk, Algorithms 1–3](https://arxiv.org/pdf/1602.01896#page=7)

## A family of separated path winners

Take an integer $h\ge4$, $m=\lfloor\log_2 h\rfloor$, and $U=(h^2)^{m+1}$. Gajjar and Radhakrishnan construct a layered directed acyclic graph with a source and a sink and rational affine edge weights $w_e(\lambda)$. They give $K=h^m$ disjoint positive-length intervals inside $[0,U]$. Each interval has its own source–sink path, and on the entire interval every competing path costs at least one more. The coefficient numerators and denominators have $O((\log h)^3)$ bits. These properties come from the interval construction in §3.1, Lemma 14(iii),(vi), and the choice $B=1,D=0$ in the proof of Theorem 1. The construction there has at most $6h^8+1$ vertices including the added sink. [Gajjar and Radhakrishnan, §§3.1–3.2](https://arxiv.org/pdf/1811.05115#page=12)

Discard vertices outside source–sink paths. Subdivide each remaining arc into an arc with its old weight and an arc of weight zero. Prepend a chain of $h$ zero-weight arcs to the source. This gives a simple DAG with source $o$, sink $t$, and $h\le n\le h^{O(1)}$ vertices, all reachable from $o$. Complete paths correspond bijectively and their costs agree. Number the vertices in topological order with $o$ first.

Use the source-coverage parameter $s$ in the interval

\[
J=[1/(4n),1/(2n)],\qquad \lambda=U(4ns-1).
\]

Write $W_e(s)=a_e s+b_e=-w_e(\lambda)$. In the rescaled intervals the distinguished paths now maximize the sum of the $W_e$ with gap at least one. Let $M\ge1$ be the smallest power of two bounding every $|a_e|,|b_e|$. Both coefficients and $M$ have $O((\log h)^3)$ bits, since $\log U=O((\log h)^2)$.

## From a path sum to affine composition

Put $\varepsilon=1/(128n^2 M^2)$ and define increasing affine maps

\[
F_e(y)=g_e y+\varepsilon b_e,\qquad g_e=1+\varepsilon a_e>0.
\]

For a directed path $P$, let $F_P$ apply its maps in traversal order. Uniformly over all paths and $0\le s\le1$,

\[
 |F_P(s)-s|\le 4n\varepsilon M,\qquad
 \left|F_P(s)-s-\varepsilon\sum_{e\in P}W_e(s)\right|
 \le4n^2\varepsilon^2 M^2.
\]

Indeed, for the first $j$ edges let $D_j=F_{P[1:j]}(s)-s$. It starts at zero and obeys

\[
D_j=D_{j-1}+\varepsilon W_{e_j}(s)+\varepsilon a_{e_j}D_{j-1}.
\]

Since $|W_e(s)|\le2M$, this gives $|D_j|\le 2j\varepsilon M(1+\varepsilon M)^{j-1}\le 4n\varepsilon M$. Summing the last terms gives the second bound. Thus on each designated interval its winning path beats every rival under composition by at least $\varepsilon-8n^2\varepsilon^2 M^2>\varepsilon/2$. The same rational $\varepsilon$ works on all the intervals.

Let $r_v\in\{0,\ldots,n-1\}$ be the topological rank and $\delta_v=r_v/(16n^2)$, with $\delta_o=0$. Shift the affine map on $e=(u,v)$ to

\[
 H_e(x)=F_e(x+\delta_u)-\delta_v=g_e x+c_e.
\]

For $x\in[0,1]$, its increment over $x$ is at most $3\varepsilon M-(\delta_v-\delta_u)<0$. In particular $c_e<0$. The shifts cancel along a source–$v$ path, giving $H_P(s)=F_P(s)-\delta_v$. For any such path and $s\in J$,

\[
 H_P(s)\ge s-4n\varepsilon M-\delta_v
 \ge \frac{1}{4n}-\frac{1}{32n}-\frac{1}{16n}>0.
\]

Thus the shifted maps retain the separated winners at the sink, and every source path has positive value on $J$.

## The game and its unique flow

Use one type and one target per vertex. Set the defender payoffs to zero when uncovered and one when covered, and give each type prior $1/n$. Type $u$'s payoff at its own target is $-x_u$. On a DAG arc $e=(u,v)$, give type $u$ payoff $(c_e-x_v)/g_e$ at target $v$. At all other targets $v\ne u$, use payoff $-2-x_v$. The uncovered and covered payoffs are the values of these affine functions at zero and one. The own target is best precisely when every outgoing inequality

\[
 x_v\ge H_e(x_u)
\]

holds. Off-graph targets are strictly worse throughout the unit box. At zero coverage each type strictly prefers its own target because $c_e<0$. Initialization is therefore forced.

If the diagonal assignment is feasible at a coverage, it is the unique flow on best responses with the current uniform row and column totals. At each vertex, its total off-diagonal outflow equals its total off-diagonal inflow after subtracting its diagonal entry from the two margins. These off-diagonal flows form a nonnegative circulation on a DAG, hence are all zero. Algorithm 2 returns the same diagonal every time these inequalities hold. All defender scores are $1/n$, and before a target reaches its cap every target is in the open defender boundary. Relabel the vertices so that the prescribed first target is $o$.

## What Algorithm 3 traces

For $0\le s\le1$, define $X_o(s)=s$, and in topological order put

\[
 X_v(s)=\max\bigl(0,\max_{e=(u,v)} H_e(X_u(s))\bigr)\quad(v\ne o).
\]

These are the componentwise least nonnegative coverages satisfying the DAG inequalities at source coverage $s$. Since the maps increase and $H_e(0)<0$, induction gives

\[
 X_v(s)=\max\bigl(0,\max_{P:o\leadsto v} H_P(s)\bigr).
\]

In particular $X(0)=0$, and each coordinate is convex, nondecreasing and piecewise affine with finitely many pieces. The constant coverage vector with value $s$ satisfies all comparisons since $H_e(s)<s$. Thus $X_v(s)\le s$. The total coverage increases continuously and strictly from zero to at least one as $s$ ranges up to one. At its unique unit-budget endpoint the algorithm can terminate. Before that endpoint every target is below cap, and throughout $J$ total coverage is at most $1/2$.

At $X(s)$, with $s$ before the unit-budget endpoint, every seed is eligible. From target $u$ the residual graph goes to its own type along a reverse edge of cost zero. From that type it reaches a different target $v$ just when the DAG comparison on $e=(u,v)$ is tight, at cost $\log(1/g_e)$. The redundant own forward edge, if included, has cost zero. Therefore the rate from the first seed $o$ is $\gamma_o=1$, and $\gamma_v$ is the maximum product of the $g_e$ along a tight path from $o$ to $v$, with zero for an unreachable target. This also equals the right derivative of $X_v(s)$. Differentiating the finite maximum in topological order takes the largest $g_e X'_{u,+}(s)$ over tight incoming comparisons, with zero available at the floor. On $J$, each coordinate is positive, so its maximizing source path is tight edge by edge. Thus all targets are residual-reachable throughout the counted interval. [Li et al., Algorithm 3, lines 2–25](https://arxiv.org/pdf/1602.01896#page=7)

The algorithm's entire straight step follows $X$. For each positive-rate target, a tight path attaining its rate gives an affine path formula with current value $X_v(s)$ and slope $\gamma_v$. If the rate is zero then $X_v(s)=0$, since a positive value has a tight source path. The ray $X(s)+d\gamma$ remains feasible until the first new tie, cap, or budget event. Leastness gives $X(s+d)\le X(s)+d\gamma$ on the feasible ray. The attaining paths and the zero floors supply the opposite inequality there. Starting at zero, this proves the claim by induction for every step, including simultaneous ties.

A nonterminal step ends as an initially slack comparison closes at positive speed $g_e\gamma_u-\gamma_v>0$. The right derivative of $X_u$ at the endpoint is at least its old slope by convexity, so the new tight comparison forces the right derivative of $X_v$ to exceed $\gamma_v$. Each such event is a genuine kink of a coordinate. Finiteness of the path envelopes rules out an accumulation of events before the budget. Algorithm 4 is never called.

## Count and scope

On the interior of each of the $K$ rescaled intervals the sink coordinate is the affine formula of its unique winning path. These formulas are pairwise distinct, because a path with an identical formula to another path could never strictly beat it. Every interval overlaps the interior of some successful step. The sink is affine as a function of $s$ on each step, so a single step cannot cover positive-length portions of two designated intervals. This gives at least $K=h^{\lfloor\log_2 h\rfloor}$ successful iterations.

The shifts, reciprocal gains, and both endpoint payoffs have $O((\log h)^3)$ bits per entry. The explicit table and priors use $L=O(n^2(\log n)^3)$ bits. Since $h\le n\le h^{O(1)}$, this proves both lower bounds stated above.

**Exact check.** Take three two-edge paths $o\to i\to t$, in vertex order $o,1,2,3,t$, with additive maximization weights $(\lambda+3,-2\lambda-1)$, $(\lambda-2,-\lambda+2)$ and $(-\lambda+1,2\lambda-7)$ along the respective paths. Applying the construction with $n=5$ and $U=8$ gives seven continuation steps when the source is first. The unique winners at $\lambda=1/2,4,15/2$ pass through vertices $1,2,3$ respectively. The exact rational replay agrees with the path recurrence at every step endpoint and midpoint. [Exact replay code](../experiments/b3_fixed_load_search.py)

On every game in this family, choosing the sink first spends the whole budget on that target in one step. The greatest fixed-flow jump in B3a also completes in one step, since the all-ones point satisfies every DAG inequality and interpolation gives uniform coverage $1/n$. The general complexity of finding an exact equilibrium remains open. [B3a, fixed-flow extension](B3a-fixed-flow-jump.md) · [Conitzer, open problem](https://arxiv.org/pdf/2610.08796)
