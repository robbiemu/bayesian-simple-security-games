# B1 · Worst-case augmentation counts by instance class

Counting feasible signatures in strict-payoff Bayesian simple security games gives at most $2^{O(\sqrt{nk}\log(nk+1))}$ outer iterations, where $n$ is the number of targets and $k$ the number of positive-probability types. The bound is polynomial for fixed $n$, fixed $k$, or fixed rank of the comparisons between types that can attack the same target. If every target can be optimal for at most one type, the bound is linear in $n$. These are counts of outer iterations. L2 proves signature non-repetition for a fixed seed order and derives the exact bit-time bound. The question of a polynomial bound in the unrestricted dimensions remains open. [Conitzer, problem statement](https://arxiv.org/pdf/2610.08796) · [Li, Conitzer and Korzhyk, §§2, 3.1 and 6.2](https://arxiv.org/pdf/1602.01896) · [Exact arithmetic and non-repetition proof](L2-exact-arithmetic-audit.md)

## What counts as a state

Write $x_t$ for coverage, $q_{it}$ for prior-weighted attack mass, $p_i>0$ for the prior, $a_{it}$ for the uncovered attack payoff, $d_{it}>0$ for the attacker's loss from coverage and $\beta_t>0$ for the defender's gain. Each row has sum $p_i$ and per-target cap $p_i$. At every equilibrium along the augmentation path, define

$$
 v_i=\max_t(a_{it}-d_{it}x_t),\qquad
 s_t=\beta_t\sum_i q_{it},\qquad
 \lambda=\max_{t:x_t<1}s_t.
$$

The last expression is used only while some target is unsaturated. A player type can assign all its mass to any one target. Consequently every positive $q_{it}$ attains $v_i$, even if one edge carries the whole row. The paper's canonical evader threshold is the **minimum over positively allocated sites**. This makes it exactly $v_i$. Each active edge attains $v_i$, and every remaining edge is inferior. Each row has at least one active edge, so the number of complete signatures is at most $(2^n-1)^k$. In Algorithm 3 a pure type's occupied target is its sole residual predecessor, so its payoff decrease rate is exactly $d_{it}\gamma_t$. For a split row, each positive allocation is below cap and its edge has both residual directions, giving the same equality. This verifies the threshold convention in the actual event calculation. [Li et al., §§2 and 3.1](https://www.cs.cmu.edu/~conitzer/catcherIJCAI16.pdf)

Let $B=\{t:x_t<1,\ s_t=\lambda\}$. Lemma 7 bounds the number of changes of $B$ by $2n$. The proof of Lemma 8 counts whole payoff signatures **resulting from successful calls** of Algorithm 3 within a phase of constant $B$, using non-repetition. Lemma 6 charges a failed call to a subsequent success or a newly tied defender site. The arrangement bounds below invoke that per-phase claim. The disjoint-target proof instead counts individual activation and saturation events directly. [Li et al., §6.2, Lemmas 6–8 and Theorem 5](https://arxiv.org/pdf/1602.01896)

## Counting the signatures two ways

For each type, keep targets in

$$
C_i=\{t:a_{it}\ge L_i\},\qquad L_i=\max_s(a_{is}-d_{is}),\qquad I_t=\{i:t\in C_i\}.
$$

Every coverage vector in the cube gives $v_i\ge L_i$. Conversely, if $t\in C_i$, setting $x_t=0$ and all other coordinates to one makes $t$ a maximizer. This is an exact viability test on the whole cube and a safe pruning test along the augmentation path.

Write $F(H,d)=\sum_{j=0}^{\min(H,d)}2^j\binom Hj$. An arrangement of $H$ affine hyperplanes in dimension $d$ has at most $F(H,d)$ nonempty sign cells, including faces of lower dimension. On adding one hyperplane, each old cell it cuts yields two additional cells. The cut cells inject into the arrangement restricted to that hyperplane. This gives the recurrence $F(H,d)=F(H-1,d)+2F(H-1,d-1)$ with both zero-index boundary values one.

**Coverage coordinates.** The relative signs of $a_{it}-d_{it}x_t$ and $a_{is}-d_{is}x_s$ within each $C_i$ determine all best-response sets, including ties. Thus $H_x=\sum_i\binom{|C_i|}{2}\le k\binom n2$ hyperplanes in $n$ variables suffice. One may use the rank $d_x$ of their normals in place of $n$. A vector $z$ is in their common kernel exactly when $d_{it}z_t=c_i$ for some scalars $c_i$ on all viable edges. In a connected component of the viability graph, propagating one coordinate determines all the others. The component contributes one free dimension if the slope ratios multiply to one around every alternating cycle, equivalently if $d_{it}=u_i h_t$ on its edges. Otherwise it contributes zero. An isolated target contributes one.

**Type-payoff coordinates.** Suppose $\lambda>0$. Defender optimality gives $s_t\ge\lambda$ whenever $x_t>0$. Every positively covered target consequently receives positive mass from at least one type. Combining its equality with the payoff inequalities of all types gives

$$
x_t=\max\bigl(\{0\}\cup\{(a_{it}-v_i)/d_{it}:i\in I_t\}\bigr).
$$

The same formula holds when $x_t=0$, because every displayed normalized value is then nonpositive. Type $i\in I_t$ is active at $t$ exactly when its normalized value equals this maximum. For each target compare its $|I_t|$ affine functions with zero and with one another. The total number of hyperplanes is

$$
H_v=\sum_t\left(|I_t|+\binom{|I_t|}{2}\right)\le n\binom{k+1}{2}.
$$

There are at most $F(H_v,k)$ signatures at positive $\lambda$. Known affine relations between the $v_i$ can reduce the dimension further. For example, positively affine-equivalent utility rows satisfy the same affine relation between their maxima.

**The zero-threshold tail.** If $\lambda=0$, every unsaturated target has zero attack mass, since $\beta_t>0$. Algorithm 2 preserves that column total. From an unsaturated target there is no residual reverse arc to a type and no positive-capacity forward arc to the sink. Algorithm 3 can choose any such target and increase only that coverage. All positively supported attack payoffs stay fixed on saturated targets, so no inferior edge catches up. Each call fills the chosen target or the remaining budget. The tail takes at most $n$ calls, all successful.

Put

$$
C=\min\left\{\prod_i(2^{|C_i|}-1),\ F(H_x,d_x),\ F(H_v,k)\right\}.
$$

For explicit endpoint accounting, set aside successes that change $B$ and the final success, at most $2n+1$ calls altogether. The remaining positive-threshold successes have positive-threshold endpoints in a fixed phase, so Lemma 8 gives at most $(2n+1)C$. Add at most $n$ zero-threshold successes. If $S$ counts all successes, there are at most $S+2n$ failures by Lemmas 6–7. One conservative outer bound is therefore

$$
2(2n+1)(C+1)+4n.
$$

It also holds for zero defender budget, when the loop never starts. The smaller of this and the published $2n+4n3^{kn}$ is valid. In particular $H_x,H_v=O((nk)^2)$, and one of the two arrangement dimensions is at most $\sqrt{nk}$. Bounding $F(H,d)\le(1+2H)^d$ yields the stated size-uniform subexponential count in the explicit payoff table. The strict-gap hypotheses matter for both the published logarithmic edge costs and the reconstruction. Conitzer's full problem permits zero gaps. [Li et al., Theorem 5](https://arxiv.org/pdf/1602.01896) · [Conitzer, §1](https://arxiv.org/pdf/2610.08796)

## How much competition causes extra events

Each $v_i$ is nonincreasing because coverage increases coordinatewise. If $I_t=\{i\}$, then at positive $\lambda$ its viable edge is active exactly when $a_{it}\ge v_i$. Once this happens, it remains active throughout the positive-threshold portion. If all $C_i$ are disjoint, every success ends at a newly active edge, a newly saturated target, or budget exhaustion, as follows from the event conditions in Algorithm 3. The zero-threshold tail has only the latter two events. At least $k$ viable edges are active initially. There are at most $n$ saturations. Hence $S\le \sum_i|C_i|-k+n+1\le 2n-k+1$. The published failure accounting gives **at most $6n-2k+2$ outer iterations**. [Li et al., Algorithm 3 and Lemmas 6–7](https://arxiv.org/pdf/1602.01896)

More generally, let $E_C=\sum_i|C_i|$ and $h=\sum_t\binom{|I_t|}{2}$. Each sign of $a_{it}-v_i$ changes at most twice. Refining the phases by all those signs and by $B$ creates at most $2E_C+2n+1$ intervals before the zero-threshold tail. Inside each interval, only the $h$ pairwise comparisons of normalized type payoffs can distinguish signatures. If their normals have rank $d_o$, their number is at most $M=\min\{3^h,F(h,d_o)\}$. Set aside the success crossing each phase boundary and the terminal success as before. This gives an outer bound $O((n+E_C+1)(M+1))$. The dimension $d_o$ is at most the number of types that share a viable target with another type. Thus bounded overlap gives a tractable class even when both total dimensions grow.

**A two-target obstruction.** Let $R=1$, priors be $(1/4,3/4)$, and defender gains both one. For type 1 use $a_1=(0,0)$, $d_1=(1,1)$. For type 2 use $a_2=(1/4,0)$, $d_2=(2,1)$. Order targets $A,B$ and put an initial tie on $A$. The following are successive states of the published algorithm.

| Event | Coverage $(x_A,x_B)$ | Attack totals $(q_A,q_B)$ | Best targets of type 1 |
| --- | --- | --- | --- |
| Initialization | $(0,0)$ | $(1,0)$ | $A,B$ |
| Failed increase reroutes type 1 | $(0,0)$ | $(3/4,1/4)$ | $A,B$ |
| Increase until type 2 ties | $(1/8,0)$ | $(3/4,1/4)$ | $B$ |
| Failed increase reroutes type 2 | $(1/8,0)$ | $(1/2,1/2)$ | $B$ |
| Increase while keeping type 2 indifferent | $(1/4,1/4)$ | $(1/2,1/2)$ | $A,B$ |

At the first rerouting, type 1 has only $1/4$ to move. At the second, equalizing the two defender rewards moves $1/4$ of type 2. With type 2 split, preserving its tie forces $\gamma_B=2\gamma_A$. Edge $(1,A)$ has now left and re-entered at positive defender threshold. Counting a single activation per edge fails even with two types and two targets.

## A class with an exact longest path

Take $m\ge4$ divisible by four, $k=m$, targets $A_i,B_i$ for each type, equal priors, defender budget $m/2$, and all defender gains and attacker penalties one. Set $a_{i,A_i}=1$, $a_{i,B_i}=1/2$, and every other uncovered payoff in row $i$ to $-1$. Use the ordinary initialization and stop as soon as the coverage sum equals $m/2$. For a deterministic run, scan targets in the order $A_1,\ldots,A_m,B_1,\ldots,B_m$.

All attack mass stays on its owner's $A_i$, and $B=\{A_1,\ldots,A_m\}$. For an unprocessed $i$, source $A_i$ reaches only its own type among the relevant nodes. Its coverage rises alone to $1/2$, when $B_i$ first ties. Afterward the residual path $A_i\to i\to B_i$ disqualifies that source because $B_i\notin B$. The min-cost flow is unique given the column totals and active edges. Until the budget is exhausted some source is eligible, so Algorithm 4 never runs.

Every allowed source order therefore has **exactly $m$ outer iterations**. If all permitted source choices are included, the reachable-state graph has one vertex for every subset $S\subseteq[m]$ of processed types and arcs $S\to S\cup\{i\}$. The rank $|S|$ proves the exact path length. At the same allocated resource $m/4$, the same defender boundary and the same attack totals admit $\binom m{m/2}$ reachable full signatures under different source orders. A fixed scan order selects a single chain. Exact-fraction enumeration of the residual arcs and coverage events gave 16 vertices and 32 arcs for $m=4$, and 256 vertices and 1,024 arcs for $m=8$.

## Computing a worst case

Fix the solver, arithmetic, iteration metric and tie rules. For example, send each initial type to its first maximizing target. Choose the lexicographically first eligible source, the lexicographically smallest optimal flow in Algorithm 2, and the lexicographically smallest maximizing flow at the largest feasible $\Delta$ in Algorithm 4. Solve for $\Delta$ exactly, skip zero denominators in Algorithm 3 event tests, and use $\lambda$ as an upper bound when Algorithm 4 has no lower-valued site. At $\Delta=\lambda$ each open site has already released its entire current load.

- **Bounded rational encodings.** Enumerate all valid instances of length at most $L$, run the terminating solver and take the largest count. This computes a maximum for that encoding and size. Extending the result to all sizes requires a bound on its growth.
- **Fixed $n,k$, real payoffs.** For any semialgebraic instance class specified over the rationals, the exact maximum outer count is also computable in principle. Use the finite bound to unroll the deterministic transition relation. Minimum-cost flow optimality is equivalent to the absence of a negative simple residual cycle. Sums of signed $\log d_{it}$ around a cycle compare products of the positive slopes. A shortest-path rate is the maximum reciprocal cost product over finitely many simple reachable paths. These tests use polynomial inequalities after clearing positive denominators. Feasible flows, the maximal feasible $\Delta$, and lexicographic tie rules are first-order conditions over real numbers. Decide whether one parameter tuple sustains at least $j$ steps and maximize $j$ by binary search. Quantifier elimination gives a decision procedure whose running time can greatly exceed the count it computes. A real witness can have algebraic irrational coordinates, so transferring a maximum to unrestricted rational inputs would need a separate argument. [Cohen and Mahboubi, real quantifier elimination](https://arxiv.org/abs/1201.3731)
- **A finite transition graph.** A topological longest path certifies an upper bound when every real transition is represented, initialization and termination are correct, and a common rank makes the relevant graph acyclic. To certify an exact maximum, exhibit a path of that length realizable on one instance, or prove a path-lifting property. The same local signatures can hide different next events. For example, with one type, two targets, unit slopes and budget one, changing the initial payoff gap from $1/4$ to $2$ preserves the initial active set, flows and legal source. The first increase hits a tie in the former game and exhausts the budget in the latter. A graph formed by taking local edges from different inputs can join incompatible transitions.

The next compression to test is a sum of ranks over disconnected competition components. In the explicit family the sum is $|S|$. For general components, a proof must bound local progress when Algorithm 4's shared decrease in $\lambda$ is determined by a different component. The two-type example shows that a component rank must tolerate repeated membership of an individual edge. A separate algorithm already solves the bounded-component class without analyzing its augmentation path. [Component composition](B2-component-composition.md)
