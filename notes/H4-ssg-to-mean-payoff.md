# Simple stochastic games reduce to deterministic mean-payoff games

## Statement

Given an explicitly encoded simple stochastic reachability game $G$, a state $s$, and a binary rational $t$, one can construct in polynomial bit time a deterministic mean-payoff game $H$ with binary integer weights and a state $s'$ such that

```math
                 v_G(s)\ge t\quad\Longleftrightarrow\quad v_H(s')\ge0.
```

The source has absorbing Win and Lose states, nonempty successor lists at player states, and two equally probable successors at chance states. Reaching Win pays one and all other plays pay zero, including plays that never absorb. The target payoff is the lower limiting average of its edge weights. The reduction is many-one and handles equality at the threshold.

The main lemma also reduces Bodirsky, Loho and Skomra's max-average feasibility problem to max-atom feasibility. The proof handles rational strict difference inequalities, which gives the deterministic mean-payoff reduction for the finite tropically convex semilinear CSP language of Bodirsky and Mamino. [Max-average CSP, Definition 4](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2025.145) · [Tropically convex CSPs, Section 2 and Theorem 3.4](https://arxiv.org/abs/1506.04184)

## 1. Approximate one mean with a small circuit

Suppose $|u-v|\le W$, where $W>0$. Let $H_0=\max(u,v)$, $L_0=\min(u,v)$. In round $j$ sort the pair

```math
                H_{j-1}-W2^{-j-1},\qquad L_{j-1}+W2^{-j-1}
```

into $H_j\ge L_j$. The sum stays $u+v$ and the gap satisfies

```math
 d_j=|d_{j-1}-W2^{-j}|,\qquad
 0\le d_j\le W2^{-j}.
```

The last bound follows by induction from $d_{j-1}\in[0,2W2^{-j}]$. Thus

```math
          \frac{u+v}{2}\ \le\ H_r(u,v)\
          \le\ \frac{u+v}{2}+W2^{-r-1}.                        \tag{1}
```

There are $2r+2$ gates. Each gate is a max or min of two translated predecessors. It is order preserving on the entire real line in each operand. The gap bound only needs the initial input difference bound.

This is a recentered form of an existing recurrence. Bezem, Nieuwenhuis and Rodríguez-Carbonell construct the min/max layers with successively doubled earlier offsets. Rescaling those offsets gives the dyadic layers. Allamigeon, Benchimol, Gaubert and Joswig use the stages $(a,b)\mapsto(1+\min(a,b),1-2^{-j}+\max(a,b))$ directly. Subtracting the common stage drift $1-2^{-j-1}$ from both outputs leaves the two shifted values above for $W=1$. Sorting after this subtraction rather than before the next stage gives the displayed form. The papers also use upper inequalities for the gates. [Bezem et al., Section 3](https://www.cs.upc.edu/~roberto/papers/dam08.pdf#page=4) · [Allamigeon et al., Proposition 20 and equation (30)](https://www.cmap.polytechnique.fr/~gaubert/PAPERS/sigest-paper.pdf#page=27)

For $W=1$ and $r\ge1$, the gap is the distance from $|u-v|$ to the $2^{r-1}$ midpoints of the equally spaced intervals in $[0,1]$. To see this, at each refinement the two new midpoints of the previous nearest cell are offset from its midpoint by $2^{-j}$. The closest new midpoint is one of those two, with distance $\bigl|d_{j-1}-2^{-j}\bigr|$. Equivalently $H_r$ is the minimum of $2^r$ shifted maxima $\max(u+c,v-c)$ for the centered dyadic grid of shifts. Bodirsky and Mamino use the corresponding intersection over all rational shifts to describe the exact mean inequality. The circuit shares its two progressing outputs and uses only $O(r)$ gates even at exponentially fine precision. [Bodirsky and Mamino, proof of Corollary 3.5](https://arxiv.org/pdf/1506.04184#page=8)

## 2. Eliminate means from bounded feasibility

Consider a conjunction of rows of the following forms. Constrain the source variables to a rational box, with all permitted average operands, including literals, in a common scalar interval of width at most $W$.

- A rational literal bound or equality, or a difference inequality with a rational offset.
- $x_i\le\max_{j\in J}(x_j+c_j)$ for a nonempty explicitly listed set of terms.
- $x_i\le(x_j+x_k)/2$.

Literals can occupy either input of an average. A minimum on the right is expressed by one upper inequality per term. All inequalities here are weak. The later strict-margin lemma handles strict differences.

### A uniform violation bound

Fix any selection of one term in each max row. A feasible point of the original system satisfies a selection, and a feasible point of a selection satisfies the original max rows. Add a slack variable $0\le\rho\le1$ to the selected system, replacing every average row by $x_i\le(x_j+x_k)/2+\rho$. Keep the box and all hard rows exact. Clear the factor of two on the average rows. Let $D\ge1$ be a common denominator of every right side in these linear systems and $A\ge1$ an integer bound on every coefficient row's Euclidean norm. Both are computable from the explicitly listed rows and terms. Let $n$ be the number of source variables.

If a selected relaxed system is feasible, its minimum $\rho$ occurs at a vertex of a compact rational polyhedron in $n+1$ coordinates. A vertex has $n+1$ linearly independent tight rows even if the polyhedron has smaller affine dimension. Let $M$ be the matrix of these tight rows. Its entries are integral and $0<|\det M|\le A^{n+1}$ by Hadamard's inequality. Applying Cramer's rule with the right side multiplied by $D$ shows that $D\det(M)\rho$ is an integer. Therefore

```math
        \min\rho=0\quad\text{or}\quad\min\rho\ge 1/(D A^{n+1}).        \tag{2}
```

This holds for every selection. Repeated variables combine their coefficients in a row, and the row-norm bound is taken after that combination. Terms which are constants affect the right side. The encoder only needs bounds for the possible rows, irrespective of which ones a solution selects.

### One-sided gates and exact feasibility

Choose $r$ with $\varepsilon=W2^{-r-1}<\min(1,1/(D A^{n+1}))$. For each average row use the circuit in (1). Replace an equality $z=\min(a+c,b+d)$ by $z\le a+c$ and $z\le b+d$. Replace an equality $z=\max(a+c,b+d)$ by the upper inequality on that same maximum. Enforce $x_i\le H_r$ using the variable for the last upper gate. Use fresh internal variables for the replacement of each average, retaining shared wires within each circuit.

Given the source variables in any assignment to the new system, induction along each directed acyclic circuit shows that every internal variable is at most the exact evaluation at those inputs. This uses monotonicity on all real operands. An auxiliary variable can lie outside the original input range. It can only lower the upper bounds supplied to later gates. Cycle edges among the original variables cause no problem because the induction conditions on their assigned values. In the other direction the exact circuit evaluation realizes all gate bounds.

An exact source solution extends to the compiled system by the lower bound on $H_r$ in (1). Conversely a compiled witness projects to a point satisfying all hard rows and all average rows with common slack $\varepsilon$. At this point choose an attaining term of each original max. We have a feasible point of that particular relaxed linear program. Its optimum is at most $\varepsilon$, so (2) forces optimum zero. The original system has an exact solution of the selected branch. In a search application, one rational linear program recovers such a point. The projected compiled point itself may use positive slack.

### Integers and bit length

Use a single reference variable $o$ to express absolute constants and box bounds. For example $x_i\ge a$ becomes $o\le x_i-a$, with the reference normalized to zero by translation. A weighted maximum with unequal input offsets can be made an ordinary max-atom by making separate variables $a'=a+c$, $b'=b+d$ with two difference inequalities per equality. A long maximum can use binary max gates and upper inequalities, which have the same monotonicity proof. Thus all constraints become $z\le\max(a,b)+c$, including difference inequalities with repeated right-hand terms.

Scale all variables and offsets by a common positive integer denominator. Coordinatewise flooring then maps any real solution to an integer solution because it commutes with maximum and integer translation. Conversely integer solutions give real solutions by reversing the scaling and normalizing the reference. Every scaling factor has polynomial bit length. For the unscaled circuit the new denominators divide $2^{r+1}$ times the denominator of $W$, and the number of new gate rows is linear in $r$ per average. The chosen $r$ is polynomial in $\log(W+1)$, the printed bit lengths, and $n\log(A+1)$. This yields polynomial construction time and size in the full binary input length.

## 3. Remove the box and allow strict inequalities

First handle empty maxima if they are allowed over the extended domain, with $\max\varnothing=-\infty$. Mark their left-side variables as forced to $-\infty$. Close the set under the rules that a mean row with a marked operand forces its left side to be marked, and a max row with every term marked forces its left side to be marked. In the shifted language also propagate along any difference row whose right-side variable is marked. Reject a marked variable with an imposed finite equality or lower bound. Discard rows with marked left sides and remove marked terms from the remaining maxima. Every original solution has the marked coordinates equal to $-\infty$; conversely, extending a residual solution by these bottom values satisfies the discarded rows and restores all the remaining ones. Closure and deletion take polynomial time. All residual max lists are nonempty.

In the max-average language with nonempty max lists and fixed rational literal equalities, any solution over $\mathbb Q\cup\{-\infty\}$ can be truncated from below at a common finite $L$ no larger than all literals. A max or average of truncated inputs is at least $L$ and is no smaller than before truncation. If a left side increases, its new value is $L$, so the corresponding inequality still holds. This gives finite-variable feasibility for that language. The argument is used here for the unshifted max and average rows. The strict and shifted language below is over finite rationals.

To bound finite witnesses, take any selected set of max terms and append $R\ge0$ and $-R\le x_i\le R$. If the selected weak system is feasible, the resulting pointed polyhedron is nonempty and has a vertex. Let $h\ge2$ bound the absolute coefficients and right sides after clearing denominators in each possible row. With $n+1$ coordinates, Cramer's rule bounds the absolute coordinates at a vertex by $(n+1)!\,h^{n+1}$. Hence a box of that radius suffices uniformly over selections.

To handle $x_i<x_j+c$, instead add a common $0\le\delta\le1$ and replace each strict row by $x_i+\delta\le x_j+c$. Append the same $R$ rows. A strictly feasible point gives some $\delta>0$ in its selected rational polyhedron. Maximizing $\delta$ has an attained optimum since the objective is bounded above on a nonempty polyhedron, and its optimal face is pointed and contains a vertex. With $n+2$ coordinates, take $B=(n+2)!\,h^{n+2}$, increasing $h$ if needed for these added rows. A positive optimum at a vertex is at least $1/B$, and that vertex's source coordinates have magnitude at most $B$. Thus a box $[-B,B]^n$ and the single imposed margin $\delta=1/B$ preserve feasibility exactly. Every solution of the strengthened weak rows satisfies the strict rows.

Apply Section 2 in this box. The bit length of $B$ is polynomial in the input length, including rational constants. This proves the many-one reduction for unbounded max-average feasibility and for finite rational systems with weak or strict differences and shifted max rows. In particular, each relation in a fixed finite tropically convex semilinear language over $\mathbb Q$ has a fixed primitive-positive definition using strict order, two unit difference bounds, the average hypograph, and the max hypograph. Substituting its definition per occurrence takes linear expansion for the fixed language. The finite canonical language therefore reduces to mean-payoff decision, and the reverse reduction for that language is already established. This answers the finite-language question through a reduction on whole instances. [Bodirsky and Mamino, Section 2, Theorem 3.4(2), Observation 3.6 and Section 5](https://arxiv.org/pdf/1506.04184)

## 4. From max-atoms to one deterministic game

In the integer system, make a Min vertex for each variable $x_i$. Each row $x_i\le\max_j(x_j+c_{aj})$ gives an edge at weight zero from $i$ to its own Max vertex $a$. At $a$, Max chooses $j$ and receives weight $c_{aj}$ on the edge back to variable $j$. Add a weight-zero self-loop to a variable with no row. Add a fresh start $s_0$, owned by Min, with a weight-zero edge to every variable. The compiler always supplies a reference variable, so the start has an outgoing edge. This gives a single target $K$.

Given a feasible potential $x$, choose one satisfying term in each row. On each two-edge move the weight is at least $x_i-x_j$. The sum along every play against these choices is bounded below, by telescoping, so $v_K(s_0)\ge0$. Conversely an optimal positional Max policy with nonnegative value from $s_0$ leaves no negative directed cycle. Min could enter any variable of such a cycle directly from $s_0$ and repeat the cycle. Contract the row moves and add one sink with a zero edge from every variable. Shortest distances $x_i$ to the sink are finite integers and satisfy $x_i\le c_{aj}+x_j$ for every selected term. The system is feasible. This is the max-atom game construction with a designated start. [Atserias and Maneva](https://www.cs.upc.edu/~atserias/papers/mean-payoff-games-max-atom/mpma.pdf)

## 5. Apply the compiler at an arbitrary stochastic-game threshold

On the nonterminal coordinates, let $F$ be the ordinary Bellman operator of the reachability game. Its rows are max, min, or fair averages of successors. Terminal successors have the constant values one or zero. The finite-horizon values are $F^k(0)$ by backward induction, with the terminal values supplied from the first step. They increase to a vector $v$ with $v=F(v)$ by continuity. The finite-horizon strategies show that Max can ensure an infinite-horizon probability arbitrarily close to $v_s$.

For any $x\in[0,1]^n$ satisfying $x\ge F(x)$, let Min pick a successor attaining the minimum at $x$ wherever she moves. Against any Max play, the conditional expectation of the next $x$-value is at most the current one, including after absorption. Thus the probability of reaching Win by time $k$ is at most $x_s$ for every $k$, and taking the increasing limit gives the same bound for eventual reachability. In particular $v$ is an upper bound attainable by Min, so it is the value vector of $G$ and the least Bellman fixed point. This argument allows closed nonterminal recurrent classes.

We need to recognize the strict negative case $v_s<t$. It is equivalent to the existence of $x\in[0,1]^n$ with $x\ge F(x)$ and $x_s<t$. Make the change $y=\mathbf 1-x$. The exact constraints are

```math
  y\in[0,1]^n,\qquad y\le\mathbf 1-F(\mathbf 1-y),\qquad y_s>1-t.
                                                                    \tag{3}
```

The dual operator swaps max with min and complements terminal constants. Its chance rows are fair averages. Here it is used as a system of inequalities on numbers, with no claim about the reachability value of the game with swapped terminals.

### Explicit precision on the unit cube

Write $t=a/b$ with $b>0$. Cases $t\le0$, $t>1$, and terminal starts are decidable directly and output a one-vertex target with the corresponding sign. Otherwise choose

```math
                    D=b\,3^{n+1}.
```

For the strict row in (3), use $y_s\ge 1-t+\delta$ and maximize $0\le\delta\le1$ in a selected branch on the unit cube. Clearing chance rows by two gives integral matrices with row norm at most $\sqrt8<3$. The only nonintegral right side has denominator dividing $b$. In $n+1$ coordinates a strictly positive optimum is at least $1/(b\,3^{n+1})$. Thus the single weak threshold $y_s\ge1-t+1/D$ is exact for (3). No source value denominator bound is needed.

Next use the violation program of Section 2 in $n+1$ coordinates, now with the weak threshold and the variable $\rho$. Its right sides have denominators dividing $D$, and row norms are at most $\sqrt{12}<4$ after clearing the chance rows. In particular the repeated-successor row can have coefficients $2,-2,-2$ on distinct coordinates, including $\rho$. Take

```math
      r=\operatorname{bitlength}(D)+2(n+1).
```

Then $W=1$ and $\varepsilon=2^{-r-1}<1/(D\,4^{n+1})$. A feasible compiled system yields an exact witness to (3) by the two gap arguments. A scale of $D\,2^{r+1}$ clears the new offsets and the threshold. Weighted maxima can go straight into the row vertices of Section 4.

For a stopping game the same unit-cube argument also works in the original direction by using $x\le F(x)$ and the weak threshold $x_s\ge t$. If $x$ satisfies these constraints, fix Max to an attaining choice at $x$. Until absorption the $x$-value is a submartingale against any Min play, and absorption gives $x_s\le v_s$. The value vector gives the converse witness. Alternatively the direct construction using (3) works uniformly for stopping and nonstopping games. [Bodirsky, Loho and Skomra, Proposition 5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.145/LIPIcs.ICALP.2025.145.html)

The order of the strict-margin and approximation steps matters. Take $S$ fair to $T$ or a nonterminal self-loop $Z$, and $T$ fair to $S$ or Win. Then $(v_S,v_T,v_Z)=(1/3,2/3,0)$. At threshold $1/3$, the strict row in (3) is $y_S>2/3$. If the averages are replaced before strengthening that row, set $y_Z=1$, $y_T=1/3$, and $y_S=H_r(1,1/3)>2/3$. The strict inequality holds because $2/3$ is never an odd dyadic center of the gap. The remaining chance row holds since $H_r(y_S,0)\ge y_S/2>1/3$. This is a spurious strict-NO witness at every finite depth $r\ge1$ if the uniform positive margin is omitted.

### Reverse the sign without losing equality

The resulting $K$ satisfies $v_K(s_0)\ge0$ exactly when $v_G(s)<t$. Let $N=|V(K)|$. Positional determinacy of finite deterministic mean-payoff games gives an optimal positional pair at the designated start. Their payoff is the mean of a cycle of length at most $N$. With integer weights, every strictly negative value is at most $-1/N$.

Form $H$ by swapping the players throughout $K$ and replacing each weight $w$ by $-Nw-1$. Keep $s_0$ as the designated start. When both games are evaluated on positional strategies, every play is eventually periodic, and the transformed payoff is the original payoff multiplied by $-N$ and shifted by $-1$. Swapping the players and taking the value over positional strategies therefore gives $v_H(s_0)=-N v_K(s_0)-1$. It follows that $v_H(s_0)\ge0$ exactly when $v_K(s_0)<0$. In particular the intermediate value zero becomes $-1$, so a weak threshold is preserved in the required direction. [Positional determinacy and max-atom games](https://www.cs.upc.edu/~atserias/papers/mean-payoff-games-max-atom/mpma.pdf)

If the source has $n$ nonterminal states, $m$ listed successor occurrences and $a_{\mathrm{ch}}$ chance rows, the target has $O(n+m+a_{\mathrm{ch}}r)$ vertices and arcs combined. Its weights have $O(n+\log b+\log N)$ bits. The shift at the end adds at most $O(\log N)$ bits per weight and changes no adjacency. The finite-horizon limits, the selections, and the LP optima are proof devices. The encoder constructs the graph from the given input and the explicit precision alone.

## Literature and review status

Bodirsky and Mamino already expressed average hypographs using an infinite family of shifted maxima, and Bezem and coauthors and Allamigeon and coauthors already gave the equivalent dyadic recurrence with its one-sided encoding. The contribution here is to use a polynomial-depth truncation and a uniform rational violation bound to preserve exact feasibility in whole, possibly cyclic systems. The arbitrary-threshold reduction uses a strict certificate for the complement to avoid a stopping transformation. The October 28, 2026 seminar stated that the reverse polynomial game reduction was open. That records the contemporary status of the question. [Prior-art comparison](H4-averaging-prior-art.md) · [Parys seminar](https://mimuw.edu.pl/en/seminars/talk/quasipolynomial-algorithms-for-mean-payoff-and-simple-stochastic-games/)

The companion notes give the search reductions, the earlier stopping-based route, and the resulting single-instance decision and search reductions for the more general stochastic mean-payoff model. [Search and stopping-gadget reductions](H4-deterministic-game-reductions.md) · [Stochastic mean-payoff extension](H4-stochastic-mean-payoff.md)

## Exact replay

Run the exhaustive replay from the repository root with Python 3 and the `z3` executable on `PATH`. The required SMT mode checks every emitted graph and exits with an error if Z3 is unavailable.

```sh
python3 experiments/h4_ssg_to_mpg_replay.py --route direct --random 0 --systematic 2 --require-smt
```

With Python 3.13.3 and Z3 5.3.2, the replay checked labelled one- and two-nonterminal-state binary game structures with unordered successors and targeted fixtures. All 3,634 game/threshold cases passed exact graph certificate verification and graph-only SMT, with 2,136 YES and 1,498 NO cases. The fixture named closed-third-equal is the cyclic $1/3$ example above. Passing `--route direct --dump closed-third-equal` emits its complete 193-vertex target and certificate. Passing `--verify` with the resulting JSON checks the target certificate without solving the source game.

The alternate stopping and fair-ladder compilers and targeted mutation tests use the same verifier. In particular omitting the strict margin or shortening the fold depth can produce incorrect target decisions, and the verifier certifies those decisions on the mutated graphs. [Replay and certificate verifier](../experiments/h4_ssg_to_mpg_replay.py)

Exponentially fine precision can already matter in an acyclic system. With $x_0=0$, $0\le x_i\le1$, the rows $x_i\le(1+x_{i-1})/2$ for $1\le i\le n$ imply $x_n\le1-2^{-n}$. Adding the bound $x_n\ge1$ makes the source infeasible, with minimum common slack $1/[2(2^n-1)]$. This follows by unrolling the relaxed recurrence and attaining equality at every step at that slack.

## Lean formalization

Lean checks the finite-horizon Bellman certificate, the explicit bounded compiler to integer weighted max-atoms, and the corresponding graph potential criterion. It also checks the integer cycle comparison used for the sign reversal. The written argument supplies the stochastic payoff interpretation, the strict real-to-rational bridge, positional determinacy, and the bit-time bounds. [Lean workspace and checked scope](../lean/README.md#stochastic-game-reduction)
