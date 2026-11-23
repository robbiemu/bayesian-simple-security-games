# Reductions from stochastic to deterministic games

The threshold reduction for arbitrary binary rationals has a shorter proof using the least reachability fixed point. The main proof also records the earlier sources for the dyadic min/max recurrence. [Arbitrary-threshold decision proof](H4-ssg-to-mean-payoff.md)

Two polynomial-time reductions follow from a small circuit for approximating an average.

1. **Decision.** Max-average feasibility reduces to integer max-atom feasibility and hence to deterministic mean-payoff threshold decision. In particular, one deterministic mean-payoff threshold instance suffices for a simple stochastic game at a specified start, including the equality case.
2. **Search.** Exact values and optimal positional strategies in finite two-player, zero-sum, turn-based stochastic discounted games with binary rational input reduce to exact search on deterministic discounted games and to positional-strategy search on deterministic mean-payoff games. Either encoder makes one game and the decoder recovers the original exact answer from any valid target answer.

The circuit uses only minima and maxima of translated predecessors. Approximation suffices because the source problems have quantitative separation bounds. In the decision reduction the bound is on the least constraint violation. In the search reduction it comes from contraction and a denominator bound. The results concern explicitly encoded games with a common discount supplied in binary.

## Averaging with shifts and comparisons

For real $x,y$ with $|x-y|\le W$, put $H_0=\max(x,y)$, $L_0=\min(x,y)$. For $j=1,\ldots,r$ define


```math
\begin{aligned}
 a_j&=H_{j-1}-W2^{-j-1}, & b_j&=L_{j-1}+W2^{-j-1},\\
 H_j&=\max(a_j,b_j), & L_j&=\min(a_j,b_j).
\end{aligned}
```


Each stage preserves the sum $H_j+L_j=x+y$. The gap satisfies

```math
d_j=|d_{j-1}-W2^{-j}|,\qquad d_0\le W.
```

Induction gives $d_j\le W2^{-j}$. In particular,

```math
0\le H_r-\frac{x+y}{2}\le W2^{-r-1}.
```


The recurrence uses $2r+2$ min or max gates when offsets are on incoming edges. Each gate is nondecreasing in its inputs and is 1-Lipschitz in the sup norm, even outside the range used for the error bound. The upper approximation $\min(H_r,H_0)$ has the same error bound and takes values in $[\min(x,y),\max(x,y)]$. That version is convenient for nested averages. The dyadic recurrence and its one-sided encoding are recentered versions of published constructions. [Bezem, Nieuwenhuis and Rodríguez-Carbonell, Section 3](https://www.cs.upc.edu/~roberto/papers/dam08.pdf#page=4) · [Allamigeon, Benchimol, Gaubert and Joswig, Proposition 20](https://www.cmap.polytechnique.fr/~gaubert/PAPERS/sigest-paper.pdf#page=27)

## Max-average feasibility reduces to deterministic mean-payoff decision

Max-average feasibility asks for a solution in $(\mathbb Q\cup\{-\infty\})^n$ to constraints of the forms $x_i\le\max_{j\in J}x_j$, $x_i\le(x_j+x_k)/2$, and $x_i=c$ for a binary rational $c$. Upper and lower constant bounds can be included directly. The version below takes the set $J$ in each max row to be nonempty. [Bodirsky, Loho and Skomra, Definition 4 and Proposition 5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.145/LIPIcs.ICALP.2025.145.html)

### A box and a positive violation gap

Let $h\ge 2$ be an integer bounding the absolute numerators and positive denominators of all rational constants. Take

```math
B=(n+1)!\,h^{\,n+1}.
```


Truncating all coordinates from below at a common finite rational $L$ below all constants preserves feasibility. If the original left side is at most $L$, every right-side max or average becomes at least $L$. Otherwise the left side stays fixed and the right side weakly increases. Thus a feasible instance has a solution with finite coordinates.

Fix one term of each max row and replace that row by the inequality using that term. Every feasible assignment satisfies at least one such system, and every point of such a system satisfies the original max rows. Append a variable $t$ with $t\ge 0$ and $-t\le x_i\le t$. The resulting polyhedron has no affine line, so if it is nonempty it has a vertex. Clear denominators row by row, using a factor of two for averages. Coefficients and right sides have magnitude at most $h$. Cramer's rule bounds every vertex coordinate by $B$, since a nonzero integer basis determinant has magnitude at least one. Consequently it suffices to test $|x_i|\le B$.

For any fixed selection of max terms, keep the box and all other rows exact and relax each average row to $x_i\le(x_j+x_k)/2+\rho$, with $0\le\rho\le1$. If this bounded linear program is feasible, its minimum $\rho$ is attained at a vertex. The coefficient entries after clearing denominators still have magnitude at most $h$, including when terms repeat. The large box bounds appear only on the right side. The determinant of any basis has magnitude at most $B$. A positive minimum is therefore at least $1/B$. This bound is uniform over selections, so the encoder never needs to find or enumerate them.

### The replacement by max-atoms

On the box use the upper approximation $H_r$ with $W=2B$ and $r=2\lceil\log_2 B\rceil+1$. The error is at most $B2^{-r}<1/B$. For each average add one variable for each gate. A gate $z=\min(u+a,v+b)$ contributes two inequalities $z\le u+a$, $z\le v+b$. A gate $z=\max(u+a,v+b)$ contributes $z\le\max(u+a,v+b)$. Replace the average row by $x_i\le H_r$ using its output variable. The directed acyclic circuit makes these one-sided inequalities sufficient. Induction in evaluation order bounds every assigned gate variable above by its true circuit value on the supplied inputs. Conversely the exact circuit values attain all gate bounds simultaneously.

An exact feasible point in the box extends to the new system because $H_r$ bounds the mean from above. If the new system has a solution, each original average row holds with common slack $B2^{-r}$, and each original max row supplies a selected term. The least-relaxation linear program for that selection has optimum below $1/B$, which forces optimum zero. This recovers exact feasibility, including on instances where every exact witness lies on an equality boundary.

Introduce a reference variable $o$ to express all literal bounds relative to $o$. For example, use $x_i\le o+B$, $o\le x_i+B$ for the box. Translation allows $o=0$. An offset inside a max can be assigned a fresh variable with two difference inequalities enforcing the offset. A max of larger arity can be expressed by binary gates with the same one-sided convention. Multiply every variable and offset by a common denominator of the offsets to obtain integral constants. Coordinatewise flooring preserves every resulting inequality because floor commutes with max and integer translation. Thus real feasibility and integer feasibility agree for the final max-atom instance. There are polynomially many gates and every offset, including the bounds and the scaling denominator, has polynomial bit length.

### A single mean-payoff instance

For each variable $x_i$ make a Min vertex. Min chooses one row $x_i\le\max_j(x_j+c_{aj})$ with that left side, moving at weight zero to its Max vertex. Max chooses a term $j$ and moves to $x_j$ at weight $c_{aj}$. A variable with no row can take a weight-zero self-loop. A fresh start is owned by Min and can reach every variable at weight zero.

Given a feasible potential $x$, choose a satisfying term in every row. Each two-edge move then earns at least $x_i-x_j$, so the finite sums are bounded below and the limiting average is nonnegative. Conversely, by positional determinacy, a nonnegative value from the fresh start supplies a positional Max choice. The resulting directed graph on variables has no negative cycle since Min could enter and repeat any such cycle. Adjoin a new sink with a zero-weight arc from each variable. Shortest distances to that sink satisfy $x_i\le c_{aj}+x_j$ for each chosen term. This gives an integral feasible potential. The construction is the usual max-atom reduction with a single test start. [Atserias and Maneva, *Mean-Payoff Games and the Max-Atom Problem*](https://www.cs.upc.edu/~atserias/papers/mean-payoff-games-max-atom/mpma.pdf)

This procedure also recovers an exact solution of a feasible max-average instance from any optimal positional Max strategy in the resulting game. Normalize the recovered potential by subtracting the reference and undoing the scaling. It satisfies the exact max rows and the approximate average rows. Select one attaining term per original max row using that potential. The violation-gap argument ensures that the original exact linear system for this selection is feasible. Solve that system by rational linear programming to recover a witness.

## Simple stochastic games at a specified start

For a stopping simple stochastic game the standard certificate for a value at least $t$ at state $s$ is a vector in $[0,1]^n$ with $x_s\ge t$ and $x\le F(x)$, where the absorbing payoffs are fixed at zero and one and $F$ has max, min and fair-average rows. The value is a witness in a YES instance. For the other direction, fix Max to an attaining successor at $x$ and Min to an attaining successor at the true value $v$. If $P$ is their transient transition matrix on nonterminal states, then $x-v\le P(x-v)$. Iterating and using absorption gives $x\le v$. This is the max-average certificate. [Bodirsky, Loho and Skomra, Proposition 5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol334-icalp2025/html/LIPIcs.ICALP.2025.145/LIPIcs.ICALP.2025.145.html)

For completeness the stopping assumption can be imposed in a single reduction from the standard reachability game, where nontermination has payoff zero. Suppose there are $n\ge1$ nonterminal states. Fix any positional pair in the original game. From any state outside the bottom recurrent classes there is a simple positive-probability path of length at most $n$ to a bottom class. Its probability is at least $2^{-n}$. Hence the expected time to reach a bottom class is at most $n2^n$. Bottom classes distinct from Win have winning probability zero. After fixing these boundary values, the winning probabilities solve a transient system whose integer coefficient matrix is $2(I-P)$. Each row has Euclidean norm at most $\sqrt{8}$. Hadamard's inequality bounds the denominator of every coordinate by $3^n$. In particular, by positional optimality, a value strictly below $1/2$ is at most $1/2-1/(2\cdot3^n)$. [Condon, *The Complexity of Stochastic Games*](https://doi.org/10.1016/0890-5401(92)90048-K)

At every entry into an original nonterminal, insert a fair-coin ladder that goes to Lose with probability $\lambda=2^{-(6n+4)}$ and otherwise proceeds to the original state. A sequence of $6n+4$ specified coin outcomes suffices, with the first failure sending play to the original state. Entry now includes the ladder at the designated start. The new game stops. Its positional choices at original states agree with those of the original game. For a fixed pair, couple both plays and count the possible forced losses before the first original bottom class. The winning probability decreases by at most $\lambda n2^n$, and cannot increase. The same bounds hold for the value, by positional optimality in both games.

Set $t=1/2-2^{-(2n+2)}$. The timeout loss is less than $1/2-t$, while the strict NO gap in the original game exceeds $1/2-t$. Thus the original value is at least $1/2$ exactly when the new value is at least $t$. The stopping certificate followed by the max-atom construction gives one polynomial-size deterministic mean-payoff instance. The supplied start can be a terminal, in which case its threshold answer is immediate.

## Exact discounted search reduces to deterministic discounted search

A source state $s$ has a nonempty action set $A_s$ and belongs to one player. Action $a$ gives rational immediate reward $r_{sa}$ to Max and moves to $j$ with rational probability $P_{saj}$. The common discount is $0<\gamma<1$. Rewards use the convention $\mathbb E[\sum_{k\ge0}\gamma^k r_k]$. The case $\gamma=0$ is decidable from the first action.

Take $R=\max(1,\max_{s,a}|r_{sa}|)$ and $t_{sa}=(1+r_{sa}/R)/2$. If $v_s$ is the original value, let $w_s=1/2+(1-\gamma)v_s/(2R)$. Then $w\in[0,1]^n$ solves the normalized equations

```math
 F_s(w)=\operatorname{opt}_{a\in A_s}
 \left((1-\gamma)t_{sa}+\gamma\sum_j P_{saj}w_j\right)=w_s.
```

The operator $F$ is a $\gamma$-contraction in the sup norm. Each action is a convex combination of the state inputs and two constant inputs zero and one, with weights $\gamma P_{saj}$, $(1-\gamma)(1-t_{sa})$ and $(1-\gamma)t_{sa}$.

### Choosing the needed precision

Let $D$ be the product of the denominators of the coefficients $\gamma P_{saj}$ and $(1-\gamma)t_{sa}$ for all actions. At $w$, choose an attaining action in each row. The normalized value solves the selected linear system, which is nonsingular by contraction. Each row of the integer coefficient matrix after multiplying by $D$ has $\ell_1$ norm at most $2D$. Therefore $Q=(2D)^n$ bounds each coordinate denominator by Cramer's rule and Hadamard's inequality. This bound is computable using the source data alone. Set

```math
\varepsilon=\frac{1-\gamma}{16Q^2}.
```

All these numbers have polynomial bit length.

### A polynomial-size circuit for each action

For a combination with $m$ inputs, round cumulative weights down to multiples of $2^{-k}$, keeping the last cumulative weight equal to one. The resulting successive differences are nonnegative and sum to one. The error in the combination on $[0,1]^m$ is at most $m2^{-k}$.

Label $2^k$ consecutive positions by the inputs, with a contiguous interval of the required integer length for each input. Their equally weighted mean is the rounded combination. Compute it conceptually by halves of a balanced binary tree. A whole interval bearing one label is just that input. At each depth at most $m-1$ intervals contain an interior label change, so the tree with uniform intervals suppressed has $O(mk)$ nodes. It can be written by recursively splitting the mixed intervals using the integer endpoints, without listing the positions.

Replace each remaining average by $\min(H_r,H_0)$ with $W=1$. Its macro output stays in the range of its two inputs, so the approximations all apply on $[0,1]$. The error accumulates by at most $2^{-r-1}$ per layer of averages because a two-input mean is nonexpansive. Choose $k,r$ with $m2^{-k}+k2^{-r-1}\le\varepsilon$. They are polynomial in the input length. Combining these circuits with the original Max and Min choices gives an acyclic circuit for each row, treating source state values as leaves. Write $G$ for the resulting simultaneous operator. It maps the cube into itself and satisfies $\|G(q)-F(q)\|_\infty\le\varepsilon$ throughout the cube.

### A single deterministic game and exact decoding

Provide two absorbing vertices with deterministic self-loop rewards zero and $1-\delta$, giving discounted values zero and one. Each circuit gate becomes a deterministic vertex of the corresponding owner. An edge for a term $u+c$ leads to its predecessor vertex and has reward $c$. The leaf representing state $s$ is the designated root vertex for row $s$. Put two clamp vertices at each root to enforce $[0,1]$. The root is Min, choosing between the constant one and a zero-reward edge to an auxiliary Max vertex. This Max vertex chooses between zero and a zero-reward edge to the row gate. The root edge to the one vertex uses reward $1-\delta$, giving exactly one at discount $\delta$. At discount one in the conditional circuit comparison, the clamp uses the exact constants zero and one.

Let $d\ge1$ bound the depth of a row circuit, including the two clamp vertices, with the state leaves held fixed. Choose a binary rational $\delta=1-2^{-h}$ with $h\ge 1$ and $2d(1-\delta)\le\varepsilon$. Fix any leaf vector $q\in[0,1]^n$. The payoffs obtained by evaluating the deterministic gate network at discount $\delta$, stopping at the fixed leaves, approximate the circuit at discount one. The exact nondiscounted gate values have absolute value at most two because every average macro takes inputs in $[0,1]$ and each internal pair preserves its sum and has gap at most one. At an ordinary edge the error is at most the predecessor error plus $2(1-\delta)$. A bound edge evaluates to its exact constant. Min and max preserve the largest edge error, so the error at each root is at most $2d(1-\delta)$.

The full deterministic discounted game has a unique value vector. Its projection $q$ to the roots lies in $[0,1]^n$ by the clamps. With these roots held at $q$, the remaining row circuits evaluate to the same values as in the full game by their Bellman equations. Hence $\|q-F(q)\|_\infty\le2\varepsilon$. Contractivity of $F$ gives

```math
\|q-w\|_\infty\le\frac{2\varepsilon}{1-\gamma}=\frac{1}{8Q^2}.
```

Each $w_s$ is the unique rational of denominator at most $Q$ in the corresponding interval of radius $1/(8Q^2)$. It can be recovered by continued fractions in polynomial time. This yields all $v_s$ and attaining actions in the original Bellman equations, hence optimal positional strategies. If a target answer gives optimal positional strategies alone, their exact discounted values follow from one rational linear system before decoding. Construction and recovery are polynomial in the full binary input length. The reverse search reduction is inclusion of the deterministic special case.

## A reduction to mean-payoff strategy search

The max-average reduction also accepts each constraint $x_i\le\sum_j w_j x_j$ with nonnegative binary rational weights summing to one. Omit zero-weight terms so the sum is defined on the extended domain as well. After clearing a row's denominators, include its integer coefficients and its multiplier on $\rho$ when choosing $h$. All box and violation bounds remain valid. For a row with $m$ weights on $[-B,B]$, use rounded cumulative weights and the shared binary tree above. The rounding error is at most $Bm2^{-k}$. Use the range-preserving upper approximation to each pairwise average with $W=2B$ and add a final upward offset $Bm2^{-k}$. The circuit bounds the original weighted mean from above and its excess is at most $2Bm2^{-k}+Bk2^{-r}$. Choose $k,r$ so this is less than $1/B$. All gates again give one-sided max-atom constraints, with the same exact feasibility and witness recovery.

Use the normalized operator $F$ of the discounted game and its dual $\bar F(y)=\mathbf 1-F(\mathbf 1-y)$, obtained by swapping the players and complementing the normalized rewards. Form one system with $0\le x,y\le1$, $x\le F(x)$, $y\le\bar F(y)$, and $1/2\le(x_s+y_s)/2$ for every state $s$. Each action uses an auxiliary variable upper bounded by its convex combination. Each state is upper bounded by the appropriate minimum or maximum of these action variables. This is an exact existential encoding of the Bellman inequalities. The pair $(w,\mathbf 1-w)$ is feasible. Conversely monotonicity and contraction give $x\le w$ and $y\le\mathbf 1-w$ by iterating the respective operators. The pairwise average bounds then force $x=w$ and $y=\mathbf 1-w$.

Apply the weighted max-average reduction and recover a witness from the returned positional Max strategy as above. Every such optimal strategy yields the exact source values and permits recovery of optimal source strategies. The target has nonnegative value because the original system is feasible. It is the target strategy that supplies the max choices used in witness recovery. The same two-vector construction works for stopping simple stochastic games by using the stopping-game subsolution bound for the original game and its dual.

## Relation to existing reductions and to affine markets

Zwick and Paterson reduce deterministic mean-payoff decision to deterministic discounted decision and then to simple stochastic games. The max-average reduction above supplies the opposite simple-stochastic-to-mean-payoff direction. For stochastic mean-payoff value and policy search, the stopping-game and max-atom route gives a polynomial-time Turing reduction by the existing stopping-game threshold reduction. The discounted search constructions use a single instance for the stated discounted model. [Zwick and Paterson, Sections 5 and 6](https://www-verimag.imag.fr/~iosif/LAT/mean-payoff.pdf) · [Bodirsky, Loho and Skomra, Theorem 3](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2025.145)

An exact rational replay checked 6,875 midpoint circuits, 150 weighted conditional evaluations, and two three-state games with stochastic self-feedback. In the latter the normalized rows were $F_1(q)=3q_1/4$, $F_2(q)=1/4+3q_2/4$, and $F_0(q)=\operatorname{opt}(1/8+3(q_0+q_1)/8,\ 1/16+3q_0/16+9q_2/16)$. Using $k=r=24$ and $\delta=1-2^{-32}$ gave 827 vertices per compiled instance. Exact Bellman verification and rational reconstruction returned $(10/13,0,1)$ for the Max example and $(1/5,0,1)$ for the Min example.

The October 2026 discussion of quasipolynomial algorithms still described the opposite polynomial reductions from simple stochastic games as open. The degree of novelty of the averaging circuit and its consequences remains subject to external review. The market question that gave rise to the circuit has a separate physical-flow condition. [Parys, October 2026 seminar](https://mimuw.edu.pl/en/seminars/talk/quasipolynomial-algorithms-for-mean-payoff-and-simple-stochastic-games/)

GPT-6.2 Astra in Codex independently recovered the published recurrence in centered form, derived the stopping-game reduction and the two-vector search encoding, located prior work, and independently checked the proofs. The coordinating Codex session developed the general feasibility and exact witness recovery proofs and checked the discounted compiler with rational arithmetic. This is a research draft awaiting independent human review.
