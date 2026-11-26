# L1a Exponentially many strict threshold drops on one boundary

**Theorem.** For each integer \(h\ge1\) there is a strictly signed game with \(2h+2\) targets, \(O(h)\) positive-prior types, unit attacker losses, and two defender gains. The defender has one resource. The exact continuation from L2 makes at least \(2^h-1\) strict Algorithm 4 threshold drops in one phase with an unchanged open boundary. The conclusion holds for any fixed seed order and any exact optimizing flow choices. The dense rational input has \(O(h^3)\) bits.

The lower bound counts distinct landing thresholds on a single run. It uses a changing minimum-cost transportation value along a proportional capacity ray. B3e and B3f exhibit many events at a constant threshold, a different kind of continuation cost. [Exact Algorithms 3 and 4](L2-exact-arithmetic-audit.md#state-and-exact-steps) · [Long fixed-flow path](B3e-parametric-path-lower-bound.md#what-algorithm-3-traces) · [Forced flow changes](B3f-forced-flow-switches.md)

## A small network with an exponentially long cost curve

Start with one unit-capacity arc from \(s\) to \(t\) of cost zero. At layer \(i\ge1\), the old network has throughput \(U=2^{i-1}\). Add new terminals \(s',t'\) and four arcs, each of capacity \(U\). Give \(s'\to s\) and \(t\to t'\) cost zero, and \(s'\to t\) and \(s\to t'\) cost \(A_i=2^i-1\). This is the four-arc shape used in the A4h counting construction. [Disser and Skutella, §3.1](https://www2.mathematik.tu-darmstadt.de/~disser/pdfs/DisserSkutella18.pdf)

At new flow value \(u\in[0,2U]\), the old flow value \(f\) can range from zero to \(\min(u,2U-u)\). The sum on the two expensive arcs is \(u-f\). Every old marginal cost is at most \(2(U-1)<A_i\), so minimum cost takes \(f=\min(u,2U-u)\). Thus the marginal costs on the first half repeat the old sequence and those on the second half are \(2A_i\) minus the old sequence in reverse. Inductively at depth \(h\) the minimum-cost curve \(C_h\) has the successive slopes

\[
 0,2,4,\ldots,2(F-1),\qquad F=2^h,
\]

on the \(F\) unit intervals. The graph is acyclic, has \(2h+2\) vertices and \(4h+1\) arcs, and total arc capacity \(D=4F-3\). Write \(O_v\) for the outgoing capacity at \(v\). Then \(O_s=F\), \(O_t=0\), and \(O_v\le F\) for every internal vertex. [Four-arc counting network](A4h-complete-candidate-generation.md#a-single-boundary-table-and-a-two-dimensional-load-hull)

## Turn the curve into a proportional transportation ray

Make each vertex a target. For each arc \(e=(v,w)\) create a row of mass equal to its capacity. Give this row cost zero at \(v\), its arc cost at \(w\), and a large penalty \(P=8DF+1\) elsewhere. In each internal column \(v\) add a row of mass \(F-O_v\), with cost zero at \(v\) and \(P\) elsewhere, omitting zero rows. Add one row of mass

\[
 K=16PF(D+nF)
\]

with cost zero at \(t\) and \(P\) elsewhere, where \(n=2h+2\). Write \(S=(n-2)F\) and \(T=K+F+S\) for the internal load and the total row mass.

At ideal column margins

\[
 b_s=F-u,\qquad b_t=K+u,\qquad b_v=F\quad(v\notin\{s,t\}),
\]

allowed arc-row assignments encode exactly the network flows of throughput \(u\). The mass sent to an arc's head is its network flow. For \(u\) on the quarter grid in \([0,F]\), the least transportation cost equals \(C_h(u)\) even with the penalty edges available. A legal flow costs at most \(D(F-1)\). Transportation integrality after scaling by four gives an optimal vertex with every positive entry at least \(1/4\). One penalty edge would cost at least \(P/4>D(F-1)\). The dedicated rows therefore stay at their designated columns in an optimal vertex and the equality of value functions holds on this grid.

Now use the actual margins

\[
 b'_t=K+u,\qquad b'_v=F(1+u/K)\ (v\notin\{s,t\}),\qquad
 b'_s=F-u-uS/K .
\]

They are positive throughout the witness range \(0\le u\le F-1/2\). The perturbation moves \(\rho=uS/K\) units from \(s\) to internal columns. Reassigning those amounts within the same rows shows that the optimum can change by at most \(P\rho\le1/16\). The reverse reassignment gives the opposite inequality. Write \(C(u)\) for the true transportation optimum with \(b'(u)\). At every integer \(j=1,\ldots,F-1\), the ideal slopes give second difference \(1/2\) for the three points \(j-1/4,j,j+1/4\). The perturbed second difference is at least \(1/2-4/16=1/4\). It follows that each of the \(F-1\) disjoint open intervals \((j-1/4,j+1/4)\) contains a point where \(C\) is not locally affine.

## Every equilibrium in the witness range has the same open boundary

Give each row prior equal to its mass divided by \(T\). Let \(c_{iv}\in[0,P]\) be its transportation cost above. Set uncovered utility to \(H{\bf1}[v\ne s]-\eta c_{iv}\), with \(H=1/(2n)\), \(\eta=H/(4P)\), and unit attacker loss. Take defender gains \(\beta_s=\beta_t=T/K\) and \(\beta_v=T/F\) on all internal vertices. Put \(\lambda=1+u/K\) for the game threshold corresponding to a witness parameter.

For any equilibrium state with \(\lambda\ge1\), the source is uncovered. Indeed, if it receives any attack, that row's comparison with \(t\) gives \(x_t-x_s\ge H-\eta P>0\). Then \(t\) is covered and must receive at least \(K\lambda/T\) of the mass. Since \(K>T/2\), the source's remaining mass is strictly less than \(K\lambda/T\), giving score below \(\lambda\). With zero attack the score is below \(\lambda\) as well. Every covered nonsource target must receive attack, and a row attacking it compares it to the uncovered source. Thus its coverage is at most \(H+\eta P=5H/4<1\).

In the witness range all targets are unsaturated. The sum of the nonsource score caps on their normalized loads is \(\sum_{v\ne s}b'_v/T\), strictly below one. The source therefore receives positive attack. A row sending any flow there compares it to every nonsource target, giving \(x_v\ge H-\eta P>0\) on each. So throughout the witness range the open boundary is exactly \(B=V\setminus\{s\}\), and the margin vector in unnormalized units is \(Tz=b'(u)\).

At initialization the source obtains zero attack, since all nonsource offers are strictly greater there. The initial threshold must exceed the top of the witness range or the nonsource caps would not take all mass. At budget one the threshold is strictly below one. Otherwise the source would be uncovered and the other coverages would sum to at most \((n-1)5H/4<1\). Algorithm 3 cannot reach a cap while moving at \(\lambda\ge1\), because all its intermediate states preserve equilibrium at that threshold and satisfy the same strict upper coverage bound. Hence crossing the range uses Algorithm 4 drops.

## Non-affinities force actual landing thresholds

During an Algorithm 4 call, hold coverage at its input vector and interpolate linearly between its old and new feasible flows. At fractional position \(\theta\), the threshold decreases linearly. The old boundary keeps scores equal to that threshold, previously full columns keep enough attack, and unsaturated columns outside the old boundary have strictly lower score for all \(\theta<1\). This gives equilibrium certificates at every intermediate threshold and preserves the old open boundary up to the endpoint.

On the part of this interpolation in the witness range, the margins are \(b'(u)\). Because the attack losses are unit slopes, a best-response flow is a minimum transportation cost flow at these margins. Summing the row comparisons over a competing flow with the same margins cancels each fixed column offset \(H{\bf1}[v\ne s]-x_v\). The interpolated flow is affine in \(u\), so \(C(u)\) is affine on this part of the call. Therefore a non-affinity inside the band cannot be interior to any interpolated call. Since the terminating L2 run crosses the band, it must be an actual Algorithm 4 landing threshold.

There are at least \(F-1\) distinct landings, by the disjoint intervals above. Each has unchanged \(B\), including a call that starts above the witness range, since its old boundary persists before its landing and every state sufficiently close to that landing has \(B=V\setminus\{s\}\). All calls counted belong to the same phase. The dense table has \(O(h^2)\) entries of \(O(h+\log h)\) bits. The bound is therefore exponential in the number of targets and at least \(2^{\Omega(L^{1/3})}\) in binary input length \(L\). It holds for two gain values without a bound on the number of distinct prior masses. [Distinct-prior and gain upper bounds](B3b-closed-group-rank.md#thresholds-and-changes-of-seed)

The construction has more types than targets. To equalize the counts, add targets with uncovered utility $-2$ for every type, unit attacker loss, and one of the two existing gains. Every original target has utility greater than $-2$ throughout the coverage box, so no type attacks an added target. Added targets stay outside the positive-threshold boundary. The $2^{\Omega(N)}$ lower bound on threshold drops thus also holds with $N$ targets and $N$ positive-prior types, where $N=\Theta(h)$.

## Tight worst-case count in balanced dimensions

**Corollary.** For the exact L2 continuation on strictly signed games with equal numbers of targets and positive-prior types, both at most \(N\), the worst-case number of strict Algorithm 4 drops within one unchanged open-boundary phase is \(2^{\Theta(N)}\).

Each counted drop preserves the boundary \(B\) and leaves coverage unchanged. The budget is still unfilled. L2's maximum-drop argument therefore gives a successful Algorithm 3 input at the new threshold. Let \(U\) and \(S\) be the rows and targets reachable from its seed. With \(k\) positive-prior types, \(U\subseteq[k]\), \(\varnothing\ne S\subseteq B\), and the weighted Hall equality gives

\[
  \lambda=\frac{\sum_{i\in U}p_i}{\sum_{t\in S}1/\beta_t}.
\]

The landing thresholds are distinct because the threshold is nonincreasing and each counted drop is strict. The empty numerator gives at most one value, zero. There are at most \(1+(2^k-1)(2^{|B|}-1)\) possible values altogether, which is at most \(4^N\) when \(k\) and the number of targets are at most \(N\). The construction above has at most \(6h+2\) positive-prior types, including its \(4h+1\) arc rows, at most \(2h\) internal fillers, and the terminal row. After padding the targets to match, taking \(h=\lfloor(N-2)/6\rfloor\) gives \(2^{\Omega(N)}\) drops for every sufficiently large \(N\). The tight count of all outer calls is the separate L2a question. [Hall-ratio count](B3b-closed-group-rank.md#thresholds-and-changes-of-seed) · [Exact L2 steps](L2-exact-arithmetic-audit.md#state-and-exact-steps) · [L2a](../investigation/L2a.md) · [PR review](https://github.com/robbiemu/bayesian-simple-security-games/pull/17#issuecomment-7179946015)

## Exact small replays

Run `python3 experiments/l1a_threshold_replay.py 1 2 3 4 5` from the project root. The replay uses rational arithmetic, the first eligible seed in target order and the identity transportation normalization, a valid minimum-cost choice because the logarithmic costs all vanish. At each threshold reset it finds one optimizing flow by a lower-bound transportation solve. It checks the active graph and the predicted witness intervals during the full run. [Replay script](../experiments/l1a_threshold_replay.py)

| Depth \(h\) | Strict drops with \(B=V\setminus\{s\}\) unchanged | Total Algorithm 4 calls | Successful coverage steps |
| --- | ---: | ---: | ---: |
| 1 | 3 | 6 | 6 |
| 2 | 7 | 12 | 13 |
| 3 | 15 | 22 | 24 |
| 4 | 31 | 41 | 47 |
| 5 | 63 | 76 | 83 |
