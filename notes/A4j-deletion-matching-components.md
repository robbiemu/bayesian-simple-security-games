# A4i1b · Count deletion-matching changes by allowed-edge components

At a fixed reached-set phase, factor each deleted buyer's matchings across the allowed-edge components of its balanced viable graph. The strict-decrease argument then counts a **sum of local product changes**. The maximum-degree-three return-edge control illustrates when the components can merge. The bound applies to the existing ascent.

## Factor once, then charge local changes

Let $R,S$ be the fixed reached buyers and goods, with $|R|=|S|+1$. For each omitted buyer $r$, choose any perfect matching of the viable bipartite graph on $R\setminus\{r\},S$. Contract its pairs, directing an arc from the pair of a buyer to the pair of any good she can buy. Use the strongly connected components of this digraph, interpreted as sets of original pairs. This is the standard allowed-edge decomposition. [Tassa, Theorem 2.2 and Algorithm 2](https://arxiv.org/pdf/1107.4711#page=3)

Every other perfect matching specifies a permutation of the pairs relative to the reference matching. Each of its permutation cycles stays inside one strongly connected component. Hence every perfect matching of **any** tight subgraph factors across the same components, even when reference edges are no longer tight. Conversely, perfect matchings of all the component subgraphs combine independently. The global minimum product equals the product of the component minima.

At an internal price event, the old chosen minimum matching for each $r$ remains tight. Its restrictions individually attained their local minima, so they certify that every component minimum weakly decreases. The A4i1b strict progress lemma forces a strict decrease in some deletion's global minimum and hence some local minimum. If $P_{r,C}$ is the set of possible viable products for component $C$ and deleted buyer $r$, the number of internal events in this phase is at most
\[
 \sum_{r}\sum_C (|P_{r,C}|-1)
 \ \le\ \sum_r\sum_C (2^{h_C}-1),
 \qquad h_C=|E_C|-|V_C|+1.
\]
For the second inequality, compare each component perfect matching with its reference matching in the binary cycle space of the original bipartite component. Logarithmic cycle rank per deletion component in every visited phase therefore suffices for polynomial time. The ascent already finds the needed global minima, and it need not compute or know these components to obtain the bound. [Matching survival, strict drops and bit cost](A4j-unit-matching-ascent.md#matching-values-bound-the-number-of-steps)

## Controls and comparison with the simple-cycle charge

In the open prime chain, deleting the root leaves $m$ square components. Deleting either buyer of block $i$ forces the path of bridges through that block and leaves the $m-i$ later squares independent. Thus the maximum rank is one and the sum of the rank bounds is $m+2\sum_i(m-i)=m^2$. The earlier nonunit-cycle count gives the sharper $m$ bound on this graph. The actual equal-bid run takes just one update. [Original control and nonunit-cycle bound](A4j-deletion-matching-chains.md)

For $m\ge2$, add the unit-slope return offer $b_m B_1$. This preserves degree at most three on both sides. With the root omitted the alternating digraph is now strongly connected, since the bridges and return connect the squares in both reachability directions. Its bipartite cycle rank is $m+1$. The example changes this structural certificate. It gives no price-update lower bound.

For the other direction, take $t$ square blocks indexed by vertices of $K_t$, and let the root offer on every $A_u$. For each edge $e=uv$ introduce a good $G_e$ with a private buyer offering only there, and also offers from $b_u$ and $b_v$ to $G_e$. With the root omitted all private goods are forced and the square choices are independent, giving $2^t$ root-deletion products when their diagonal labels use distinct primes. Omitting a square buyer forces the root into that square and leaves the other squares independent. Omitting the private buyer of $G_{uv}$ forces every other private pair. The remaining choice is which endpoint sends its $b$ buyer to $G_{uv}$ and receives the root on its $A$ good. This leaves one component of five pairs and twelve allowed edges, hence rank three, along with the unaffected squares. All deletions have component rank at most three.

The subgraph $b_u-G_{uv}-b_v$ subdivides the clique. Distinct prime slopes on its incidence offers make every simple cycle there nonunit. Hamiltonian cycles alone give $(t-1)!/2$ such certificates. Thus neither the number of global products nor the count of nonunit simple cycles gives a polynomial phase bound on this example. The additive component bound does. With all viable bids two, insert all private and square buyers before the root. These prefixes clear at zero, and the root reaches the whole incidence graph. This realizes the comparison in a single phase. It does not force a long ascent.

## Exact checks and credit

Run `python3 -B experiments/a4j_deletion_scc_replay.py`. The replay checks the open and returned chains at $m=1,2,3,5,8,10$ (return for $m\ge2$), every one of 1,408 tight-edge restrictions of the two-block chain across its deletions, the selected local minima in actual shaded-chain runs, and the subdivided-clique examples at $t=3,4,5$. [Replay](../experiments/a4j_deletion_scc_replay.py)

OpenAI Dot's background comparison supplied the additive count, chain enumeration and return-edge control. The original control and replay came from the separately credited Dot cross-project comparison, inspired by Cinna Davis's catalogue's matching-excess proof and the Hartke–Stolee–West–Yancey binary matching construction. The decomposition is Tassa's standard allowed-edge result and the strict progress lemma is the project's pre-existing A4i1b ascent. Robert Thomas Collins requested the audit. GPT-6.2 Astra independently checked it and supplied the subdivided-clique separation and exact replay. [Davis catalogue at the cited revision](https://github.com/1337isnot1337/solved-conjectures/blob/758066055ef49c2c66cb1087918ae62ad75e7ac1/results/hartke-stolee-west-yancey-matching-excess/PROOF.md) · [Pinned original ascent](https://github.com/robbiemu/bayesian-simple-security-games/blob/74589d93e4b078608e0a8ddb4b1e86722634f9ee/notes/A4j-unit-matching-ascent.md)
