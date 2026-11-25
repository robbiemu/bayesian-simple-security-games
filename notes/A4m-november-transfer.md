# A4m · Fixed-point algorithms for exact market clearing

Two fixed-point results give new market algorithms. The unrestricted polynomial-time question remains open.

| Market result | What the source supplies | What the market proof supplies |
| --- | --- | --- |
| **Polynomial bit time on markets passing a factor LP** | OpenAI's November 24 manuscript gives polynomial total bit time for finding a small residual of a sup-norm nonexpansive self-map of a cube. Its accuracy parameter counts bits. | A path inequality and a polynomial-size LP certify nonexpansiveness of the frozen assignment map. Rational assignment solves answer the oracle queries. Preserving all frozen ties gives exact least prices through A4a's repair. |
| **Exact general search in $2^{O(\sqrt{\tau}\log(2+L))}\mathrm{poly}(L)$ bit time** | Ghorbani, Lopes and Mnich's October 20 preprint gives a least-fixed-point algorithm for a lattice map with unit increments in a supplied block. Its separate cube-root bound uses switch-graph structure. | Conservative splits and comparisons round the market map. Pinning a minimum vertex cover leaves independent scalar solves. Block search on the cover of size $\tau$ and rational recovery finish the algorithm. |

- **November source.** Use the nonexpansive part of the result named *Approximation in max norm*, including equality in the nonexpansiveness inequality. The source returns an approximate residual. Exact price and flow recovery in this setting comes from the market proof. The published Lean scope for rational linear programming is separate from the fixed-point oracle theorem used here. [November theorem, pinned edition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Strongly-polynomial-linear-programming-November-24-2026/build/contractions.tex#L1-L38) · [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/380.md) · [Market certificate and exact recovery](A4m-path-sensitive-freezing.md)
- **October source.** Use the generic block algorithm in Theorem 1.2 of *ARRIVAL in cube-root subexponential time*. The imported solver handles the least fixed point of a block by oracle evaluations. The market construction gives a polynomial-bit integer map on which those calls can be made and proves the dimension and accuracy bounds. [October Theorem 1.2](https://arxiv.org/html/2610.28241v1#S1.Thmtheorem1.2) · [Market discretization and recursive bit bound](A4m-discrete-contraction.md)

The path certificate covers some slope matrices outside the earlier column condition in A4a and can be computed before the tight support is known. An inverse-polynomial strict gap suffices by ordinary iteration. The general market algorithm works for arbitrary positive slopes and binary quantities using the October theorem alone. Its game bound uses $\min(n,k)$ in place of $\tau$ for $n$ targets and $k$ positive-prior types. [Market oracle reduction and repair](A4c-any-clearing-equilibrium.md#transfer-to-the-exact-game) · [Vertex-cover refinement by ChatGPT 6 Pro](https://github.com/robbiemu/bayesian-simple-security-games/pull/12#issuecomment-7151840713)

## What remains

The factor LP is a sufficient condition. For the unrestricted problem the block recursion gives a subexponential time bound. One route is a polynomial-time fixed-point algorithm for the integer maps made of rational splits, conservative comparisons, additive merges and clipping. Another requires a polynomial-size max-norm formulation with an evaluator for all of its oracle queries. Two markets with the same local A4f formula require opposite extremal labels, so a single native-map evaluation does not give the manuscript's oracle. The exact formulation on cut coordinates has exponential size. [Interface examples and exact cut lift](A4m-extremal-price-interface.md)

## Reproduction and credit

The proofs cite the source versions separately and state the exact imported hypotheses. Robert Thomas Collins directed the investigation. GPT-6.2 Astra passes derived the path bound, the transfer rounding that preserves unit increments, and the block transfer, and an independent Astra pass audited both positive results. The coordinating Codex session tightened the factor certificate, checked the quantitative recovery, and assembled the rational replays. The max-norm replay checks the exact examples and least-price tie repair at a nonzero frozen residual. The lattice replay checks 3,121 input points, 10,048 lattice increments and 8,464 increments of conditional maps on small boxes. It also checks all 256 pins and 480 reduced increments for a mixed vertex cover, and reconstructs the exact rational price and allocation from a large mesh using scalar bisection. The imported block solver and game reduction are justified in the proofs.

~~~sh
python3 -B experiments/a4m_maxnorm_replay.py
python3 -B experiments/a4m_lattice_replay.py
~~~
