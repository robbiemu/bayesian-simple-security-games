# Verification for the fixed-flow continuation paper

The paper records the November 21, 2026 argument. The TeX and PDF in this directory are the prepared public edition. The forcing lemma for the family, the segment count, and the binary input-length bound are established in the written proof. The separate B3g audit traces those arguments and checks a second finite example. [Manuscript (PDF)](fixed-flow-continuation-lower-bound.pdf) · [Construction](../notes/B3f-forced-flow-switches.md) · [Model-assisted audit](../notes/B3g-lower-bound-audit.md)

## Lean library checks

Run `lake build LibraryChecks` from `lean/`. The modules cover affine path weights, finite assignments and doubly stochastic decomposition, finite weights, rational arithmetic, and interval and counting facts. The November 25 check used Lean 4.36.0 and mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. `lake --no-cache build LibraryChecks` completed successfully in the existing pinned workspace. [Lean check scope and inputs](../lean/README.md#what-the-examples-check)

## Exact finite replays

From the repository root, run `python3 -B experiments/b3f_forced_flow_replay.py`. With Python 3.13.3, the four-target example reproduced three distinct assignments at budgets $1/4$, $5/8$, and $1$, each with assignment gap two. The three-target replay enumerated the vertices of the compatible coverage polytope for all six permutations. It found exactly $(1,2,0)$ at budget $1/2$ and $(2,1,0)$ at budget $1$. The publication check prepared and ran the replay in OpenAI Codex using standard-library rational arithmetic. [Exact replay](../experiments/b3f_forced_flow_replay.py)

The existing Research map workflow replays the related B3e continuation example. It verifies seven exact steps and three distinct Hall-witness families at threshold $1/5$. The workflow's Lean build targets the separate `StochasticGames` library. The `LibraryChecks` build and the B3f/B3g replay above are local reproductions. [Workflow](../.github/workflows/check.yml) · [B3e replay](../experiments/b3e_parametric_replay.py)

## Companion developments

The Kintali companion has its own pinned Lean build, Python and Lean solver replays, and axiom audit. The H4 stochastic-game reduction has a Lean compiler theorem and dedicated CI checks. [Kintali verification record](kintali-lean/verification.txt) · [H4 compiler and replay](../lean/README.md#stochastic-game-reduction)
