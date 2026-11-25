<!-- Generated from catalog/ and records/ by scripts/build_map.rb -->

# A4m · Transfer max-norm and lattice fixed-point algorithms to affine markets

**🟨 Partial result**

The pinned November preprint gives conditional polynomial bounds under an alternating-path LP or logarithmic vertex-cover size. The October solver gives exact subexponential search using vertex-cover elimination and direct integer flow recovery. The source audit records the scope of the imported statements.

**Open task** — Find a polynomial-time block search for the resulting integer maps or a polynomial-size max-norm formulation for general markets.

[Read the evidence](../notes/A4m-november-transfer.md) · [Investigation index](README.md)

Parent question · [A4 · Solve the binary-mass minimum-price market with arbitrary slopes](A4.md)

## Relevant work

- A4m **extends** [A4a · Test contraction near factorized slopes](A4a.md). The path-based factor LP certifies additional frozen assignment maps, and the original tie repair returns the minimum. [Evidence](../notes/A4m-path-sensitive-freezing.md)
- A4m **uses** [A4f2 · Construct equivalent buyer–good formulations](A4f2.md). The signed node contraction admits an integer approximation that preserves unit increments. [Evidence](../notes/A4m-discrete-contraction.md#round-transfers-while-preserving-unit-increments)
- A4m **extends** [A4g · Test bounded search and shortcuts in the implicit basis graph](A4g.md). A conditional convex quadratic program handles balanced slopes and localizes hinge sign guesses to unbalanced biconnected blocks. [Evidence](../notes/A4m-structural-elimination.md#a-convex-quadratic-program-for-a-balanced-interior)
- A4m **tests the search interface of** [A4h · Generate complete candidate lists before the Hall search](A4h.md). Identical local formulas can require opposite labels and different solution regions, so a single local evaluation cannot select the correct region. [Evidence](../notes/A4m-extremal-price-interface.md#identical-local-formulas-and-opposite-required-signs)

## Contribution log

- [Obtain a subexponential exact market solver by lattice block search](../records/02970891-b5d8-42fe-8b87-a99dcfe5d543.md) · result · proof · Robert Thomas Collins, OpenAI Codex · GPT-6.2 Astra, GPT-6, Python
- [Certify exact polynomial-time clearing with a path bound on frozen prices](../records/e3aa26cd-1de3-424f-97c3-82db725e63cf.md) · result · proof · Robert Thomas Collins, OpenAI Codex · GPT-6.2 Astra, GPT-6, Python
- [Sharpen the exact lattice bound by pinning a vertex cover](../records/97fe3bb1-1a6c-4fc7-93f2-3e153d799d0c.md) · result · proof · ChatGPT 6 Pro, Robert Thomas Collins, OpenAI Codex · ChatGPT 6 Pro, GPT-6, Python
- [Search smaller market boundaries by quadratic programs and cut coordinates](../records/3ffbd547-faad-440b-89ee-94c498f81ebc.md) · result · proof · Robert Thomas Collins, OpenAI Codex · GPT-6.2 Astra, GPT-6, Python
- [Read an exact feasible flow from the lattice transfers](../records/affc1f41-6298-4cef-817e-f06d2ab4f233.md) · result · proof · Robert Thomas Collins, OpenAI Codex · GPT-6.2 Astra, GPT-6, Python
- [Audit the scope of the pinned November fixed-point dependency](../records/1033057c-197a-4873-a7bf-fe5a476f91df.md) · review · supports · Robert Thomas Collins, OpenAI Codex · GPT-6, Python

[Join an existing discussion](https://github.com/robbiemu/bayesian-simple-security-games/issues?q=is%3Aissue+in%3Atitle+%22%5BA4m%5D%22) · [Contribute to this question](https://github.com/robbiemu/bayesian-simple-security-games/issues/new?template=research.yml&title=%5BA4m%5D+) · [Contributor guide](../CONTRIBUTING.md)
