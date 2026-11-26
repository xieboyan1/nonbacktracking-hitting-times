# Vertex hitting times for non-backtracking walks with fixed and stationary starts

On a cycle of length 23, add the chord joining vertices 0 and 8. Start at vertex 2 with no previous edge. How long does it take to reach vertex 1? The non-backtracking walk takes **13 steps on average**. The simple random walk takes **1843/143**, or about 12.89. This graph gives a counterexample to the fixed-pair comparison in Corollary 5 of Altisen, Devismes, Gerbaud and Lafourcade. Breen and coauthors had already obtained the non-backtracking value in their formula for chorded cycles. [2012 corollary](https://www-verimag.imag.fr/PUBLIS/uploads/cizib1712.pdf#page=8) · [Chorded-cycle formula](https://arxiv.org/html/2510.06650v1#A1.SS1)

[Read the research manuscript (PDF)](paper/manuscript.pdf) · [LaTeX source](paper/manuscript.tex) · [Lean theorem index](lean/README.txt) · [中文核查笔记](notes/referee_audit_zh.html)

## Results and proofs

| Result | Lean source |
| --- | --- |
| On the 23-vertex graph, the excess for the specified start is exactly 16/143. | [Witness](lean/Witness.lean) |
| On theta graphs with path lengths 1, p and p², the ratio of the two means for an adjacent start and target is asymptotic to p/8. | [Theta](lean/Theta.lean) |
| For a fixed target in a finite connected simple graph with at least two vertices, sampling the start proportionally to degree gives a non-backtracking mean at most the ordinary mean. Equality holds exactly when all neighbours of the target are leaves. After averaging targets with the same law, equality holds exactly on the single-edge graph. | [Walks](lean/Walks.lean) · [Strict](lean/Strict.lean) |
| On a finite connected simple graph of minimum degree at least two with a branching vertex, the projected vertex Kemeny constant is at most the vertex hitting-time constant. Equality holds exactly when the mean return to each vertex is independent of the first neighbour chosen. The variance of these conditional means controls the gap. | [Kemeny](lean/Kemeny.lean) · [Forward](lean/Forward.lean) |

The first step is uniform among all neighbours. Later steps exclude the previous vertex whenever another neighbour exists. At a leaf the walk must reverse. A walk starting at its target has hitting time zero.

## Reproduce the checks

The three Python programs require Python 3.9 or later and use the standard library. Run from the repository root with assertions enabled.

```sh
cd supplement
python verify_theta_ldr.py
python independent_check.py
python check_trace_variance.py
```

The first program solves rational linear systems. The second uses a separately labelled graph and computes survival probabilities. The third computes the Kemeny constants and the return-time variance on five graphs. [Expected output](supplement/expected_output.txt) · [Computational details](supplement/README.txt)

For the formal proofs, install [elan](https://github.com/leanprover/elan). From the repository root, use the pinned Lean 4.19.0 and mathlib v4.19.0 environment.

```sh
cd lean
lake update
lake exe cache get
lake env python verify.py
```

The verifier builds all 15 local modules in a temporary directory, treats warnings as errors, and checks the 12 final axiom reports. It prints the SHA-256 digest of each Lean source file. [Recorded verification](lean/verification.txt)

To build the manuscript, run `tectonic manuscript.tex` in `paper/`, or run `pdflatex manuscript.tex` twice there.

## Research status and attribution

This repository accompanies a research manuscript. The manuscript describes the role of generative AI in the derivations, formalization and writing. The Chinese audit and its dated literature search record the interpretation of the earlier corollary and the limits of the priority search. [Audit](notes/referee_audit_zh.html) · [Search record](notes/priority_search.txt)

## Licenses

The Lean and Python code is available under the [MIT License](LICENSE). The original manuscript, research notes, documentation and verification transcripts are licensed under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/). For attribution, cite the manuscript title and link to the repository version used. Third-party works cited in the manuscript retain their own terms.
