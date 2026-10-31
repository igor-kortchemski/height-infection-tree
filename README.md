# Height and active profile of the infection tree

Lean 4 proofs of height and active-profile asymptotics for the embedded SIR
infection tree. The mathematical source is *The height of the infection tree*
by Emmanuel Kammerer, Igor Kortchemski and Delphin Sénizergues
([public paper reference](https://arxiv.org/abs/2504.03526v1)).

This repository contains the complete formalization library and a small
Palomar statement interface. It is being prepared privately for a possible
public release. No Palomar submission or registration has occurred.

## Read the results

| Paper result | Lean certificate | Meaning |
| --- | --- | --- |
| `thm:main` | [`HeightPaper.mainTheorem`](HeightPaper/MainTheorem.lean) | Logarithmic terminal-height limit for arbitrary asymptotic infection-rate sequences, including both early extinction and macroscopic survival. |
| `thm:profil` | [`HeightPaper.strongProfileTheorem`](HeightPaper/StrongProfileTheorem.lean) | Strong asymptotics for active vertices at exact lattice heights, including the Gaussian logarithmic correction and the survival event. |
| Following uniformity paragraph | [`HeightPaper.uniformStrongProfileTheorem`](HeightPaper/UniformStrongProfileTheorem.lean) | The profile estimates with thresholds common over compact epidemic-parameter and tilt sets. |

Start with [Challenge.lean](Challenge.lean): 293 lines of concrete definitions
and these three statements. [Solution.lean](Solution.lean) exposes their proofs.
The three theorem holes in the Challenge are deliberate statement artifacts;
there are no definition holes or implementation proof holes.

The full library retains certificates for all **31 numbered results**, with
explicitly recorded corrections. The [formalization report](FORMALIZATION_REPORT.md#numbered-result-inventory)
maps each result to its certificate and explains departures from the paper's
arguments. Only the three declarations above are selected by this
[Comparator configuration](comparator.json).

## Scope and source correspondence

The formal model is the explicit embedded epidemic event chain, with uniform
choice of the active infector or recovering vertex. The continuous-time
Poisson/exponential construction and its equality in law with this chain are
not separately formalized. The numerical approximation to the critical
parameter is not certified. Certifying statements does not certify every
printed argument in the article.

The statement audits used a supplied revised manuscript, identified by SHA-256
in [source provenance](publication/source-provenance.json). That revision and
the coauthor review drafts remain outside this publication copy. The arXiv
link is a public bibliographic reference; no byte identity or fresh audit of
that particular arXiv edition is asserted. The report preserves the exact
corrections, conventions and historical source line references.

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run from this directory:

```sh
python3 scripts/check-package.py
lake exe cache get
lake build
lake env lean verification/paper-31-results/AxiomAudit.lean
```

Lean is pinned to **4.35.0**, and Mathlib and its dependencies are pinned in
`lake-manifest.json`. The default build includes the complete library, Solution
and Challenge as separate modules. Do not import Challenge and Solution into
the same environment: they intentionally declare the same names.

CI performs a fresh build and the implementation axiom audit. The manual
private Comparator workflow independently compiles the Challenge, compares
the selected statements and their definitions, checks permitted axioms, and
replays the Solution with Lean and NanoDa. Positive and negative controls
must pass. Reports identify the exact source commit.

[Baseline evidence](verification/source-baseline/README.md) records the passing
build and Lean/NanoDa Comparator run for the unchanged mathematical sources
before this clean copy was made. It is not a verification report for this
repository's later commits. See [Palomar preparation](publication/PALOMAR.md)
for the separate official full-preflight workflow and release procedure.

## Licence and provenance

The formalization uses [Apache-2.0](LICENSE); see [NOTICE](NOTICE).
This is a substantive source copy, containing all proofs and dependencies'
pins, rather than an importing wrapper. Its Git history starts here and
contains no earlier manuscript drafts or development history.
