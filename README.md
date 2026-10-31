# The height of the infection tree: Lean formalization

This repository formalizes **all 31 numbered results** of *The height of the
infection tree* under the embedded SIR epidemic model, with the corrections and
endpoint conventions explicitly listed below. The mathematical source is the paper
by Emmanuel Kammerer, Igor Kortchemski and Delphin Sénizergues
([public paper reference](https://arxiv.org/abs/2504.03526v1)).

`height-infection-tree` is the active project and contains the complete Lean
library. Its proposed Palomar entry selects the two main theorems and the
parameter-uniform strengthening, as described below. Publication preparation
is private; public release, Palomar submission and registration remain pending.

## Coverage and explicit corrections

The completed statement audit records **25 source matches and six corrected
statements or endpoint conventions**: 2 theorems, 8 propositions, 20 lemmas,
and 1 corollary in total. The existing [31-result inventory](FORMALIZATION_REPORT.md#numbered-result-inventory)
maps every result to its Lean certificate. The [detailed correction record](FORMALIZATION_REPORT.md#explicit-corrections-and-conventions-in-the-six-relevant-entries)
gives the corrected scope and certificate for each of these six entries:

| Paper result | Correction or convention used by the formalization |
| --- | --- |
| `lem:couplage` | The coupling event includes the terminal recovery. The replacement is proved separately; the printed event is false. |
| `lem:dangling` | Components are fresh outgrowths obtained by deleting edges already present at the cutoff. |
| `lem:eventE` | Restrict the tolerance to $0<\eta<\min(m_\lambda,1-m_\lambda)$. |
| `lem:sum 1/Sni is gamma log k` | The literal logarithmic formula uses positive times; at time zero the centered empty sum is defined as zero. |
| `proposition majoration increments Mn` | Require $k<\lfloor nt\rfloor$, since the increment uses the next time. |
| `lemme z n proche de z` | Require $A_n\le\lfloor nt\rfloor$ for the preterminal comparison. |

The report separately identifies alternative proof routes and proof corrections.
Certification of these statements does not assert that every printed argument
of the article was checked. The source revision and model limitations are
specified below.

## Selected Palomar results

The current [Comparator configuration](comparator.json) selects these three
declarations for one proposed Palomar entry. Its comparison covers this selection;
the full 31-result library is compiled and audited separately.

| Paper result | Lean certificate | Meaning |
| --- | --- | --- |
| `thm:main` | [`HeightPaper.mainTheorem`](HeightPaper/MainTheorem.lean) | Logarithmic terminal-height limit for arbitrary asymptotic infection-rate sequences, including both early extinction and macroscopic survival. |
| `thm:profil` | [`HeightPaper.strongProfileTheorem`](HeightPaper/StrongProfileTheorem.lean) | Strong asymptotics for active vertices at exact lattice heights, including the Gaussian logarithmic correction and the survival event. |
| Following uniformity paragraph | [`HeightPaper.uniformStrongProfileTheorem`](HeightPaper/UniformStrongProfileTheorem.lean) | The profile estimates with thresholds common over compact epidemic-parameter and tilt sets. |

Start with [Challenge.lean](Challenge.lean): 293 lines of concrete definitions
and these three statements. [Solution.lean](Solution.lean) exposes their proofs.
The three theorem holes in the Challenge are deliberate statement artifacts;
there are no definition holes or implementation proof holes.

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

The unchanged mathematical sources passed a [fresh Linux build and axiom audit](https://github.com/igor-kortchemski/height-infection-tree/actions/runs/41202102007)
and [Comparator with Lean and NanoDa](https://github.com/igor-kortchemski/height-infection-tree/actions/runs/41202125566)
at `palomar-candidate-v1`, commit `a75323a1a0fb78ee01c47f9fa5b38fa52a509de3`.
These runs preceded the repository rename and documentation update. The source
identity manifest confirms that every Lean file and the build, dependency and
Comparator configuration still match that verified mathematical baseline.

[Baseline evidence](verification/source-baseline/README.md) records the passing
build and Lean/NanoDa Comparator run for the unchanged mathematical sources
before this clean copy was made. It is not a verification report for this
repository's later commits. See [Palomar preparation](publication/PALOMAR.md)
for the separate official full-preflight workflow and release procedure.

## Licence and provenance

The formalization uses [Apache-2.0](LICENSE); see [NOTICE](NOTICE).
This is a substantive source copy, containing all proofs and dependencies'
pins. Its Git history contains no manuscript drafts or earlier development
history. The original development project is preserved as a separate private,
read-only archive; further work belongs in this repository.
