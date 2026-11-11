# The height of the infection tree

[![CI: build and axiom audit](https://github.com/igor-kortchemski/height-infection-tree/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/height-infection-tree/actions/workflows/build.yml?query=branch%3Amain)
[![Comparator: Palomar full preflight](https://github.com/igor-kortchemski/height-infection-tree/actions/workflows/palomar-preflight.yml/badge.svg)](https://github.com/igor-kortchemski/height-infection-tree/actions/workflows/palomar-preflight.yml)

Lean 4 and Mathlib formalization of *The height of the infection tree* by
Emmanuel Kammerer, Igor Kortchemski and Delphin Sénizergues
([arXiv:2504.03526v1](https://arxiv.org/abs/2504.03526v1)).

**All 31 numbered results of the paper (2 theorems, 8 propositions, 20 lemmas,
1 corollary) are proved under the embedded SIR event-chain model: 25 as stated
and six with an explicit correction or endpoint convention. The proofs use only the
axioms `propext`, `Classical.choice` and `Quot.sound`, and there is no `sorry`
outside the three deliberate statement holes of `Challenge.lean`.**

Statements: [Challenge.lean](Challenge.lean) · Correspondence record: [FORMALIZATION_REPORT.md](FORMALIZATION_REPORT.md) · [Verification](#verify)

## Main results

One individual is infectious and $n$ are susceptible. Each event is an infection
with probability $\lambda_n S/(1+\lambda_n S)$, where $S$ is the number of
susceptibles, and otherwise a recovery; the infector or the recovering
individual is uniform among the infectious ones. The infection tree records who
infected whom. Comparator checks the three results below; [Challenge.lean](Challenge.lean)
gives every definition.

| Paper result | Lean declaration | Statement |
| --- | --- | --- |
| `thm:main` | [`HeightPaper.mainTheorem`](HeightPaper/MainTheorem.lean) | If $n\lambda_n\to\lambda>1$, the terminal height divided by $\log n$ converges in law to $0$ with probability $1/\lambda$ and to an explicit constant $C_\lambda$ (`mainCoefficient`) with probability $1-1/\lambda$. |
| `thm:profil` | [`HeightPaper.strongProfileTheorem`](HeightPaper/StrongProfileTheorem.lean) | For $\lambda_n=\lambda/n$, $0<T<t_\lambda$ and compact $K\subset(0,z_\lambda)$, on the event that the epidemic has not died out before $\lfloor Tn\rfloor$ events: at each integer height $k=\gamma_\lambda e^{x}\log n$ with $x\in K$, the proportion $p_k$ of infectious individuals at height $k$ is positive and $\log p_k=(f_\lambda(x)-1)\log n-\frac{1}{2}\log\log n+O_{\mathbb P}(1)$, uniformly in $x$. |
| Paragraph after `thm:profil` | [`HeightPaper.uniformStrongProfileTheorem`](HeightPaper/UniformStrongProfileTheorem.lean) | The same estimate, with thresholds chosen uniformly over $\lambda$ in a compact parameter set. |

Here $\gamma_\lambda=\lambda/(\lambda-1)$, $f_\lambda(x)=1+\gamma_\lambda(e^x-1-xe^x)$,
$z_\lambda$ is the positive root of $f_\lambda$ and $t_\lambda$ is the extinction
time of the fluid limit. The library also proves the other 29 numbered results; the
[inventory](FORMALIZATION_REPORT.md#numbered-result-inventory) maps each one to
its Lean certificate. Six statements differ from the printed ones
([details](FORMALIZATION_REPORT.md#explicit-corrections-and-conventions-in-the-six-relevant-entries)):

| Paper result | Correction or convention |
| --- | --- |
| `lem:couplage` | The coupling event includes the terminal recovery; the printed event is false. The corrected statement is `HeightPaper.correctedCouplingTheorem`. |
| `lem:dangling` | Components are fresh outgrowths, obtained by deleting edges already present at the cutoff. |
| `lem:eventE` | The tolerance is restricted to $0<\eta<\min(m_\lambda,1-m_\lambda)$. |
| `lem:sum 1/Sni is gamma log k` | The logarithmic formula is for positive times; at time zero the centered empty sum is defined as zero. |
| `proposition majoration increments Mn` | Requires $k<\lfloor nt\rfloor$, since the increment uses the next time. |
| `lemme z n proche de z` | Requires $A_n\le\lfloor nt\rfloor$ for the preterminal comparison. |

Scope: the continuous-time Poisson/exponential construction and its equality in
law with the event chain are not separately formalized; the numerical value
$\lambda_c\simeq1.8038$ of the critical parameter is not certified; the Lambert
function is replaced by root and infimum characterizations. Not every printed
argument of the paper was checked: the report lists the
[alternative proof routes](FORMALIZATION_REPORT.md#proof-correspondence-and-substantive-departures)
and the [issues found in the source](FORMALIZATION_REPORT.md#source-issues-relevant-to-coverage).
Statements were audited against a revised manuscript (SHA-256 in [source-provenance.json](publication/source-provenance.json)),
which is not distributed here; the report's line numbers refer to it.

## Where to start

- [Challenge.lean](Challenge.lean): the model and the three statements in 293
  lines, importing only Lean core and Mathlib; [Solution.lean](Solution.lean)
  re-exports their proofs under the same names.
- Proofs: [MainTheorem.lean](HeightPaper/MainTheorem.lean) (also
  `main_limit_of_asymptotic`, for $\lambda_n\sim\lambda/n$),
  [StrongProfileTheorem.lean](HeightPaper/StrongProfileTheorem.lean),
  [UniformStrongProfileTheorem.lean](HeightPaper/UniformStrongProfileTheorem.lean),
  [CorrectedCouplingTheorem.lean](HeightPaper/CorrectedCouplingTheorem.lean).
- [HeightPaper.lean](HeightPaper.lean) imports the whole library.
- Do not import `Challenge` and `Solution` together: they declare the same names.

## Verify

Install Lean ([setup guide](https://leanprover-community.github.io/install/project.html)), then run:

```sh
git clone https://github.com/igor-kortchemski/height-infection-tree.git
cd height-infection-tree
lake exe cache get
lake build
lake env lean verification/paper-31-results/AxiomAudit.lean
```

Lean 4.35.0 (`lean-toolchain`) and Mathlib with its dependencies
(`lake-manifest.json`) are pinned; do not run `lake update`. `lake build`
compiles the library, `Solution` and `Challenge`, whose three `sorry` warnings
are expected; the last command audits the axioms of every project declaration.
`python3 scripts/check-package.py` checks the statement interface, forbidden
tokens, pins and source hashes. To browse the proofs, open the folder in VS Code
with the Lean 4 extension.

[CI](.github/workflows/build.yml) repeats the build and axiom audit from a fresh
checkout on every push and pull request to `main`. The manual
[Palomar full preflight](.github/workflows/palomar-preflight.yml) runs the
official Palomar pipeline on a given commit: Comparator checks that `Solution`
proves the `Challenge` statements, and the Lean and NanoDa kernels replay the
proofs; its badge shows the latest run. It passed on 31 October 2026 for commit
`f1a5b7dfdcc9b3d6f7665d9e99535760c181c47f` (tag `palomar-full-preflight-v1`,
[run 41210059610](https://github.com/igor-kortchemski/height-infection-tree/actions/runs/41210059610)),
whose Lean files and build configuration are identical to the current ones
(`check-package.py` checks them against [source-files.sha256](publication/source-files.sha256)).
Earlier evidence: [source baseline](verification/source-baseline/README.md) and
[31-result audit](verification/paper-31-results/README.md). The result is not
registered in Palomar; intake and registration have not been requested.

## How it was made

The proofs were developed by AI agents (GPT-6 family models, through Codex and
ChatGPT) under the maintainer's mathematical direction, with compiler-guided
iteration and automated axiom checks. AI-assisted audits checked the statement
correspondence; no independent human review is claimed.

## License and citation

The formalization is released under [Apache-2.0](LICENSE) (see [NOTICE](NOTICE));
the license does not cover the paper, and dependencies keep their own licenses.
Maintainer: Igor Kortchemski; please report problems through GitHub issues.
Cite the paper for the mathematics: E. Kammerer, I. Kortchemski and
D. Sénizergues, *The height of the infection tree*, arXiv:2504.03526. Cite this
repository, with the full commit hash you used, for the formalization.
