# Verification of `paper-31-results`

These records were produced on 31 October 2026 by an independent local clone at
commit `da98007a3268a469ffa8ff48ceec43034f842930` (tag `paper-31-results`). They are
archived evidence from that verification, not output from a GitHub Actions run.

- `build.log` and `build-result.json`: successful source rebuild of all 470
  library modules, without copying project build artifacts.
- `axioms.log`, `axiom-result.json`, and `AxiomAudit.lean`: audit of all 7,067
  accessible project declarations and 41 named certificate queries. Only
  `propext`, `Classical.choice`, and `Quot.sound` occur in their axiom closures.
- `preflight.json`, `independence-result.json`, and `toolchain.txt`: exact source
  commit, dependency revisions, toolchain, and independence checks.
- `source-scan.txt`: source scan result for proof holes and forbidden tactics.
- `verification-summary.txt`: the verification's scope and outcome.

The two machine-specific checkout paths in `verification-summary.txt` were
replaced by descriptive placeholders for this archive. The exact original audit
probe is retained as `AxiomAudit.original.txt`; the runnable `AxiomAudit.lean`
adds a module header and an `import all` library import for current package
compliance while retaining access to private auxiliary declarations.
Other evidence files are copied without changes. Pinned dependency sources and compiled dependency
caches were reused; Mathlib itself was not rebuilt from scratch. This is not a
Palomar verification report.

To repeat the library build and axiom audit from the repository root:

```sh
lake exe cache get
lake --no-cache --rehash build
lake env lean verification/paper-31-results/AxiomAudit.lean
```

For an independent check, use a fresh clone. The audit probe lives outside the
library and is run explicitly; `lake build` builds the `HeightPaper` entry point.
