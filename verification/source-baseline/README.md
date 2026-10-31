# Verified mathematical-source baseline

These unmodified reports and logs come from the private development archive at
commit `7f56d1daf0ba8d2d621b6da715f1fdb7c44e4961` on 31 October 2026:

- `build-report.json`, `build.log` and `axioms.log`: fresh Linux source build
  and axiom audit, run `41197150015`;
- `private-comparator-report.json` and the mandatory comparison logs: passing
  statement/definition comparison and Lean/NanoDa replay, run `41197345160`;
- `control-*.log`: matching positive control and wrong-statement,
  forbidden-axiom and ill-typed-proof negative controls. The ill-typed proof
  was rejected by both Lean and NanoDa.

The audit checked 5,190 accessible project declarations from 469
declaration-bearing modules; 401 were axiom-free, and the remaining closures
used only `propext`, `Classical.choice` and `Quot.sound`. It also checked the
41 named certificates. Counts differ from the older `paper-31-results`
archive because compiler visibility and auxiliary declarations differ; the
reports retain their own source revisions and counting context.

All 473 Lean source files, the toolchain, Lake configuration, manifest and
Comparator configuration are byte-identical in this publication copy, as
recorded by `publication/source-files.sha256`. These baseline runs establish
the status of that source archive. They do not claim a fresh run for any
later commit or the official full Palomar pipeline. The original workflow
URLs in the reports refer to private runs and may be inaccessible to readers;
the reports and logs themselves are retained here for inspection.

Those raw reports retain the historical repository name `height-infection-tree`.
That source repository (GitHub id `1440719370`) is now the private, read-only
`height-infection-tree-archive`. The active clean repository is now named
`height-infection-tree` (GitHub id `1440844580`), formerly
`height-infection-tree-palomar`. The historical baseline workflow URLs must
therefore be read with the archive repository name; the original JSON is
preserved without rewriting its recorded identity.

Current publication-candidate verification belongs to its own exact-commit
CI and Comparator artifacts. Public release, full Palomar preflight, intake
and registration are separate later steps.
