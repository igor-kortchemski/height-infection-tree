# Palomar publication candidate

The active project is `igor-kortchemski/height-infection-tree`. It is the clean
publication repository originally prepared as `height-infection-tree-palomar`;
the rename preserves its commit history, tags and verification runs. The former
development repository is retained privately as `height-infection-tree-archive`
and is archived read-only. Its manuscript history is not in this active project.

The maintainer authorized public release and official full mechanical preflight
on 31 October 2026. The clean repository is public; the development archive
remains private and read-only. The public source tree includes the complete
Lean library, selected statement interface,
metadata, verification scripts and evidence. It excludes manuscript files,
figures, coauthor review drafts, local skills and development roadmaps. Its
new Git history does not contain those excluded materials.

## Selected record

The root `comparator.json` selects exactly one proposed Palomar entry:

- `HeightPaper.mainTheorem` for `thm:main`;
- `HeightPaper.strongProfileTheorem` for `thm:profil`;
- `HeightPaper.uniformStrongProfileTheorem` for the following uniformity paragraph.

The underlying model, full quantifiers and all mathematical definitions are
unchanged. `publication/source-files.sha256` records the byte identity of every
Lean source and the build/dependency/Comparator files with the verified source
baseline. The existing 31-result inventory and proof-route disclosures remain
in `FORMALIZATION_REPORT.md`.

Repository coverage is all 31 numbered results: 25 source matches and six
explicit corrections or endpoint conventions. This complete-library claim is
distinct from the three selected declarations in the proposed Palomar entry.
The README makes both scopes and the six corrections visible at the start.

Metadata distinguishes the supplied revised manuscript from the public arXiv
bibliographic reference. Historical line numbers refer to that supplied
revision. Neither its contents nor the private blue review copy are included.
No independent human review or blanket verification of the paper's proofs is
claimed. The continuous-time construction and numerical critical value retain
the limitations stated in the README and metadata.

## Build and private-preparation evidence

The automatic build workflow uses a fresh checkout, the pinned Mathlib
dependency cache, a complete source build and an implementation axiom audit.
During private preparation, the manually dispatched Comparator workflow ran positive/negative
controls, an independent dependency-only Challenge compilation, statement and
definition comparison, and Lean/NanoDa replay. Its private-repository guard
prevents use after public release. Those standalone checks are retained as
preparation evidence. Current official full-preflight outcomes belong to the
separate reusable workflow's exact-commit mechanical report.

The retained baseline reports describe their original source commit. A
publication candidate's current outcome must be read from its own run, not
inferred solely from baseline evidence. Preparation edits do not change the
Lean source or dependency pins.

## Official full preflight after public release

`.github/workflows/palomar-preflight.yml` is a manual caller of the official
reusable workflow. It requires a public repository and an explicit full
40-character source commit. Its `uses` revision and `pipeline_commit` are both
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
It selects `mode: full` and `execution_profile: palomar-standard-v1`, generates
a 12-character request identifier and passes the chosen relationship using
JSON serialization. No token or secret is forwarded to the reusable workflow.

Recheck the current policy and pipeline revisions before running the workflow.
In Actions, select **Palomar
full preflight**, enter the candidate's full commit, and enter the truthful
supported relationship. For the responsible maintainer the documented value is
`I am a responsible author or maintainer`. The workflow fails its guard while
the repository is private. It has no push or pull-request trigger.

Read the resulting `mechanical-report.json`: confirm a passing result, the
exact source and pipeline identities, paths and declarations, canonical
dependency/source checks, mandatory Lean/NanoDa results and the recorded
con-ron replay outcome. Resource failures and missing phases are not passes.
The full workflow is predictive mechanical preflight; it does not run the
service's editorial review or register a result.

## Later submission decisions

The candidate repository is
`igor-kortchemski/height-infection-tree`. The project, metadata and
Comparator paths are the root, `formalization.yaml`, and `comparator.json`.
Use a full immutable commit, not a branch or tag, for an eventual submission.

Service intake and registration remain pending. Intake follows
the live service protocol. Registration requires the maintainer's decision
after seeing the returned review; a preflight pass does not make that decision.

Preparation checked these immutable revisions on 31 October 2026:

- [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md): `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`;
- [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/README.md): `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`;
- [metadata schema v0.4](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json): `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.

The [service protocol](https://submit.palomar-registry.org/llms.txt) is checked
again before any intake request.
