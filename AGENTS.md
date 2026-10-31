# Publication candidate

This is a clean publication copy of the infection-tree formalization. The
development archive, manuscript drafts and planning history are kept separately.
Do not add them to this repository as part of routine publication work.

- Preserve all Lean source files and the three selected declarations in
  `comparator.json`. Do not change their mathematical meaning or assumptions.
- Preserve `HeightPaper.MainTheoremStatement`, `HeightPaper.mainTheorem`,
  `HeightPaper.main_limit`, and `HeightPaper.main_limit_of_asymptotic`.
- Keep Lean 4.35.0 and every dependency revision unchanged.
- No implementation proof holes, custom axioms or native-evaluation axioms.
  Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
  Exactly three deliberate statement holes belong to `Challenge.lean`.
- Keep the complete 31-result coverage record in `FORMALIZATION_REPORT.md`.
  Distinguish historical evidence, current verification and paper-proof fidelity.
- Run `python3 scripts/check-package.py`, appropriate build checks and the axiom
  audit before claiming verification. Inspect exact-commit Comparator reports.
- Publication preparation does not authorize public release, Palomar intake or
  registration. The repository remains private until the maintainer decides.
- In Markdown, use `$...$` inline. Put each `$$` display delimiter on its own
  line, with blank lines surrounding the display. Use MathJax-compatible LaTeX.
