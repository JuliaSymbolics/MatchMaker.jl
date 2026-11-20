# Agent notes

See `DEVELOPING.md` for the file map and cross-file invariants;
`DESIGN.md`/`REWRITING.md` for the *why*.

## Style

- Docstrings are concise and describe user-facing behavior only.
  Implementation details belong in an `# Extended help` section, and
  only when necessary.
- Use DocStringExtensions in docstrings (`$TYPEDSIGNATURES`, etc.).

## Tests

- Changes must be accompanied by tests. Per-source-file unit suites
  live in `test/unit/`; `test/qa/` holds Aqua + JET.
- JET coverage should be comprehensive: add signatures for new
  functions to the curated list in `test/qa/jet.jl`.
- QA must pass before committing — `Pkg.instantiate` `test/qa` once,
  then run `julia --project=test/qa test/qa/qa.jl`.

## Docs

- Surface new functions/API changes in the docs: the matching
  `docs/src/api/*.md` `@docs` block, plus prose pages when relevant.

## Commits

- Always format with Runic before committing:
  `julia -e 'using Runic; exit(Runic.main(ARGS))' -- --inplace <paths>`
  (checked by the FormatCheck workflow).
- AI-generated commits need attribution trailers naming the harness,
  model, and session, plus a `Co-Authored-By` line for the agent —
  e.g. `Generated with [Devin](https://devin.ai)` and
  `Co-Authored-By: Devin <158243242+devin-ai-integration[bot]@users.noreply.github.com>`.
