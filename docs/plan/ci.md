# CI Workflow Skeleton

The `Lean SDD Gates` workflow (`.github/workflows/lean-sdd.yml`) establishes three jobs that will evolve into the SPEC → PLAN → IMPLEMENT gates.

## Jobs
- **spec** — Installs the Lean toolchain via `elan`, restores the Lake cache, and runs `lake build`.
- **plan** — Depends on `spec`, repeats the environment setup, and executes the placeholder `lake exe cli -- plan` command.
- **implement** — Depends on `plan`, reruns setup, and executes `lake exe cli -- implement`.

## Environment setup
- The workflow pins the toolchain with `LEAN_TOOLCHAIN=leanprover/lean4:v4.9.0`.
- `elan` is installed using the upstream shell installer; we export `~/.elan/bin` through `$GITHUB_PATH`.
- Lake build artefacts (`.lake`, `lake-manifest.json`) and the toolchain directory are cached under a key derived from the Lean sources.

## Local mirroring
- `lake build` mirrors the SPEC job.
- `lake exe cli -- plan` / `lake exe cli -- implement` are placeholders until plan & implement automation mature.
- `act -j spec` is the intended local runner, but **not executed yet**; run manually once `act` is configured.

## Next steps
- Replace placeholder PLAN/IMPLEMENT commands with real traceability and oracle checks.
- Split common setup into a reusable composite action or script to avoid duplication.
- Add artefact uploads (DOT/Mermaid graphs) once exporters land.
