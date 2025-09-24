# Lean Kit

This repository hosts a Lean 4 native Spec-Driven Development toolkit.

## Bootstrap

1. Install the Lean toolchain via [elan](https://github.com/leanprover/elan).
2. From the repo root, run `lake build` to compile the library stubs.

## Project Layout

- `lean-spec/` — Lean sources for the DSL, CLI, specs, and adapters.
- `docs/` — Human-facing documentation (to be populated in later iterations).
- `memories/` — Ultra-compact tool notes (`memories/LEAN`, `memories/LAKE`, …).
- `PLAN.md` — Living plan with milestone-scoped tasks and status.
- `AGENTS.md` — Responsibilities and hand-offs for each project agent.

Refer to `INSTRUCTIONS.md` for the long-form product blueprint.

## CLI

- `lake exe cli -- help` (or `lake run cli -- help`) lists available commands. The `spec`, `plan`, and `implement` subcommands remain stubs.
- `lake exe cli -- init:spec --cap <name>` invokes the generator directly (may require unsandboxed execution on macOS).
- `lake run initSpec --cap <name>` uses the Lake script wrapper to generate Lean spec and plan stubs without launching an external binary.
