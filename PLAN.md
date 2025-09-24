# PLAN

**Process**: After checking off any task, immediately create a dedicated git commit for that task before continuing; capture fresh tool knowledge under `memories/<TOOL>` before moving on.

## Iteration 0 — Bootstrapping (M0)
- [x] Task 0.1: Pin Lean toolchain and scaffold Lake package skeleton
  - Implementation: add `lean-toolchain`, `lakefile.lean`, base `lakefile.toml`/`leanpkg.toml`, and create empty module placeholders under `lean-spec/`.
  - Tests: `lake build`
  - Proofs: n/a (no obligations defined yet)
  - Docs: seed `README.md` with bootstrap instructions
- [x] Task 0.2: Create CLI entry point with `lake run help`
  - Implementation: add `Cli/Main.lean` with command routing and stub subcommands aligned with SPEC/PLAN/IMPLEMENT phases.
  - Tests: `lake exe cli -- help`
  - Proofs: n/a (CLI logic only)
  - Docs: document CLI usage in `README.md`
  - Notes: `lake exe cli -- help` fails locally due to dyld SG_READ_ONLY restriction; needs toolchain investigation.
- [x] Task 0.3: Provide sample capability doc and spec generator
  - Implementation: add `docs/capabilities/mutex.md`, implement `Cli/Gen.lean` to generate `Spec/Mutex.lean` via `lake run initSpec`.
  - Tests: `lake run initSpec --cap mutex` followed by `lake build`
  - Proofs: n/a (generated spec contains stubs only)
  - Docs: update `docs/plan/mutex.md` with generated obligations list
  - Notes: `lake run initSpec` uses Lake script naming (colon not supported); CLI still exposes `init:spec` for consistency.
- [ ] Task 0.4: Configure CI workflow skeleton
  - Implementation: add `.github/workflows/lean-sdd.yml` with SPEC/PLAN/IMPLEMENT jobs wiring commands.
  - Tests: `act -j spec` (or CI dry run if local `act` unavailable)
  - Proofs: n/a (automation pipeline)
  - Docs: record CI behaviour in `docs/plan/ci.md`

- [x] Task 0.5: Establish Lean memory log
  - Implementation: create `memories/LEAN` and seed it with current Lean insights.
  - Tests: `ls memories/LEAN`
  - Proofs: n/a (reference notes only)
  - Docs: document the memory workflow in `README.md` and `PLAN.md`

## Backlog — Milestone 1 (Kernel + Explorer MVP)
- [ ] Task 1.1: Implement `Dsl/Core.lean` primitives for stores, traces, and runs
  - Implementation: encode store type, Init/Next signatures, run semantics, temporal operators skeleton.
  - Tests: `lake build`, unit tests in `Dsl/CoreTest.lean`
  - Proofs: prove well-typedness lemmas for Init/Next composition
  - Docs: explain core semantics in `docs/capabilities/semantics.md`
- [ ] Task 1.2: Implement action constructors and composition rules
  - Implementation: populate `Dsl/Actions.lean` and `Dsl/Composition.lean` with constructors and helper lemmas.
  - Tests: unit tests covering action evaluation and composition identities.
  - Proofs: prove associativity/identity lemmas in Lean.
  - Docs: update action catalogue reference in `docs/capabilities/actions.md`
- [ ] Task 1.3: Build invariant automation helpers
  - Implementation: implement `Dsl/Invariants.lean` with `inv_auto` tactic and invariant combinators.
  - Tests: tactic-level regression tests via `.extra` tests.
  - Proofs: prove soundness lemmas for invariant helpers.
  - Docs: write how-to in `docs/capabilities/invariants.md`
- [ ] Task 1.4: Implement explorer BFS with symmetry reduction
  - Implementation: fill `Explorer/Scope.lean`, `Explorer/Search.lean`, and `Explorer/Hashing.lean` skeletons.
  - Tests: unit tests for BFS expansions and hashing determinism.
  - Proofs: prove soundness of symmetry reduction assumptions.
  - Docs: document explorer usage in `docs/models/README.md`
- [ ] Task 1.5: Complete Mutex safety example
  - Implementation: finish `Spec/Examples/Mutex.lean` with invariant proofs and bounded explorer integration.
  - Tests: `lake run spec --cap mutex`
  - Proofs: safety invariant theorem for Mutex spec
  - Docs: update `docs/capabilities/mutex.md` with proof outline and CE trace example

## Backlog — Milestone 2 (Temporal + WF/SF)
- [ ] Task 2.1: Implement temporal operators and WF/SF kernels
  - Implementation: complete `Dsl/Temporal.lean` and `Dsl/Liveness.lean` with core lemmas.
  - Tests: unit tests for temporal algebra properties.
  - Proofs: prove `leads_to` transitivity and WF/SF introduction lemmas.
  - Docs: extend temporal semantics doc in `docs/capabilities/temporal.md`
- [ ] Task 2.2: Add liveness proof for Queue example
  - Implementation: fill `Spec/Examples/Queue.lean` with liveness obligations.
  - Tests: `lake run spec --cap queue`
  - Proofs: leads-to theorem for queue progress.
  - Docs: document scenario and proof in `docs/capabilities/queue.md`
- [ ] Task 2.3: Integrate explorer lasso detection for liveness CEs
  - Implementation: augment `Explorer/Search.lean` with lasso detection.
  - Tests: regression test generating known lasso trace.
  - Proofs: justify lasso detection correctness (Lean lemma).
  - Docs: update explorer docs with lasso workflow.

## Backlog — Milestones 3-6
- [ ] Task 3.x: Adapters for DOT, Mermaid, TLA, Alloy exports (break down when scheduled)
  - Implementation: fill `Spec/Adapters/Export/*.lean` modules.
  - Tests: golden-file comparisons for exporters.
  - Proofs: structural consistency lemmas between Lean model and exports.
  - Docs: add exporter usage notes in `docs/out/README.md`
- [ ] Task 4.x: Traceability gate linking docs to Lean obligations
  - Implementation: complete `Cli/Traceability.lean` and docs parser.
  - Tests: `lake run traceability`
  - Proofs: correctness lemma for ReqID ↔ theorem mapping.
  - Docs: detail traceability workflow in `docs/plan/traceability.md`
- [ ] Task 5.x: Runtime oracle generation and NDJSON checker
  - Implementation: implement `Spec/Adapters/Runtime/Oracle.lean` and CLI tool.
  - Tests: property tests using sample logs.
  - Proofs: prove oracle compliance with invariant definitions.
  - Docs: write runtime monitoring guide in `docs/capabilities/oracles.md`
- [ ] Task 6.x: Example suite completion and documentation pass
  - Implementation: finalize five worked examples with proofs and exports.
  - Tests: run all SPEC/PLAN/IMPLEMENT gates in sequence.
  - Proofs: ensure each example has completed safety + liveness proofs.
  - Docs: finalize README and prompt cookbook in `docs/prompts/`
