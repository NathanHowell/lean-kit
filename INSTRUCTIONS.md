Awesome. Here’s a fully stand-alone, agent-consumable build plan for a Lean-4–native Spec-Driven Development (SDD) system that borrows the best DX ideas from Spec-Kit while delivering stronger formalism (Lean 4 + TLA-style semantics). It includes repo layout, milestones, CI gates, adapters (DOT, Mermaid), model explorer, proof obligations, and copy-pasteable agent prompts.

⸻

Product Vision

Goal: Make the Lean model the single source of truth for large software projects. Human-readable specs drive code generation and tests, while Lean proofs + bounded model exploration gate progress. The workflow mirrors Spec-Kit’s SPEC → PLAN → IMPLEMENT phases, but everything is Lean-native and formal.

Non-Goals: Replace enterprise modeling tools; do UX/UI design; build an IDE. We optimize for correctness, traceability, and team flow.

⸻

Architecture & Repo Layout

/lean-spec/                      # Lake package (Lean 4)
  Dsl/
    Core.lean                    # Init/Next, traces, runs, labels
    Temporal.lean                # □, ◇, leads-to, fairness kernels
    Actions.lean                 # Assign, If, Disj, Unchanged, Enabled
    Composition.lean             # Parallel composition, hiding, renaming
    Refinement.lean              # Abstraction maps, ⊑ obligations
    Invariants.lean              # Safety: invariant def + proof helpers
    Liveness.lean                # WF/SF rules, leads-to lemmas
    Pluscal.lean                 # (Optional) PlusCal-like macro/surface layer
    Explorer/
      Scope.lean                 # Domains, bounds, symmetry
      Search.lean                # BFS/DFS, CE traces, lasso detection
      Hashing.lean               # State hashing (with symmetry)
      ModelIO.lean               # Read/write TOML/JSON for models
  Spec/
    Examples/
      Mutex.lean                 # Minimal worked example (safety + liveness)
      Queue.lean                 # Bounded queue example
    Adapters/
      Export/DOT.lean            # Graphviz DOT state graphs
      Export/Mermaid.lean        # Mermaid flowchart/sequence/state diagrams
      Export/TLA.lean            # Minimal .tla exporter (subset)
      Export/Alloy.lean          # Minimal Alloy/relations exporter (subset)
      Runtime/Oracle.lean        # Turn invariants into runtime checkers
  Cli/
    Main.lean                    # lake run spec/plan/implement/etc.
    Parsers.lean                 # Markdown front-matter + fenced blocks
    Gen.lean                     # Generate Lean stubs from docs
    Traceability.lean            # ReqID ↔ theorem mapping
/docs/                           # Human-readable spec & plan
  capabilities/                  # One file per capability (front-matter + blocks)
  plan/                          # Capability→Feature→Obligations decomposition
  api/                           # (Optional) OpenAPI schemas for services
  models/                        # *.toml finite domains, symmetry, bounds
  prompts/                       # Agent prompt templates (SPEC/PLAN/IMPL)
.github/workflows/
  lean-sdd.yml                   # CI phase gates
lakefile.lean                    # Lake targets/aliases


⸻

Phase Gates (lean-native)

SPEC gate (authoritative model):
	•	Build Lean.
	•	For each declared invariant/liveness obligation:
	•	Prove it or run bounded exploration with /docs/models/*.toml.
	•	Any counterexample (CE) fails the gate.
	•	Export state graphs for changed specs (DOT + Mermaid).

PLAN gate (traceability + obligations):
	•	Every capability/feature in /docs/plan/*.md must have corresponding Lean obligations (theorems or refinement goals).
	•	If /docs/api/*.yaml exists, generate data constraints (e.g., uniqueness, acyclicity) and prove or falsify them.

IMPLEMENT gate (tests + oracles):
	•	Run generated example-based tests (from scenarios).
	•	Run runtime oracles (derived from invariants) on integration logs if provided.

⸻

Lean DSL Semantics (TLA-style)
	•	Kernel:
	•	Store (typed record or Var → Val)
	•	Label (action name + args)
	•	Init : Store → Prop
	•	Next : Store → Label → Store → Prop (disjunction of actions)
	•	Runs/Traces: Run := Nat → (Store × Label)
	•	Operators:
	•	ENABLED A ≜ ∃ s' l, A s l s'
	•	UNCHANGED xs (stuttering on tracked vars)
	•	Temporal □, ◇, □◇, ◇□ over runs
	•	WF/SF lists on actions
	•	Safety & Liveness:
	•	Invariant P S with automation (inv_auto): prove Init ⊢ P and P ∧ Next ⊢ P'.
	•	Liveness via WF/SF schemas and leads-to library lemmas (transient/ensure/stable rules).
	•	Refinement:
	•	Refines (map : Store → Store) : Impl ⊑ Spec
	•	Macro refine_by map := produces two obligations (init & step).
	•	Composition:
	•	Parallel composition, label synchronization (e.g., send/recv), hiding, renaming.
	•	PlusCal-like surface (optional):
	•	Macro that turns structured algorithm text blocks into Next and a pc variable per process.

⸻

Explorer (bounded model search)
	•	Scope:

steps = 200
vals  = [0,1,2,3]
symmetry = ["Accounts","Workers"]  # domains to permute
queues = { inbox = 2 }             # optional resource bounds


	•	Algorithms:
	•	BFS/DFS with visited set & symmetry reduction (canonicalization).
	•	Lasso detection to witness simple liveness (cycle + pending goal).
	•	CE traces: JSON + TLA-like tabular text; also export DOT & Mermaid.
	•	CLI:
	•	lake run explore --spec Mutex --model docs/models/mutex.toml
	•	lake run ce:print --last (pretty print)
	•	lake run ce:export --format dot|mermaid|json

⸻

Adapters & Exporters
	•	Graphviz DOT: State nodes (hash labels), edges labeled with Label.name(args).
lake run export:dot --spec Ledger --out docs/out/ledger.dot
	•	Mermaid:
	•	Flowchart for state graphs (small scopes).
	•	Sequence diagrams for scenario traces (actors inferred from labels).
	•	State diagrams for PC-based processes.
	•	TLA subset:
	•	Emit .tla with VARIABLES, Init, Next (subset).
	•	.cfg-like domains from the TOML model for TLC sanity (optional).
	•	Alloy subset:
	•	Emit signatures/relations for structural constraints; run outside if desired.
	•	Runtime Oracle:
	•	Generate a small Lean/C/TS checker from invariants to validate event logs at runtime (CLI compiles a binary or transpiles TS for web).

⸻

Documentation Formats (agent-friendly)

Capabilities (Markdown with front-matter):

---
id: LEDGER-001
title: Posting transactions
version: 1.2.0
invariants:
  - NoNegativeBalance
  - ConservationOfValue
liveness:
  wf: [ApplyTx]    # weak fairness actions
  sf: []           # strong fairness actions
constants:
  Accounts: [A,B,C]
tracked:
  - Accounts
  - Balances
---

Fenced blocks (parsed by CLI):

### Init
```lean
fun s => s.balances = {A:=0,B:=0,C:=0}

Actions

def ApplyTx : Action := fun s l s' =>
  l.name = "apply" ∧
  -- update balances...

Scenarios

- name: basic_transfer
  steps:
    - apply: {from: A, to: B, amount: 1}
    - apply: {from: B, to: C, amount: 1}

**Plan files** map capability → feature → obligations:
```md
- Capability: LEDGER-001 Posting
  - Feature: Idempotent Apply
    - Obligation: Invariant NoDoubleSpend
    - Obligation: Refines PostingImpl ⊑ PostingSpec

Model files (.toml) define finite exploration domains (see Scope above).

⸻

CLI (Lake) Commands
	•	lake run init:spec --cap capabilities/ledger.md
Generate/refresh Lean stubs in Spec/Ledger.lean with invariants, Next, WF/SF lists, theorem shells, and link version IDs.
	•	lake run spec
SPEC gate: build, parse docs, sync stubs, run explorer (as configured), require proofs or CE.
	•	lake run plan
PLAN gate: ensure every plan obligation exists in Lean; generate missing stubs as failing TODOs.
	•	lake run implement
IMPLEMENT gate: run tests & runtime oracles.
	•	lake run explore --spec <Name> --model <path>
Bounded exploration; produce CE traces & graphs.
	•	lake run export:dot|mermaid|tla|alloy --spec <Name>
	•	lake run traceability
Emit CSV/JSON mapping ReqID → theorems / proofs / CE.
	•	lake run ce:print|ce:export --last

⸻

CI Workflow (GitHub Actions)

name: Lean SDD Gates
on: [pull_request]
jobs:
  spec:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
      - run: lake build
      - run: lake run spec
  plan:
    runs-on: ubuntu-latest
    needs: spec
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
      - run: lake run plan
  implement:
    runs-on: ubuntu-latest
    needs: plan
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
      - run: lake run implement

PR Bot niceties:
	•	Comment with missing obligations, failing theorems, CE summaries (top-k shortest traces), and links to DOT/Mermaid renders.
	•	Block merge if SPEC/PLAN/IMPLEMENT checks fail.

⸻

Developer Experience (DX) Features
	•	Scaffolders: lake run init:spec creates Lean stubs from MD front-matter & blocks.
	•	Trace-linked errors: on failure, print exact ReqID, theorem name, and file:line.
	•	Version locks: front-matter version must match an embedded tag in Spec/*.lean.
	•	Deterministic builds: pin Lean toolchain via elan and Lake manifest.
	•	Mermaid previews: write .md fragments with Mermaid code blocks for quick docs.
	•	One-line repro: lake run explore --spec X --model docs/models/X.toml --seed N.
	•	Symmetry helpers: canned canonicalizers for common domains (IDs, accounts, workers).
	•	Examples: Five worked examples (Mutex, Queue, Two-Phase Commit sketch, Leader Election sketch, Ledger Posting) each with:
	•	1 proved invariant,
	•	1 liveness proof using WF/SF,
	•	explorer model & graphs,
	•	scenario-derived tests.

⸻

Agent Prompt Library (copy/paste)

01-Author Spec (SPEC phase)

You are drafting a capability spec used to generate Lean 4 models.

Deliver:
- Markdown in /docs/capabilities/<name>.md with front-matter:
  id, title, version, invariants[], liveness{wf[],sf[]}, constants{}, tracked[]
- Fenced blocks:
  "Init" : Lean predicate Store → Prop
  "Actions" : Lean definitions of actions used by Next
  "Scenarios" : YAML steps usable for scenario tests

Constraints:
- Keep Init and Actions total on declared constants.
- Prefer small, enumerable domains.
- Name actions with stable strings; args are simple values.

Output only the Markdown file content.

02-Generate Lean Stubs

Read /docs/capabilities/<name>.md and create/update:
- Spec/<Name>.lean with:
  variables, Init, Next (disjunction of actions), WF/SF lists
  theorem stubs for each invariant (Invariant P Spec.Name.S)
  theorem stubs for refinement edges if declared in plan
- docs/models/<name>.toml default scope based on constants

Do not invent semantics not present in the MD doc.

03-Prove Safety Invariants

Open Spec/<Name>.lean and complete theorems marked with @[req "...", invariant "..."].
Use inv_auto first; if it fails, decompose Next cases and use simp/aesop/linarith.

If a proof seems false, run a bounded search:
  lake run explore --spec <Name> --model docs/models/<name>.toml
Attach the shortest CE trace and propose a minimal spec fix in MD.

04-Prove Liveness (WF/SF)

Use provided WF/SF lists. Prove a leads-to property using library lemmas.
If difficult, construct a transient set and show eventual progress.
When stuck, produce a small model and try lasso detection via explorer; adjust WF/SF minimally.

05-Add Refinement Mapping

Given Impl and Spec, define map : Impl.Store → Spec.Store.
Invoke `refine_by map :=` to open init & step obligations.
Prove obligations or adjust Impl actions accordingly.

06-Export Graphs

For Spec <Name>, export:
- DOT: lake run export:dot --spec <Name> --out docs/out/<name>.dot
- Mermaid: lake run export:mermaid --spec <Name> --out docs/out/<name>.md
Ensure graphs are small (limit nodes via model bounds).

07-Traceability Check

Run: lake run traceability
If any ReqID in /docs/plan is not mapped to a theorem or model, create a stub and fail the PLAN gate.

08-Runtime Oracle Generation

For each invariant I in Spec <Name>, generate a checker function and a CLI tool that ingests NDJSON events.
Emit violations with (ReqID, timestamp, summary). Include a small README.


⸻

Milestones & Acceptance Criteria

M0 — Bootstrapping (Day 0–2)
	•	Lake project compiles; Cli/Main.lean prints help.
	•	docs/capabilities/mutex.md sample exists.
	•	lake run init:spec --cap ... generates Spec/Mutex.lean.
Accept: Build passes; stubs created.

M1 — Kernel + Explorer MVP (Week 1)
	•	Core, Actions, Invariants, Explorer/Search implemented.
	•	BFS over small scopes; CE JSON + DOT export.
	•	Mutex invariant proved; CE generated for a broken variant.
Accept: lake run spec fails on CE; passes on fixed spec.

M2 — TLA-style Temporal + WF/SF (Week 2)
	•	Temporal, Liveness, WF/SF semantics & lemmas.
	•	Liveness proof for Queue or Mutex (progress).
Accept: One liveness theorem proved; failing case yields lasso CE.

M3 — Adapters + Mermaid + TLA/Alloy Export (Week 3)
	•	DOT + Mermaid exporters; minimal TLA/Alloy subset exporters.
	•	CI uploads artifacts; PR comment links to renders.
Accept: Artifacts visible on PR; links clickable.

M4 — Plan Gate + Traceability (Week 4)
	•	/docs/plan/*.md parsed; obligations materialized as stubs.
	•	lake run plan fails if unmapped; CSV/JSON traceability generated.
Accept: PLAN gate blocks missing obligations.

M5 — Runtime Oracles + API Constraints (Week 5)
	•	Invariant → oracle generator; basic NDJSON checker.
	•	If /docs/api present: data constraints generated and proved/searched.
Accept: IMPLEMENT gate runs oracles/tests; fails on violations.

M6 — Examples Suite + Docs (Week 6)
	•	Five examples complete (safety+liveness+graphs+scenarios).
	•	README + usage docs + prompt cookbook.
Accept: New engineer can run all gates in <15 min.

⸻

Testing Strategy
	•	Unit tests: semantics rules; explorer state transitions; exporter outputs (goldens).
	•	Property tests: composition laws (associativity, identity) for systems.
	•	Golden traces: fixed CE traces for broken specs.
	•	Performance smoke: exploration completes under given bounds in CI time budget.

⸻

Security & Governance
	•	Small trusted core: keep kernel + explorer minimal; review changes carefully.
	•	Versioned specs: front-matter version must match embedded tags in Lean modules.
	•	Reproducibility: pin Lean toolchain; CI caches Lake build.

⸻

“Nothing Missing?” Cross-Check vs. Discussion
	•	Lean-4 DSL kernel with Init/Next, invariants, liveness, refinement ✅
	•	TLA+ ideas: stuttering, ENABLED/UNCHANGED, WF/SF, leads-to, refinement mappings, prophecy/history (extendable) ✅
	•	PlusCal-like surface (optional macro) ✅
	•	Spec-Kit ideas: SPEC/PLAN/IMPLEMENT phases, CI gates, PR comments, agent prompts, traceability, spec-first CE loop ✅
	•	Bounded explorer with symmetry & lasso CE ✅
	•	Adapters: DOT + Mermaid (and minimal TLA/Alloy subsets) ✅
	•	Runtime oracles from invariants ✅
	•	Doc-to-Lean generators (front-matter + fenced blocks) ✅
	•	Traceability matrix generator ✅
	•	Examples: mutex, queue, two-phase commit sketch, leader election sketch, ledger posting ✅

Stretch (future): prophecy variables templates; SMT/SAT plug-in; code-gen to test scaffolds—design leaves room for these.

⸻

If you want, I can turn this into a Lake repo skeleton (files + TODO stubs + the Mutex example) so you can git clone, run lake run spec, and see the gates & artifacts immediately.