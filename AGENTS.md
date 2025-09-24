# AGENTS

## Planner Agent
- **Purpose**: Maintain `PLAN.md`, decompose milestones into actionable tasks with tests, proofs, and documentation updates.
- **Inputs**: `INSTRUCTIONS.md`, stakeholder goals, current repo state.
- **Outputs**: Updated `PLAN.md` with checked boxes for completed tasks and newly scheduled items.
- **Handoff**: Signals Spec and Implement agents when a task moves from backlog to in-progress.

## Spec Agent
- **Purpose**: Author Lean specifications and associated proof obligations for each capability.
- **Inputs**: Capability docs under `docs/capabilities/`, task definitions from `PLAN.md`.
- **Outputs**: Lean files in `lean-spec/Spec/`, updated proofs, exported artifacts.
- **Handoff**: Provides Proof Agent with theorem stubs and Explorer Agent with models.

## Proof Agent
- **Purpose**: Complete safety and liveness proofs, ensure invariants and refinement obligations discharge.
- **Inputs**: Lean modules from Spec Agent, explorer counterexamples.
- **Outputs**: Proven theorems, proof scripts, or documented counterexamples with proposed fixes.
- **Handoff**: Returns verified modules to Implement Agent; communicates failures back to Spec Agent.

## Explorer Agent
- **Purpose**: Configure bounded model searches and analyze counterexamples.
- **Inputs**: Models in `docs/models/`, Lean specs, task-specific bounds from `PLAN.md`.
- **Outputs**: CE traces, `.dot`/Mermaid exports, updated model configs.
- **Handoff**: Supplies Proof and Docs Agents with traces and analysis summaries.

## Implement Agent
- **Purpose**: Build supporting tooling (CLI, generators, exporters) and maintain project infrastructure.
- **Inputs**: Requirements from `PLAN.md`, feedback from Spec/Proof agents.
- **Outputs**: Lean and auxiliary code under `/lean-spec/` and `/docs/`, passing builds/tests.
- **Handoff**: Requests Docs Agent to capture new behaviours; notifies CI Agent of changes.

## Docs Agent
- **Purpose**: Keep documentation synchronized with the current state of specs, proofs, and tooling.
- **Inputs**: Updates from all agents, especially task deliverables.
- **Outputs**: Revised markdown in `/docs/`, changelog entries, prompt templates.
- **Handoff**: Confirms with Planner Agent that documentation requirements are satisfied per task.

## CI Agent
- **Purpose**: Ensure automation (SPEC, PLAN, IMPLEMENT gates) works and remains trustworthy.
- **Inputs**: Workflow definitions in `.github/workflows/`, test suites, build logs.
- **Outputs**: Verified CI pipelines, badges, failure diagnostics.
- **Handoff**: Alerts Planner Agent and Implement Agent about regressions or flaky jobs.

## Runtime Agent
- **Purpose**: Generate and operate runtime oracles derived from invariants.
- **Inputs**: Invariant definitions, NDJSON logs, runtime checker tooling.
- **Outputs**: Oracle binaries, violation reports, monitoring dashboards.
- **Handoff**: Provides feedback to Proof and Docs Agents for runtime guarantees documentation.
