# Core Semantics

`LeanSpec.Dsl.Core` defines the foundational `System` kernel used throughout the toolkit:

- `System` captures the store type, label type, `Init` predicate, and `Next` relation.
- `System.Step` packages a single labeled transition with its proof witness.
- `System.Execution` represents an infinite run with per-step labels and proof that each transition respects `Next`.
- Temporal shells:
  - `System.Always P ρ` — property `P` holds at every state of execution `ρ`.
  - `System.Eventually P ρ` — `P` holds at some state along `ρ`.
  - `System.LeadsTo P Q` — whenever `P` holds at step `n`, `Q` will hold for some step `m ≥ n`.
  - `System.Invariant P` — if `P` holds initially, it remains true for every state of every execution.

A regression test (`LeanSpec.Dsl.CoreTest`) exercises these definitions using a simple boolean toggle system.
