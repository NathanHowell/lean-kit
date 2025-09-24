# Explorer Configuration

The explorer consumes a `Config` containing:

- `scope.maxDepth` — maximum transition depth explored from the initial state.
- `scope.maxStates` — cap on visited states (controls BFS fuel).
- `symmetry` — optional canonicalisation function to reduce equivalent states.

The BFS driver expects a successor generator `Σ.Store → List (Σ.Label × Σ.Store)` and produces the trace to the first state satisfying a goal predicate. See `LeanSpec.Dsl.Explorer.Search` and `LeanSpec.Dsl.Explorer.SearchTest` for usage.
