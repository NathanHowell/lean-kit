# Action Primitives

`LeanSpec.Dsl.Actions` provides building blocks for the `Next` relation:

- `Action.skip` — reflexive step that leaves the store unchanged.
- `Action.assign f` — deterministic step applying function `f` to the store.
- `Action.guarded g act` — executes `act` when predicate `g` holds in the current state.
- `Action.disj a b` — non-deterministic choice between `a` and `b`.
- `Action.seq a b` — relational composition (`a` followed by `b`).
- `Action.enabled act s` — witness that `act` has at least one successor from `s`.
- `Action.unchanged proj act` — projection `proj` is preserved by `act`.

`LeanSpec.Dsl.Composition` supplies algebraic laws (`seq_skip_left/right`, `seq_assoc`, `disj_comm`, `disj_assoc`) and rewrites for `enabled` on `disj`/`guarded`. Labeled actions connect these primitives to the `System.Next` relation via `LabeledAction.compile`.

Regression tests live in `LeanSpec.Dsl.ActionsTest` and cover sequential composition, guarded enablement, and label compilation.
