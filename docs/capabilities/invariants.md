# Invariant Helpers

`LeanSpec.Dsl.Invariants` introduces the induction principle and automation used to discharge safety proofs:

- `System.invariant_induction` — prove an invariant by supplying base (`Init`) and step (`Next`) obligations.
- `inv_auto` — tactic shortcut that refines the current goal to the two subgoals required by `invariant_induction`.

`LeanSpec.Dsl.InvariantsTest` demonstrates the pattern on a bounded counter system whose `Next` relation constrains the value to remain ≤ 1.
