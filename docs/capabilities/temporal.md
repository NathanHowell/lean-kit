# Temporal Reasoning

`LeanSpec.Dsl.Temporal` reuses the core execution model to provide helper aliases and
lemmas:

- `Always` / `Eventually` — wrappers around `System.Always` and `System.Eventually`.
- `LeadsTo` — temporal progress predicate with reflexivity and monotonicity lemmas.
- Utility lemmas:
  - `Always.mono` — lift invariants under implication.
  - `Eventually.mono` — push implication through eventuality.
  - `LeadsTo.trans` — compose progress steps.

`LeanSpec.Dsl.TemporalTest` shows how to use these primitives on a simple incrementing
system.
