---
capability: mutex
title: Mutual Exclusion Controller
status: draft
owners:
  - platform
summary: >-
  Lightweight controller that ensures exactly one worker performs a critical action
  at a time. Models safety (exclusion) and outlines eventual release obligations.
---

# Intent

The mutex protects a single critical section shared by multiple worker processes. The
model focuses on: (1) restricting simultaneous ownership, (2) capturing queued
requests, and (3) guaranteeing that a holder eventually releases the lock.

# Interfaces

- `Acquire(worker)` — Worker requests ownership. Enabled when the mutex is free or the
  worker already holds it.
- `Release(worker)` — Worker relinquishes ownership. Enabled only for the current owner.

# Guarantees

- **Safety**: At most one worker may hold the lock.
- **Fairness sketch**: If a worker remains enabled to release, it eventually does.

# Scenarios

1. `Acquire(w1)` then `Release(w1)` — canonical acquire/release pair.
2. `Acquire(w1)` followed by concurrent `Acquire(w2)` — second request waits until
   the first releases.
3. `Acquire(w1)` without release — explorer should exhibit a counterexample for
   progress obligations.

# Notes

This document seeds the automatic spec generator; additional structure (e.g., state
variables or temporal properties) will be refined in later iterations.

# Specification

- Store: `List Nat` capturing the active holders (length ≤ 1 invariant).
- Labels: `acquire n` and `release n`.
- `Next`: acquiring when free installs `[n]`; releases clear the holder; conflicting requests stutter.

The proof `LeanSpec.Spec.Examples.Mutex.safety` certifies the length invariant using `inv_auto`.
