---
capability: queue
title: Single-slot Queue
status: draft
owners:
  - platform
summary: >-
  Bounded queue with capacity one, exposing `enqueue` and `dequeue` actions and
  guaranteeing that a successful dequeue eventually empties the buffer.
---

# Intent

Model a minimal queue where the buffer holds at most one element. Safety enforces the
capacity constraint, while liveness ensures that dequeue operations eventually clear the
queue when they succeed.

# Interfaces

- `enqueue(x)` — adds value `x` if the buffer is empty; otherwise stutters.
- `dequeue()` — removes the element when present; otherwise stutters.

# Guarantees

- **Safety**: Buffer length never exceeds one.
- **Liveness**: Whenever the queue is non-empty, a dequeue transition eventually leads to the empty state.

# Notes

Specification and proofs reside in `LeanSpec.Spec.Examples.Queue`. Use the explorer to
search for counterexamples involving back-to-back enqueues without dequeues.

The safety proof `LeanSpec.Spec.Examples.Queue.safety` bounds the buffer, and `dequeue_eventually_empty` shows `full` ensures `empty` in one step.
