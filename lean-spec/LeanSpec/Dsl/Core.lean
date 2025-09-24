import Std

namespace LeanSpec
namespace Dsl

universe u v

/-- Core kernel describing a state-transition system. -/
structure System where
  /-- Set of possible states. -/
  Store : Type u
  /-- Labels annotate transitions (e.g. action names, events). -/
  Label : Type v
  /-- Initial-state predicate. -/
  Init : Store → Prop
  /-- Next-state relation; usually a disjunction of labeled actions. -/
  Next : Store → Label → Store → Prop

namespace System

variable {Σ : System}

/-- A single labeled step within the system. -/
structure Step (Σ : System) where
  before : Σ.Store
  label  : Σ.Label
  after  : Σ.Store
  witness : Σ.Next before label after

/-- Executions are infinite sequences of states with accompanying labels. -/
structure Execution (Σ : System) where
  state  : Nat → Σ.Store
  label  : Nat → Σ.Label
  init   : Σ.Init (state 0)
  step   : ∀ n, Σ.Next (state n) (label n) (state (n.succ))

/-- The raw state trace for an execution. -/
@[simp] def Execution.trace (ρ : Execution Σ) : Nat → Σ.Store := ρ.state

@[simp] lemma Execution.trace_zero (ρ : Execution Σ) : ρ.trace 0 = ρ.state 0 := rfl

@[simp] lemma Execution.trace_succ (ρ : Execution Σ) (n : Nat) :
    ρ.trace (Nat.succ n) = ρ.state (Nat.succ n) := rfl

/-- The first state in an execution. -/
@[simp] def Execution.head (ρ : Execution Σ) : Σ.Store := ρ.state 0

/-- Predicate stating that a property holds at every state along an execution. -/
@[simp] def Always (P : Σ.Store → Prop) (ρ : Execution Σ) : Prop :=
  ∀ n, P (ρ.state n)

/-- Predicate stating that a property eventually holds on some state. -/
@[simp] def Eventually (P : Σ.Store → Prop) (ρ : Execution Σ) : Prop :=
  ∃ n, P (ρ.state n)

/-- `LeadsTo P Q` captures the usual liveness obligation: whenever `P` holds,
`Q` will hold at some later (or equal) point. -/
def LeadsTo (P Q : Σ.Store → Prop) : Prop :=
  ∀ (ρ : Execution Σ) {n}, P (ρ.state n) → ∃ m, m ≥ n ∧ Q (ρ.state m)

/-- `Invariant` is a safety property satisfied on all states along executions
that start in an initial state. -/
def Invariant (P : Σ.Store → Prop) : Prop :=
  ∀ (ρ : Execution Σ), P (ρ.state 0) → Always P ρ

end System

end Dsl
end LeanSpec
