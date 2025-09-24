import LeanSpec.Dsl.Core
import LeanSpec.Dsl.Explorer.Scope
import LeanSpec.Dsl.Explorer.Hashing

namespace LeanSpec
namespace Dsl
namespace Explorer

open System

variable {Σ : System}

structure Node (Σ : System) where
  state : Σ.Store
  depth : Nat
  trace : List (Σ.Label × Σ.Store)
  deriving Repr

@[simp] def Node.nextDepth (node : Node Σ) : Nat := node.depth + 1

structure Result (Σ : System) where
  steps : List (Σ.Label × Σ.Store)
  deriving Repr

variable [BEq Σ.Store] [Hashable Σ.Store]

private def enqueueSucc (cfg : Config Σ) (node : Node Σ)
    (succ : Σ.Label × Σ.Store)
    (cache : StateCache Σ) (queue : List (Node Σ)) (visited : Nat) :
    StateCache Σ × List (Node Σ) × Nat :=
  let (label, nextState) := succ
  if node.nextDepth > cfg.scope.maxDepth then
    (cache, queue, visited)
  else if StateCache.contains cfg cache nextState then
    (cache, queue, visited)
  else if visited ≥ cfg.scope.maxStates then
    (cache, queue, visited)
  else
    let cache' := StateCache.insert cfg cache nextState
    let trace' := node.trace ++ [(label, nextState)]
    let entry := Node.mk nextState node.nextDepth trace'
    (cache', queue ++ [entry], visited + 1)

private def bfsLoop (cfg : Config Σ)
    (succ : Σ.Store → List (Σ.Label × Σ.Store))
    (goal : Σ.Store → Bool)
    : Nat → List (Node Σ) → StateCache Σ → Nat → Option (Result Σ)
  | 0, _, _, _ => none
  | Nat.succ fuel, [], _, _ => none
  | Nat.succ fuel, node :: rest, cache, visited =>
      if goal node.state then
        some ⟨node.trace⟩
      else
        let neighbors := succ node.state
        let (cache', queue', visited') :=
          neighbors.foldl (fun acc succState =>
              let (cacheAcc, queueAcc, visitedAcc) := acc
              enqueueSucc cfg node succState cacheAcc queueAcc visitedAcc
            ) (cache, rest, visited)
        bfsLoop fuel queue' cache' visited'

/-- Breadth-first exploration up to the configured scope. Returns the trace to the
first state satisfying `goal`, if found. -/
@[simp] def bfs (cfg : Config Σ)
    (succ : Σ.Store → List (Σ.Label × Σ.Store))
    (init : Σ.Store)
    (goal : Σ.Store → Bool) : Option (Result Σ) :=
  let initNode := Node.mk init 0 []
  let cache0 := StateCache.insert cfg StateCache.empty init
  bfsLoop cfg succ goal cfg.scope.maxStates [initNode] cache0 1

end Explorer
end Dsl
end LeanSpec
