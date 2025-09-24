import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Dsl
namespace Explorer

open System

/-- Bounding parameters for the exploration. -/
structure Scope (Σ : System) where
  maxDepth : Nat := 32
  maxStates : Nat := 4096
  deriving Repr

/-- Symmetry reduction abstracts states to canonical representatives. -/
structure Symmetry (Σ : System) where
  canonical : Σ.Store → Σ.Store
  idempotent : ∀ s, canonical (canonical s) = canonical s

/-- Explorer configuration with optional symmetry settings. -/
structure Config (Σ : System) where
  scope : Scope Σ := {}
  symmetry : Option (Symmetry Σ) := none
  deriving Repr

@[simp] def Config.canonical {Σ : System} (cfg : Config Σ) : Σ.Store → Σ.Store
  | s => match cfg.symmetry with
    | none => s
    | some sym => sym.canonical s

end Explorer
end Dsl
end LeanSpec
