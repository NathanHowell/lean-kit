import Std.Data.HashSet
import LeanSpec.Dsl.Core
import LeanSpec.Dsl.Explorer.Scope

namespace LeanSpec
namespace Dsl
namespace Explorer

open System
open Std

variable {Σ : System}

structure StateCache (Σ : System) [BEq Σ.Store] [Hashable Σ.Store] where
  visited : HashSet Σ.Store := {}
  deriving Inhabited

namespace StateCache

variable {Σ : System} [BEq Σ.Store] [Hashable Σ.Store]

@[simp] def empty : StateCache Σ := {}

@[simp] def contains (cfg : Config Σ) (cache : StateCache Σ) (s : Σ.Store) : Bool :=
  cache.visited.contains (cfg.canonical s)

@[simp] def insert (cfg : Config Σ) (cache : StateCache Σ) (s : Σ.Store) : StateCache Σ :=
  { visited := cache.visited.insert (cfg.canonical s) }

end StateCache

end Explorer
end Dsl
end LeanSpec
