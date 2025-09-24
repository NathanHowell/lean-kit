import Lean
import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Dsl

open System
open Lean

namespace System

variable {Σ : System}

/-- Invariant induction principle using the system's `Init` and `Next`. -/
lemma invariant_induction {P : Σ.Store → Prop}
    (h_init : ∀ s, Σ.Init s → P s)
    (h_step : ∀ {s ℓ s'}, P s → Σ.Next s ℓ s' → P s') :
    Invariant (Σ:=Σ) P := by
  intro ρ hρ
  have h₀ : P (ρ.state 0) := h_init _ ρ.init
  intro n
  have : ∀ m, P (ρ.state m) := by
    intro m
    induction m with
    | zero => simpa using h₀
    | succ m ih =>
        have := h_step ih (ρ.step m)
        simpa using this
  simpa using this n

end System

/-- Tactic that refines the invariant goal to the induction principle. -/
syntax (name := invAuto) "inv_auto" : tactic

open Elab.Tactic Meta

@[tactic invAuto] def evalInvAuto : Tactic := fun _ =>
  evalTactic (← `(tactic|
    refine System.invariant_induction ?_ ?_
  ))

end Dsl
end LeanSpec
