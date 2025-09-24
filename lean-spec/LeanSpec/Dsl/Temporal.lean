import Lean
import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Dsl
namespace Temporal

open Classical
open System

variable {Σ : System}

abbrev Always (P : Σ.Store → Prop) := System.Always (Σ:=Σ) P
abbrev Eventually (P : Σ.Store → Prop) := System.Eventually (Σ:=Σ) P
abbrev LeadsTo (P Q : Σ.Store → Prop) := System.LeadsTo (Σ:=Σ) P Q

namespace Always

lemma mono {P Q : Σ.Store → Prop}
    (h : ∀ s, P s → Q s) {ρ : System.Execution Σ}
    (hP : Always (Σ:=Σ) P ρ) : Always (Σ:=Σ) Q ρ := by
  intro n; exact h _ (hP n)

lemma of_forall {ρ : System.Execution Σ} {P : Σ.Store → Prop}
    (h : ∀ n, P (ρ.state n)) : Always (Σ:=Σ) P ρ := h

end Always

namespace Eventually

lemma mono {P Q : Σ.Store → Prop}
    (h : ∀ s, P s → Q s) {ρ : System.Execution Σ}
    (hP : Eventually (Σ:=Σ) P ρ) : Eventually (Σ:=Σ) Q ρ := by
  rcases hP with ⟨n, hPn⟩
  exact ⟨n, h _ hPn⟩

lemma of_exists {ρ : System.Execution Σ} {P : Σ.Store → Prop}
    (n : Nat) (h : P (ρ.state n)) : Eventually (Σ:=Σ) P ρ := ⟨n, h⟩

end Eventually

namespace LeadsTo

lemma refl (P : Σ.Store → Prop) : LeadsTo (Σ:=Σ) P P := by
  intro ρ n hPn; exact ⟨n, Nat.le_refl _, hPn⟩

lemma mono_left {P P' Q : Σ.Store → Prop}
    (h : ∀ s, P s → P' s) : LeadsTo (Σ:=Σ) P' Q → LeadsTo (Σ:=Σ) P Q := by
  intro hP ρ n hPn
  exact hP ρ (h _ hPn)

lemma mono_right {P Q Q' : Σ.Store → Prop}
    (h : ∀ s, Q s → Q' s) : LeadsTo (Σ:=Σ) P Q → LeadsTo (Σ:=Σ) P Q' := by
  intro hPQ ρ n hPn
  rcases hPQ ρ hPn with ⟨m, hm, hQ⟩
  exact ⟨m, hm, h _ hQ⟩

lemma trans {P Q R : Σ.Store → Prop}
    (hPQ : LeadsTo (Σ:=Σ) P Q) (hQR : LeadsTo (Σ:=Σ) Q R) :
    LeadsTo (Σ:=Σ) P R := by
  intro ρ n hPn
  rcases hPQ ρ hPn with ⟨m, hm, hQ⟩
  rcases hQR ρ hQ with ⟨k, hk, hR⟩
  refine ⟨k, ?_, hR⟩
  exact Nat.le_trans hm hk

lemma eventually_of_leadsTo {P Q : Σ.Store → Prop}
    {ρ : System.Execution Σ} {n}
    (hPn : P (ρ.state n))
    (hPQ : LeadsTo (Σ:=Σ) P Q) :
    Eventually (Σ:=Σ) Q ρ := by
  rcases hPQ ρ hPn with ⟨m, _, hQ⟩
  exact Eventually.of_exists (Σ:=Σ) m hQ

end LeadsTo

end Temporal
end Dsl
end LeanSpec
