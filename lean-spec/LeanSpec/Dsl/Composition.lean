import LeanSpec.Dsl.Actions

namespace LeanSpec
namespace Dsl

open Classical
open List
open System

namespace System
namespace Action

variable {Σ : System}

@[simp] lemma seq_skip_left (a : Action Σ) :
    seq skip a = a := by
  funext s u; apply propext
  constructor
  · intro h
    rcases h with ⟨t, hskip, ha⟩
    have : t = s := by simpa [skip] using hskip
    subst this
    simpa using ha
  · intro ha
    exact ⟨s, rfl, ha⟩

@[simp] lemma seq_skip_right (a : Action Σ) :
    seq a skip = a := by
  funext s u; apply propext
  constructor
  · intro h
    rcases h with ⟨t, ha, hskip⟩
    have : u = t := by simpa [skip] using hskip
    subst this
    simpa using ha
  · intro ha
    exact ⟨u, ha, rfl⟩

lemma seq_assoc (a b c : Action Σ) :
    seq (seq a b) c = seq a (seq b c) := by
  funext s u; apply propext
  constructor
  · intro h
    rcases h with ⟨t, ⟨mid, ha, hb⟩, hc⟩
    exact ⟨mid, ha, ⟨t, hb, hc⟩⟩
  · intro h
    rcases h with ⟨mid, ha, ⟨t, hb, hc⟩⟩
    exact ⟨t, ⟨mid, ha, hb⟩, hc⟩

@[simp] lemma disj_comm (a b : Action Σ) :
    disj a b = disj b a := by
  funext s u; apply propext; constructor
  · intro h; rcases h with h | h <;> [exact Or.inr h; exact Or.inl h]
  · intro h; rcases h with h | h <;> [exact Or.inr h; exact Or.inl h]

lemma disj_assoc (a b c : Action Σ) :
    disj (disj a b) c = disj a (disj b c) := by
  funext s u; apply propext; constructor
  · intro h
    rcases h with h | h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro h
    rcases h with h | h
    · exact Or.inl (Or.inl h)
    · rcases h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

@[simp] lemma enabled_disj {a b : Action Σ} {s : Σ.Store} :
    enabled (disj a b) s ↔ enabled a s ∨ enabled b s := by
  constructor
  · intro h; rcases h with ⟨u, h⟩; cases h with
    | inl ha => exact Or.inl ⟨u, ha⟩
    | inr hb => exact Or.inr ⟨u, hb⟩
  · intro h; rcases h with h | h
    · rcases h with ⟨u, ha⟩; exact ⟨u, Or.inl ha⟩
    · rcases h with ⟨u, hb⟩; exact ⟨u, Or.inr hb⟩

@[simp] lemma enabled_guarded {g : Σ.Store → Prop} {a : Action Σ} {s : Σ.Store} :
    enabled (guarded g a) s ↔ g s ∧ enabled a s := by
  constructor
  · intro h
    rcases h with ⟨u, ⟨hg, ha⟩⟩
    exact ⟨hg, ⟨u, ha⟩⟩
  · intro h
    rcases h with ⟨hg, ⟨u, ha⟩⟩
    exact ⟨u, ⟨hg, ha⟩⟩

end Action

namespace LabeledAction

variable {Σ : System}

@[simp] lemma compile_cons (act : LabeledAction Σ) (acts : List (LabeledAction Σ)) :
    compile (act :: acts) =
      fun s ℓ s' => (ℓ = act.label ∧ act.action s s') ∨ compile acts s ℓ s' := by
  funext s ℓ s'; apply propext; constructor
  · intro h
    rcases h with ⟨b, hb_mem, hb_label, hb_action⟩
    cases hb_mem with
    | head => exact Or.inl ⟨hb_label, hb_action⟩
    | tail hb_mem => exact Or.inr ⟨b, hb_mem, hb_label, hb_action⟩
  · intro h
    cases h with
    | inl h' =>
        rcases h' with ⟨hb_label, hb_action⟩
        exact ⟨act, List.mem_cons_self (a := act) (l := acts), hb_label, hb_action⟩
    | inr h' =>
        rcases h' with ⟨b, hb_mem, hb_label, hb_action⟩
        exact ⟨b, List.mem_cons_of_mem (a := act) hb_mem, hb_label, hb_action⟩

end LabeledAction

end System

end Dsl
end LeanSpec
