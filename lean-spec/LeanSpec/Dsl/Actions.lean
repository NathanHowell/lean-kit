import LeanSpec.Dsl.Core

namespace LeanSpec
namespace Dsl

open System

namespace System

/-- Unlabeled actions are binary relations on stores. -/
@[simp] def Action (Σ : System) : Type _ :=
  Σ.Store → Σ.Store → Prop

namespace Action

variable {Σ : System}

/-- Skip action that leaves the store unchanged. -/
@[simp] def skip : Action Σ := fun s s' => s' = s

@[simp] lemma skip_apply {s s'} : skip (Σ:=Σ) s s' ↔ s' = s := Iff.rfl

/-- Deterministic assignment-style action. -/
@[simp] def assign (f : Σ.Store → Σ.Store) : Action Σ :=
  fun s s' => s' = f s

@[simp] lemma assign_apply {f : Σ.Store → Σ.Store} {s s'} :
    assign (Σ:=Σ) f s s' ↔ s' = f s := Iff.rfl

/-- Guarded action that requires predicate `g` before running `act`. -/
@[simp] def guarded (g : Σ.Store → Prop) (act : Action Σ) : Action Σ :=
  fun s s' => g s ∧ act s s'

/-- Disjunction (non-deterministic choice) of actions. -/
@[simp] def disj (a b : Action Σ) : Action Σ :=
  fun s s' => a s s' ∨ b s s'

/-- Relational composition of actions (sequential execution). -/
@[simp] def seq (a b : Action Σ) : Action Σ :=
  fun s u => ∃ t, a s t ∧ b t u

/-- Predicate stating that an action leaves a projection unchanged. -/
@[simp] def unchanged {β : Sort _} (proj : Σ.Store → β) (act : Action Σ) : Prop :=
  ∀ ⦃s s'⦄, act s s' → proj s' = proj s

/-- An action is enabled if it has at least one successor from `s`. -/
@[simp] def enabled (act : Action Σ) (s : Σ.Store) : Prop :=
  ∃ s', act s s'

@[simp] lemma skip_enabled (s : Σ.Store) : enabled (skip (Σ:=Σ)) s :=
  ⟨s, rfl⟩

@[simp] lemma assign_enabled {f : Σ.Store → Σ.Store} (s : Σ.Store) :
    enabled (assign (Σ:=Σ) f) s :=
  ⟨f s, rfl⟩

lemma seq_intro {a b : Action Σ} {s t u : Σ.Store}
    (ha : a s t) (hb : b t u) : seq a b s u :=
  ⟨t, ha, hb⟩

lemma seq_elim {a b : Action Σ} {s u : Σ.Store} :
    seq a b s u → ∃ t, a s t ∧ b t u :=
  id

end Action

/-- Labeled actions bridge unlabeled actions with system labels. -/
structure LabeledAction (Σ : System) where
  label  : Σ.Label
  action : Action Σ

namespace LabeledAction

variable {Σ : System}

/-- Interpret a labeled action as a fragment of the `Next` relation. -/
@[simp] def toNext (a : LabeledAction Σ) : Σ.Store → Σ.Label → Σ.Store → Prop :=
  fun s ℓ s' => ℓ = a.label ∧ a.action s s'

/-- Compose a list of labeled actions into a `Next` relation. -/
@[simp] def compile (acts : List (LabeledAction Σ)) :
    Σ.Store → Σ.Label → Σ.Store → Prop :=
  fun s ℓ s' => ∃ act ∈ acts, ℓ = act.label ∧ act.action s s'

lemma of_mem {acts : List (LabeledAction Σ)}
    {s s' : Σ.Store} {ℓ : Σ.Label}
    {act : LabeledAction Σ} (h_mem : act ∈ acts)
    (h_step : act.action s s') :
    compile acts s ℓ s' ↔ ℓ = act.label ∧ act.action s s' ∨
      ∃ b ∈ acts, b ≠ act ∧ ℓ = b.label ∧ b.action s s' := by
  constructor
  · intro h; rcases h with ⟨b, b_mem, hb_label, hb_action⟩
    by_cases hba : b = act
    · subst hba; exact Or.inl ⟨hb_label, hb_action⟩
    · exact Or.inr ⟨b, b_mem, hba, hb_label, hb_action⟩
  · intro h
    cases h with
    | inl h' => rcases h' with ⟨hb_label, hb_action⟩; exact ⟨act, h_mem, hb_label, hb_action⟩
    | inr h' =>
        rcases h' with ⟨b, hb_mem, _, hb_label, hb_action⟩
        exact ⟨b, hb_mem, hb_label, hb_action⟩

end LabeledAction

end System

end Dsl
end LeanSpec
