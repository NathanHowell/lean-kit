import LeanSpec.Dsl.Core
import LeanSpec.Dsl.Temporal

namespace LeanSpec
namespace Dsl
namespace Liveness

open System
open Temporal

variable {Σ : System}

/-- Property `P` is stable if once true it remains true after each transition. -/
@[simp] def Stable (P : Σ.Store → Prop) : Prop :=
  ∀ ⦃s ℓ s'⦄, P s → Σ.Next s ℓ s' → P s'

/-- Property `P` ensures `Q` when every execution that starts in `P` eventually reaches `Q`. -/
@[simp] def Ensures (P Q : Σ.Store → Prop) : Prop :=
  LeadsTo (Σ:=Σ) P Q

lemma ensures_trans {P Q R : Σ.Store → Prop}
    (hPQ : Ensures (Σ:=Σ) P Q)
    (hQR : Ensures (Σ:=Σ) Q R) :
    Ensures (Σ:=Σ) P R :=
  LeadsTo.trans (Σ:=Σ) hPQ hQR

lemma ensures_mono_left {P P' Q : Σ.Store → Prop}
    (h : ∀ s, P s → P' s) :
    Ensures (Σ:=Σ) P' Q → Ensures (Σ:=Σ) P Q :=
  LeadsTo.mono_left (Σ:=Σ) h

lemma ensures_mono_right {P Q Q' : Σ.Store → Prop}
    (h : ∀ s, Q s → Q' s) :
    Ensures (Σ:=Σ) P Q → Ensures (Σ:=Σ) P Q' :=
  LeadsTo.mono_right (Σ:=Σ) h

end Liveness
end Dsl
end LeanSpec
