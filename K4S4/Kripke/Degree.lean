module

public import BlokDichotomy.Modal.Kripke.Degree

/-!
# Intersections of Kripke-complete logics and frame companions

Kripke completeness is preserved under intersection. Over infinitely many variables,
intersection also preserves frame equivalence on all Kripke frames.
-/

@[expose] public section

namespace Modal

universe u v

variable {α : Type v} {L₀ L₁ L₂ L₃ : NormalLogic α}
  {P : ⦃κ : Type u⦄ → Frame κ → Prop}

lemma NormalLogic.KripkeComplete.inter (h₁ : L₁.KripkeComplete P) (h₂ : L₂.KripkeComplete P) :
    (L₁ ∩ L₂).KripkeComplete P :=
  fun _ hφ => ⟨h₁ <| NormalLogic.frameLogic_mono (L₁ := L₁ ∩ L₂) (L₂ := L₁)
    (fun _ h => h.1) hφ, h₂ <| NormalLogic.frameLogic_mono (L₁ := L₁ ∩ L₂) (L₂ := L₂)
      (fun _ h => h.2) hφ⟩

lemma Frame.kripkeComplete_logic {κ : Type u} (F : Frame κ) (hF : P F) :
    (F.logic (α := α)).KripkeComplete P :=
  fun _ h => h F hF (fun _ hφ => hφ)

lemma Frame.validateLogic_inter_iff_forall_pointGenerate {κ : Type u} {F : Frame κ}
    [Infinite α] [L₁.IsNExt 𝐊] [L₂.IsNExt 𝐊] :
    F ⊧ (L₁ ∩ L₂) ↔ ∀ x : F.World, (F⥜x ⊧ L₁) ∨ (F⥜x ⊧ L₂) := by
  constructor;
  · intro h x;
    exact validates_inter_of_isRooted_of_infinite isRooted_pointGenerate h.pointGenerate;
  · intro h;
    apply Frame.validateLogic_iff_forall_pointGenerate.mpr;
    intro x φ hφ;
    rcases h x with h₁ | h₂;
    · exact h₁ φ hφ.1;
    · exact h₂ φ hφ.2;

/-- Intersections preserve frame equivalence on an infinite set of variables. -/
theorem NormalLogic.FrameEquiv.inter [Infinite α] [L₁.IsNExt 𝐊] [L₂.IsNExt 𝐊]
    [L₃.IsNExt 𝐊] [L₀.IsNExt 𝐊]
    (h₁ : NormalLogic.FrameEquiv.{u} (fun _ _ => True) L₁ L₂)
    (h₂ : NormalLogic.FrameEquiv.{u} (fun _ _ => True) L₃ L₀) :
    NormalLogic.FrameEquiv.{u} (fun _ _ => True) (L₁ ∩ L₃) (L₂ ∩ L₀) := by
  intro κ F _;
  rw [Frame.validateLogic_inter_iff_forall_pointGenerate,
    Frame.validateLogic_inter_iff_forall_pointGenerate];
  exact forall_congr' fun x => or_congr (h₁ (F⥜x) trivial) (h₂ (F⥜x) trivial);

end Modal
