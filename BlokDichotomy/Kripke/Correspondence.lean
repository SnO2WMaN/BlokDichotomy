module

public import BlokDichotomy.Kripke.Basic

/-!
# Frame correspondence for `T` and `4`

A frame validates `T` iff it is reflexive, and `4` iff it is transitive; so the frames of `𝐒𝟒`
are exactly the reflexive and transitive ones.

## References

- [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31]
-/

@[expose] public section

universe u v

variable {κ : Type u} {α : Type v} {F : Frame κ}

namespace Frame

open Model.World

lemma validates_axiomsT_of_refl [Std.Refl F.Rel'] : F ⊧ (FormulaSet.axiomsT : FormulaSet α) := by
  rintro _ ⟨⟩ V x hx;
  exact forces_box.mp hx x <| refl x

lemma validates_axiomsFour_of_trans [IsTrans κ F.Rel'] :
    F ⊧ (FormulaSet.axiomsFour : FormulaSet α) := by
  rintro _ ⟨⟩ V x hx;
  exact forces_box.mpr fun y Rxy => forces_box.mpr fun z Ryz =>
    forces_box.mp hx z <| _root_.trans (r := F.Rel') Rxy Ryz

/-- - [CZ98, Proposition 3.30] -/
lemma refl_of_validates_axiomsT [Inhabited α] (h : F ⊧ (FormulaSet.axiomsT : FormulaSet α)) :
    Std.Refl F.Rel' where
  refl x := h _ (.t (φ := #default)) (fun y _ => x ≺ y) x <| forces_box.mpr fun _ Rxy => Rxy

/-- - [CZ98, Proposition 3.31] -/
lemma trans_of_validates_axiomsFour [Inhabited α]
    (h : F ⊧ (FormulaSet.axiomsFour : FormulaSet α)) : IsTrans κ F.Rel' where
  trans x y z Rxy Ryz :=
    forces_box.mp (forces_box.mp (h _ (.four (φ := #default)) (fun w _ => x ≺ w) x <|
      forces_box.mpr fun _ Rxw => Rxw) y Rxy) z Ryz

lemma validates_logicS4 [Std.Refl F.Rel'] [IsTrans κ F.Rel'] : F ⊧ (𝐒𝟒 : NormalLogic α) :=
  validates_add (validates_add validates_logicK validates_axiomsFour_of_trans)
    validates_axiomsT_of_refl

/-- The frames of `𝐒𝟒` are exactly the reflexive and transitive ones.

- [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31] -/
lemma validates_logicS4_iff [Inhabited α] :
    F ⊧ (𝐒𝟒 : NormalLogic α) ↔ Std.Refl F.Rel' ∧ IsTrans κ F.Rel' := by
  constructor;
  · intro h;
    exact ⟨refl_of_validates_axiomsT fun φ hφ => h φ <| NormalLogic.mem_add hφ,
      trans_of_validates_axiomsFour fun φ hφ => h φ <|
        NormalLogic.mem_add_of_mem <| NormalLogic.mem_add hφ⟩;
  · rintro ⟨_, _⟩;
    exact validates_logicS4

end Frame

end
