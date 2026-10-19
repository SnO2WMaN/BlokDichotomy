module

public import BlokDichotomy.Kripke.Basic

/-!
# Frame correspondence for `T` and `4`

A frame validates `T` iff it is reflexive, and `4` iff it is transitive. Hence the frames of `𝐒𝟒`
are exactly the reflexive transitive ones.

## References

- [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31]
-/

@[expose] public section

universe u v

variable {κ : Type u} {α : Type v} {F : Frame κ} {a : α} {φ : Formula α}

namespace Frame

open Model.World

lemma validates_T_of_refl [Std.Refl F.Rel'] : F ⊧ □φ 🡒 φ := by
  rintro V x hx;
  exact forces_box.mp hx x <| refl x

lemma validates_four_of_trans [IsTrans κ F.Rel'] {φ : Formula α} : F ⊧ □φ 🡒 □□φ := by
  rintro V x hx;
  exact forces_box.mpr fun y Rxy => forces_box.mpr fun z Ryz =>
    forces_box.mp hx z <| _root_.trans (r := F.Rel') Rxy Ryz

/-- - [CZ98, Proposition 3.30] -/
lemma refl_of_validates_T (h : F ⊧ (□#a 🡒 #a : Formula α)) : Std.Refl F.Rel' where
  refl x := h (fun y _ => x ≺ y) x <| forces_box.mpr fun _ Rxy => Rxy

/-- - [CZ98, Proposition 3.31] -/
lemma trans_of_validates_four (h : F ⊧ (□#a 🡒 □□#a : Formula α)) : IsTrans κ F.Rel' where
  trans x y z Rxy Ryz :=
    forces_box.mp (forces_box.mp (h (fun w _ => x ≺ w) x <|
      forces_box.mpr fun _ Rxw => Rxw) y Rxy) z Ryz

/-- - [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31] -/
lemma validates_logicS4 [Std.Refl F.Rel'] [IsTrans κ F.Rel'] : F ⊧ (𝐒𝟒 : NormalLogic α) := by
  refine validates_add (validates_add validates_logicK ?_) ?_
  · rintro _ ⟨φ, rfl⟩
    exact validates_four_of_trans
  · rintro _ ⟨φ, rfl⟩
    exact validates_T_of_refl

/-- - [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31] -/
lemma validates_logicS4_iff [Inhabited α] :
    F ⊧ (𝐒𝟒 : NormalLogic α) ↔ Std.Refl F.Rel' ∧ IsTrans κ F.Rel' := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨_, _⟩ => validates_logicS4⟩
  · exact refl_of_validates_T (a := (default : α)) <| h _ <| NormalLogic.mem_add ⟨#default, rfl⟩
  · exact trans_of_validates_four (a := (default : α)) <|
      h _ <| NormalLogic.mem_add_of_mem <| NormalLogic.mem_add ⟨#default, rfl⟩

end Frame

end
