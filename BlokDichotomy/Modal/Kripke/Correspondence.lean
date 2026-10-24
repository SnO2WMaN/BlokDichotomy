module

public import BlokDichotomy.Modal.Kripke.Completeness

/-!
# Frame correspondence for `T` and `4`

A frame validates `T` iff it is reflexive, and `4` iff it is transitive. Hence the frames of `𝐒𝟒`
are exactly the reflexive transitive ones, and `𝐒𝟒` is complete for them.

## References

- [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31]
- [CZ98, Corollary 5.18]
-/

@[expose] public section

namespace Modal

universe u v

variable {κ : Type u} {α : Type v} {F : Frame κ} {a : α} {A : Formula α}

namespace Frame

open Model.World

lemma validates_T_of_refl [Std.Refl F.Rel] : F ⊧ □A 🡒 A := by
  rintro V x hx;
  exact forces_box.mp hx x <| refl x

lemma validates_four_of_trans [IsTrans _ F.Rel] {A : Formula α} : F ⊧ □A 🡒 □□A := by
  rintro V x hx;
  exact forces_box.mpr fun y Rxy => forces_box.mpr fun z Ryz =>
    forces_box.mp hx z <| _root_.trans (r := F.Rel) Rxy Ryz

/-- - [CZ98, Proposition 3.30] -/
lemma refl_of_validates_T (h : F ⊧ (□#a 🡒 #a)) : Std.Refl F.Rel where
  refl x := h (fun y _ => x ≺ y) x <| forces_box.mpr fun _ Rxy => Rxy

/-- - [CZ98, Proposition 3.31] -/
lemma trans_of_validates_four (h : F ⊧ (□#a 🡒 □□#a)) : IsTrans _ F.Rel where
  trans x y z Rxy Ryz :=
    forces_box.mp (forces_box.mp (h (fun w _ => x ≺ w) x <|
      forces_box.mpr fun _ Rxw => Rxw) y Rxy) z Ryz

/-- - [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31] -/
lemma validates_logicS4 [Std.Refl F.Rel] [IsTrans _ F.Rel] : F ⊧ logicS4 (α := α) := by
  refine validates_add (validates_add validates_logicK ?_) ?_
  · rintro _ ⟨A, rfl⟩
    exact validates_four_of_trans
  · rintro _ ⟨A, rfl⟩
    exact validates_T_of_refl

/-- - [CZ98, Proposition 3.30]
- [CZ98, Proposition 3.31] -/
lemma validates_logicS4_iff [Inhabited α] :
    F ⊧ logicS4 (α := α) ↔ Std.Refl F.Rel ∧ IsTrans _ F.Rel := by
  constructor;
  · intro h;
    constructor;
    · exact refl_of_validates_T (a := default) <| h _ <| NormalLogic.mem_add ⟨#default, rfl⟩;
    · exact trans_of_validates_four (a := default) <|
        h _ <| NormalLogic.mem_add_of_mem <| NormalLogic.mem_add ⟨#default, rfl⟩;
  · rintro ⟨_, _⟩;
    exact validates_logicS4

end Frame

namespace NormalLogic

variable {α : Type v} {A : Formula α}

namespace canonicalFrame

instance {L : NormalLogic α} [L.IsNExt 𝐒𝟒] :
    IsPreorder (L.canonicalFrame |>.World) (· ≺ ·) where
  refl x := by
    rw [rel_iff_box];
    intro A hA;
    exact x.mem_of_imp_mem axiomT hA;
  trans x y z Rxy Ryz := by
    rw [rel_iff_box] at Rxy Ryz ⊢;
    intro A hA;
    exact Ryz A <| Rxy _ <| x.mem_of_imp_mem axiomFour hA;

end canonicalFrame

/-- `𝐒𝟒` is sound and complete for the reflexive transitive frames.
- [CZ98, Corollary 5.18] -/
theorem mem_logicS4_iff :
    A ∈ 𝐒𝟒 ↔ ∀ {κ : Type v} (F : Frame κ) [IsPreorder _ F.Rel], F ⊧ A := by
  constructor;
  · intro h κ F _;
    exact Frame.validates_logicS4 _ h;
  · intro h;
    apply NormalLogic.mem_iff_canonicalModel_validates.mpr;
    exact h 𝐒𝟒.canonicalFrame _;

end NormalLogic

end Modal

end
