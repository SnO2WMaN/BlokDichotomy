module

public import K4S4.Construction.Kripke
public import K4S4.Construction.Validity

/-!
# Independent membership patterns above S4

The indexed extensions have a common class of validating Kripke frames. Their coding
formulas and the logics of the underlying frames record exactly the omitted indices.
-/

@[expose] public section

namespace Modal.K4S4.Construction

variable {I : Set ℕ}

instance : ((frame I).logic (α := ℕ)).IsNExt 𝐒𝟒 :=
  ⟨fun A hA => Frame.validates_logicS4 A hA⟩

lemma generalFrame_validates_baseLogic : generalFrame I ⊧ baseLogic := by
  apply GeneralFrame.validatesLogic_add;
  · exact fun A hA => GeneralFrame.validates_of_toFrame <|
      Frame.validates_logicS4 (F := frame I) A hA;
  · rintro _ (rfl | ⟨n, rfl⟩);
    · exact generalFrame_validates_sigma;
    · exact GeneralFrame.validates_of_toFrame <| frame_validates_theta I n;

lemma generalFrame_validates_sourceLogic : generalFrame I ⊧ sourceLogic I := by
  apply GeneralFrame.validatesLogic_add generalFrame_validates_baseLogic;
  rintro _ ⟨n, hn, rfl⟩;
  exact GeneralFrame.validates_of_toFrame <| frame_validates_chi.mpr hn;

lemma chi_mem_sourceLogic_iff (n : ℕ) : chi n ∈ sourceLogic I ↔ n ∉ I := by
  constructor;
  · intro h hn;
    exact generalFrame_not_validates_chi hn <| generalFrame_validates_sourceLogic _ h;
  · intro hn;
    exact NormalLogic.mem_add ⟨n, hn, rfl⟩;

end Modal.K4S4.Construction
