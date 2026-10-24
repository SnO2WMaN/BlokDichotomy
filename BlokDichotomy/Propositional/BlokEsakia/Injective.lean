module

public import BlokDichotomy.Propositional.BlokEsakia.Maps
public import BlokDichotomy.Propositional.GeneralFrame.Canonical
public import BlokDichotomy.Propositional.GeneralFrame.Companion

/-!
# Injectivity of `greatestMC` and `leastMC`

For a superintuitionistic logic `L`, the superintuitionistic fragments of `L.greatestMC = 𝐆𝐫𝐳 ⊕ Lᵍ`
and `L.leastMC = 𝐒𝟒 ⊕ Lᵍ` are both `L`. Hence `greatestMC` and `leastMC` are injective, and
`L.greatestMC` and `L.leastMC` are modal companions of `L`.

## References

- [CZ98, Theorem 9.57]
-/

@[expose] public section

universe v

namespace Propositional.Logic

variable {α : Type v} (L : Logic α) [L.IsExt 𝐈𝐧𝐭]

/-- The superintuitionistic fragment of `L.greatestMC` is `L`.
- [CZ98, Theorem 9.57] -/
theorem siFragment_greatestMC_eq : L.greatestMC.siFragment = L := by
  apply le_antisymm _ le_siFragment_greatestMC;
  intro A hA;
  by_contra hAL;
  have h₁ : L.canonicalGeneralFrame.toModal ⊧ L.greatestMC := by
    apply _root_.GeneralFrame.validatesLogic_add GeneralFrame.toModal_validates_logicGrz;
    rintro _ ⟨B, hB, rfl⟩;
    exact GeneralFrame.toModal_validates_gödelTranslate_iff.mpr
      (canonicalGeneralFrame.validatesLogic_self B hB);
  exact hAL <| canonicalGeneralFrame.validates_iff.mp
    (GeneralFrame.toModal_validates_gödelTranslate_iff.mp (h₁ _ hA))

/-- The superintuitionistic fragment of `L.leastMC` is `L`.
- [CZ98, Theorem 9.57] -/
theorem siFragment_leastMC_eq : L.leastMC.siFragment = L :=
  le_antisymm
    ((NormalLogic.siFragment_mono leastMC_le_greatestMC).trans (siFragment_greatestMC_eq L).le)
    le_siFragment_leastMC

/-- `L.leastMC` is a modal companion of `L`.
- [CZ98, Theorem 9.57] -/
theorem isModalCompanion_leastMC : L.IsModalCompanion L.leastMC := by
  intro A;
  constructor;
  · exact gödelTranslate_mem_leastMC;
  · intro h;
    have h₁ : A ∈ L.leastMC.siFragment := h;
    rwa [siFragment_leastMC_eq] at h₁;

/-- `L.greatestMC` is a modal companion of `L`.
- [CZ98, Theorem 9.57] -/
theorem isModalCompanion_greatestMC : L.IsModalCompanion L.greatestMC := by
  intro A;
  constructor;
  · exact gödelTranslate_mem_greatestMC;
  · intro h;
    have h₁ : A ∈ L.greatestMC.siFragment := h;
    rwa [siFragment_greatestMC_eq] at h₁;

end Propositional.Logic

end
