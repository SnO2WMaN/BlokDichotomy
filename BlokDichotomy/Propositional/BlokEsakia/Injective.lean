module

public import BlokDichotomy.Propositional.BlokEsakia.Maps
public import BlokDichotomy.Propositional.GeneralFrame.Canonical
public import BlokDichotomy.Propositional.GeneralFrame.Companion

/-!
# Injectivity of `σ` and `τ`

For a superintuitionistic logic `L`, the superintuitionistic fragments of `σ L = 𝐆𝐫𝐳 ⊕ Lᵍ` and
`τ L = 𝐒𝟒 ⊕ Lᵍ` are both `L`. Hence `σ` and `τ` are injective, and `σ L` and `τ L` are modal
companions of `L`.

## References

- [CZ98, Theorem 9.57]
-/

@[expose] public section

universe v

namespace Propositional.Logic

variable {α : Type v} (L : Logic α) [L.IsExt 𝐈𝐧𝐭]

/-- The superintuitionistic fragment of `σ L` is `L`.
- [CZ98, Theorem 9.57] -/
theorem rho_sigma_eq : L.sigma.rho = L := by
  apply le_antisymm _ le_rho_sigma;
  intro A hA;
  by_contra hAL;
  have h₁ : L.canonicalGeneralFrame.toModal ⊧ L.sigma := by
    apply _root_.GeneralFrame.validatesLogic_add GeneralFrame.toModal_validates_logicGrz;
    rintro _ ⟨B, hB, rfl⟩;
    exact GeneralFrame.toModal_validates_gödelTranslate_iff.mpr
      (canonicalGeneralFrame.validatesLogic_self B hB);
  exact hAL <| canonicalGeneralFrame.validates_iff.mp
    (GeneralFrame.toModal_validates_gödelTranslate_iff.mp (h₁ _ hA))

/-- The superintuitionistic fragment of `τ L` is `L`.
- [CZ98, Theorem 9.57] -/
theorem rho_tau_eq : L.tau.rho = L :=
  le_antisymm ((NormalLogic.rho_mono tau_le_sigma).trans (rho_sigma_eq L).le) le_rho_tau

/-- `τ L` is a modal companion of `L`.
- [CZ98, Theorem 9.57] -/
theorem isModalCompanion_tau : L.IsModalCompanion L.tau := by
  intro A;
  constructor;
  · exact gödelTranslate_mem_tau;
  · intro h;
    have h₁ : A ∈ L.tau.rho := h;
    rwa [rho_tau_eq] at h₁;

/-- `σ L` is a modal companion of `L`.
- [CZ98, Theorem 9.57] -/
theorem isModalCompanion_sigma : L.IsModalCompanion L.sigma := by
  intro A;
  constructor;
  · exact gödelTranslate_mem_sigma;
  · intro h;
    have h₁ : A ∈ L.sigma.rho := h;
    rwa [rho_sigma_eq] at h₁;

end Propositional.Logic

end
