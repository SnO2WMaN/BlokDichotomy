module

public import BlokDichotomy.Propositional.BlokEsakia.Injective
public import BlokDichotomy.Propositional.BlokEsakia.Surjective

/-!
# The Blok–Esakia theorem

The map `σ L = 𝐆𝐫𝐳 ⊕ Lᵍ` is an order isomorphism from the superintuitionistic logics onto the
normal extensions of `𝐆𝐫𝐳`, with inverse `ρ`. In particular `σ 𝐈𝐧𝐭 = 𝐆𝐫𝐳`, `τ 𝐈𝐧𝐭 = 𝐒𝟒`, and
`ρ 𝐒𝟒 = ρ 𝐆𝐫𝐳 = 𝐈𝐧𝐭`.

## References

- [Blo76]
- [Esa76]
- [CZ98, Theorem 9.66]
-/

@[expose] public section

universe v

namespace Propositional

variable {α : Type v}

instance (L : {L : Logic α // L.IsExt 𝐈𝐧𝐭}) : L.1.IsExt 𝐈𝐧𝐭 := L.2

instance (L' : {L' : NormalLogic α // L'.IsNExt 𝐆𝐫𝐳}) : L'.1.IsNExt 𝐆𝐫𝐳 := L'.2

/-- The Blok–Esakia isomorphism between the superintuitionistic logics and the normal extensions
of `𝐆𝐫𝐳`, `L ↦ 𝐆𝐫𝐳 ⊕ Lᵍ`, with inverse `L' ↦ {A | Aᵍ ∈ L'}`.
- [Blo76]
- [Esa76]
- [CZ98, Theorem 9.66] -/
noncomputable def blokEsakia (α : Type v) [Infinite α] :
    {L : Logic α // L.IsExt 𝐈𝐧𝐭} ≃o {L' : NormalLogic α // L'.IsNExt 𝐆𝐫𝐳} where
  toFun L := ⟨L.1.sigma, inferInstance⟩
  invFun L' := ⟨L'.1.rho, inferInstance⟩
  left_inv L := Subtype.ext (Logic.rho_sigma_eq L.1)
  right_inv L' := Subtype.ext (sigma_rho_eq L'.1)
  map_rel_iff' {L₁ L₂} := by
    constructor;
    · intro h;
      have h₁ := NormalLogic.rho_mono (L := L₁.1.sigma) (L' := L₂.1.sigma) h;
      rwa [Logic.rho_sigma_eq, Logic.rho_sigma_eq] at h₁;
    · exact Logic.sigma_mono

@[simp] lemma blokEsakia_apply [Infinite α] (L : {L : Logic α // L.IsExt 𝐈𝐧𝐭}) :
    (blokEsakia α L).1 = L.1.sigma := rfl

@[simp] lemma blokEsakia_symm_apply [Infinite α] (L' : {L' : NormalLogic α // L'.IsNExt 𝐆𝐫𝐳}) :
    ((blokEsakia α).symm L').1 = L'.1.rho := rfl

namespace Logic

/-- `τ 𝐈𝐧𝐭 = 𝐒𝟒`.
- [CZ98, §3.9, Example 9.63] -/
theorem tau_logicInt : (𝐈𝐧𝐭 : Logic α).tau = 𝐒𝟒 :=
  le_antisymm (tau_le fun _ hA => gödelTranslate_mem_logicS4_iff.mp hA) NormalLogic.le_add

/-- `σ 𝐈𝐧𝐭 = 𝐆𝐫𝐳`.
- [CZ98, §3.9, Example 9.63] -/
theorem sigma_logicInt : (𝐈𝐧𝐭 : Logic α).sigma = 𝐆𝐫𝐳 :=
  le_antisymm
    (sigma_le fun _ hA => NormalLogic.logicS4_le_logicGrz (gödelTranslate_mem_logicS4_iff.mp hA))
    NormalLogic.le_add

end Logic

/-- `ρ 𝐒𝟒 = 𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem _root_.NormalLogic.rho_logicS4 : (𝐒𝟒 : NormalLogic α).rho = 𝐈𝐧𝐭 :=
  SetLike.ext fun _ => gödelTranslate_mem_logicS4_iff.symm

/-- `ρ 𝐆𝐫𝐳 = 𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem _root_.NormalLogic.rho_logicGrz : (𝐆𝐫𝐳 : NormalLogic α).rho = 𝐈𝐧𝐭 := by
  apply SetLike.ext;
  intro A;
  have h : Aᵍ ∈ (𝐈𝐧𝐭 : Logic α).sigma ↔ A ∈ 𝐈𝐧𝐭 := by
    rw [← NormalLogic.mem_rho, Logic.rho_sigma_eq];
  rw [NormalLogic.mem_rho, ← Logic.sigma_logicInt];
  exact h

/-- `𝐆𝐫𝐳` is a modal companion of `𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem logicInt_isModalCompanion_logicGrz : 𝐈𝐧𝐭.IsModalCompanion (α := α) 𝐆𝐫𝐳 :=
  fun A => (Iff.of_eq (congrArg (A ∈ ·) NormalLogic.rho_logicGrz.symm)).trans NormalLogic.mem_rho

end Propositional

end
