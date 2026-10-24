module

public import BlokDichotomy.Propositional.BlokEsakia.Injective
public import BlokDichotomy.Propositional.BlokEsakia.Surjective

/-!
# The Blok–Esakia theorem

The map `L ↦ 𝐆𝐫𝐳 ⊕ Lᵍ` is an order isomorphism from the superintuitionistic logics onto the
normal extensions of `𝐆𝐫𝐳`, with inverse `L ↦ L.siFragment`. In particular
`𝐈𝐧𝐭.greatestMC = 𝐆𝐫𝐳`, `𝐈𝐧𝐭.leastMC = 𝐒𝟒`, and `𝐒𝟒.siFragment = 𝐆𝐫𝐳.siFragment = 𝐈𝐧𝐭`.

## References

- [Blo76]
- [Esa76]
- [CZ98, Theorem 9.66]
-/

@[expose] public section

universe v

namespace Propositional

variable {α : Type v}

/-- The Blok–Esakia isomorphism between the superintuitionistic logics and the normal extensions
of `𝐆𝐫𝐳`, `L ↦ 𝐆𝐫𝐳 ⊕ Lᵍ`, with inverse `L ↦ {A | Aᵍ ∈ L}`.
- [Blo76]
- [Esa76]
- [CZ98, Theorem 9.66] -/
noncomputable def beIsomorphism (α : Type v) [Infinite α] :
    Ext (𝐈𝐧𝐭 : Logic α) ≃o NExt (𝐆𝐫𝐳 : NormalLogic α) where
  toFun L := ⟨L.1.greatestMC, inferInstance⟩
  invFun L := ⟨L.1.siFragment, inferInstance⟩
  left_inv L := Subtype.ext (Logic.siFragment_greatestMC_eq L.1)
  right_inv L := Subtype.ext (greatestMC_siFragment_eq L.1)
  map_rel_iff' {L₁ L₂} := by
    constructor;
    · intro h;
      have h₁ := NormalLogic.siFragment_mono (L := L₁.1.greatestMC) (L' := L₂.1.greatestMC) h;
      rwa [Logic.siFragment_greatestMC_eq, Logic.siFragment_greatestMC_eq] at h₁;
    · exact Logic.greatestMC_mono

@[simp] lemma beIsomorphism_apply [Infinite α] (L : Ext (𝐈𝐧𝐭 : Logic α)) :
    (beIsomorphism α L).1 = L.1.greatestMC := rfl

@[simp] lemma beIsomorphism_symm_apply [Infinite α] (L : NExt (𝐆𝐫𝐳 : NormalLogic α)) :
    ((beIsomorphism α).symm L).1 = L.1.siFragment := rfl

namespace Logic

/-- `𝐈𝐧𝐭.leastMC = 𝐒𝟒`.
- [CZ98, §3.9, Example 9.63] -/
theorem leastMC_logicInt : (𝐈𝐧𝐭 : Logic α).leastMC = 𝐒𝟒 :=
  le_antisymm (leastMC_le fun _ hA => gödelTranslate_mem_logicS4_iff.mp hA) NormalLogic.le_add

/-- `𝐈𝐧𝐭.greatestMC = 𝐆𝐫𝐳`.
- [CZ98, §3.9, Example 9.63] -/
theorem greatestMC_logicInt : (𝐈𝐧𝐭 : Logic α).greatestMC = 𝐆𝐫𝐳 :=
  le_antisymm
    (greatestMC_le fun _ hA =>
      NormalLogic.logicS4_le_logicGrz (gödelTranslate_mem_logicS4_iff.mp hA))
    NormalLogic.le_add

end Logic

/-- `𝐒𝟒.siFragment = 𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem _root_.NormalLogic.siFragment_logicS4 : (𝐒𝟒 : NormalLogic α).siFragment = 𝐈𝐧𝐭 :=
  SetLike.ext fun _ => gödelTranslate_mem_logicS4_iff.symm

/-- `𝐆𝐫𝐳.siFragment = 𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem _root_.NormalLogic.siFragment_logicGrz : (𝐆𝐫𝐳 : NormalLogic α).siFragment = 𝐈𝐧𝐭 := by
  apply SetLike.ext;
  intro A;
  have h : Aᵍ ∈ (𝐈𝐧𝐭 : Logic α).greatestMC ↔ A ∈ 𝐈𝐧𝐭 := by
    rw [← NormalLogic.mem_siFragment, Logic.siFragment_greatestMC_eq];
  rw [NormalLogic.mem_siFragment, ← Logic.greatestMC_logicInt];
  exact h

/-- `𝐆𝐫𝐳` is a modal companion of `𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem logicInt_isModalCompanion_logicGrz : 𝐈𝐧𝐭.IsModalCompanion (α := α) 𝐆𝐫𝐳 :=
  fun A => (Iff.of_eq (congrArg (A ∈ ·) NormalLogic.siFragment_logicGrz.symm)).trans
    NormalLogic.mem_siFragment

end Propositional

end
