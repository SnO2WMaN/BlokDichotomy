module

public import BlokDichotomy.Propositional.GeneralFrame.Basic
public import BlokDichotomy.Propositional.GeneralFrame.Companion
public import BlokDichotomy.Propositional.ModalCompanion

/-!
# The superintuitionistic fragment and the modal companions `leastMC` and `greatestMC`

The superintuitionistic fragment `L.siFragment` of a normal extension `L` of `𝐒𝟒`, and the normal
extensions `𝐒𝟒 ⊕ Lᵍ` and `𝐆𝐫𝐳 ⊕ Lᵍ` of a superintuitionistic logic `L`. The superintuitionistic
fragments of both are `L`, so both are modal companions of `L`.

## References

- [CZ98, §9.6]
- [CZ98, Theorem 9.57]
-/

@[expose] public section

universe v

namespace Propositional

open Modal

variable {α : Type v} {L : NormalLogic α} {A B : Formula α}

section

variable [L.IsNExt 𝐒𝟒]

/-- Gödel translations are boxed in every extension of `𝐒𝟒`. -/
lemma gödelTranslate_iff_box (C : Formula α) : Cᵍ 🡘 □Cᵍ ∈ L := by
  induction C with
  | falsum => exact NormalLogic.iff_of_imp NormalLogic.efq NormalLogic.axiomT;
  | atom a => exact NormalLogic.iff_of_imp NormalLogic.axiomFour NormalLogic.axiomT;
  | and A B ihA ihB =>
    exact NormalLogic.iff_trans (NormalLogic.and_iff_congr ihA ihB)
      (NormalLogic.iff_symm NormalLogic.box_and);
  | or A B ihA ihB =>
    apply NormalLogic.iff_of_imp;
    · exact NormalLogic.mdp₂ NormalLogic.or_elim
        (NormalLogic.imp_trans (NormalLogic.iff_mp ihA)
          (NormalLogic.box_mono NormalLogic.or_left))
        (NormalLogic.imp_trans (NormalLogic.iff_mp ihB)
          (NormalLogic.box_mono NormalLogic.or_right));
    · exact NormalLogic.axiomT;
  | imp A B ihA ihB => exact NormalLogic.iff_of_imp NormalLogic.axiomFour NormalLogic.axiomT;

/-- The translation of `A⟦s⟧` is equivalent to `Aᵍ` under the substitution of the translations
of the images of `s`. -/
lemma gödelTranslate_subst (A : Formula α) (s : Formula.Substitution α α) :
    (A⟦s⟧)ᵍ 🡘 Aᵍ⟦fun a => (s a)ᵍ⟧ ∈ L := by
  induction A with
  | falsum => exact NormalLogic.iff_refl;
  | atom a => exact gödelTranslate_iff_box (s a);
  | and A B ihA ihB => exact NormalLogic.and_iff_congr ihA ihB;
  | or A B ihA ihB => exact NormalLogic.or_iff_congr ihA ihB;
  | imp A B ihA ihB => exact NormalLogic.box_congr (NormalLogic.imp_iff_congr ihA ihB);

end

/-- The superintuitionistic fragment of a normal extension `L` of `𝐒𝟒`: the formulas whose Gödel
translation lies in `L`. It is written `ρ L` in [CZ98, §9.6].
- [CZ98, §9.6] -/
def _root_.Modal.NormalLogic.siFragment (L : NormalLogic α) [L.IsNExt 𝐒𝟒] : Logic α where
  carrier := {A | Aᵍ ∈ L}
  mdp hA hAB := NormalLogic.mem_mdp hA <| NormalLogic.mem_mdp hAB NormalLogic.axiomT
  subst {A s} hA :=
    (NormalLogic.mem_iff_of_iff (gödelTranslate_subst A s)).mpr <| NormalLogic.mem_subst hA

section

variable [L.IsNExt 𝐒𝟒]

@[simp] lemma _root_.Modal.NormalLogic.mem_siFragment : A ∈ L.siFragment ↔ Aᵍ ∈ L := Iff.rfl

instance : L.siFragment.IsExt 𝐈𝐧𝐭 :=
  ⟨fun _ hA => NormalLogic.IsNExt.logic_le <| gödelTranslate_mem_logicS4_iff.mp hA⟩

end

lemma _root_.Modal.NormalLogic.siFragment_mono {L₁ L₂ : NormalLogic α} [L₁.IsNExt 𝐒𝟒] [L₂.IsNExt 𝐒𝟒]
    (h : L₁ ≤ L₂) : L₁.siFragment ≤ L₂.siFragment :=
  fun _ hA => h hA

namespace Logic

variable {L L₁ L₂ : Logic α} {L' : NormalLogic α}

/-- `𝐆𝐫𝐳 ⊕ Lᵍ`, the least normal extension of `𝐆𝐫𝐳` containing the Gödel translations of the
formulas of `L`; it is written `σ L` in [CZ98, §9.6]. For `L ⊇ 𝐈𝐧𝐭` it is the greatest modal
companion of `L` by Esakia's theorem.
- [CZ98, Corollary 9.64]
- [Esa76] -/
def greatestMC (L : Logic α) : NormalLogic α :=
  𝐆𝐫𝐳 + Formula.gödelTranslate '' L

/-- `𝐒𝟒 ⊕ Lᵍ`, the least normal extension of `𝐒𝟒` containing the Gödel translations of the
formulas of `L`; it is written `τ L` in [CZ98, §9.6]. For `L ⊇ 𝐈𝐧𝐭` it is the least modal companion
of `L`.
- [CZ98, §9.6] -/
def leastMC (L : Logic α) : NormalLogic α :=
  𝐒𝟒 + Formula.gödelTranslate '' L

instance : L.greatestMC.IsNExt 𝐆𝐫𝐳 := ⟨NormalLogic.le_add⟩

instance : L.leastMC.IsNExt 𝐒𝟒 := ⟨NormalLogic.le_add⟩

lemma gödelTranslate_mem_greatestMC (h : A ∈ L) : Aᵍ ∈ L.greatestMC :=
  NormalLogic.mem_add ⟨A, h, rfl⟩

lemma gödelTranslate_mem_leastMC (h : A ∈ L) : Aᵍ ∈ L.leastMC :=
  NormalLogic.mem_add ⟨A, h, rfl⟩

lemma leastMC_le_greatestMC : L.leastMC ≤ L.greatestMC :=
  NormalLogic.add_mono NormalLogic.logicS4_le_logicGrz subset_rfl

lemma greatestMC_mono (h : L₁ ≤ L₂) : L₁.greatestMC ≤ L₂.greatestMC :=
  NormalLogic.add_mono le_rfl <| Set.image_mono h

lemma le_siFragment_greatestMC : L ≤ L.greatestMC.siFragment :=
  fun _ hA => gödelTranslate_mem_greatestMC hA

lemma le_siFragment_leastMC : L ≤ L.leastMC.siFragment :=
  fun _ hA => gödelTranslate_mem_leastMC hA

/-- `L.greatestMC` is below every normal extension of `𝐆𝐫𝐳` whose superintuitionistic fragment
contains `L`. -/
lemma greatestMC_le [L'.IsNExt 𝐆𝐫𝐳] (h : L ≤ L'.siFragment) : L.greatestMC ≤ L' :=
  NormalLogic.add_le NormalLogic.IsNExt.logic_le <| by
    rintro _ ⟨A, hA, rfl⟩;
    exact h hA;

/-- `L.leastMC` is below every normal extension of `𝐒𝟒` whose superintuitionistic fragment contains
`L`. -/
lemma leastMC_le [L'.IsNExt 𝐒𝟒] (h : L ≤ L'.siFragment) : L.leastMC ≤ L' :=
  NormalLogic.add_le NormalLogic.IsNExt.logic_le <| by
    rintro _ ⟨A, hA, rfl⟩;
    exact h hA;

section

variable (L : Logic α) [L.IsExt 𝐈𝐧𝐭]

/-- The superintuitionistic fragment of `L.greatestMC` is `L`.
- [CZ98, Theorem 9.57] -/
theorem siFragment_greatestMC_eq : L.greatestMC.siFragment = L := by
  apply le_antisymm _ le_siFragment_greatestMC;
  intro A hA;
  by_contra hAL;
  have h₁ : L.canonicalGeneralFrame.toModal ⊧ L.greatestMC := by
    apply Modal.GeneralFrame.validatesLogic_add GeneralFrame.toModal_validates_logicGrz;
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
theorem leastMC_isModalCompanionOf : L.leastMC.IsModalCompanionOf L := by
  intro A;
  constructor;
  · exact gödelTranslate_mem_leastMC;
  · intro h;
    have h₁ : A ∈ L.leastMC.siFragment := h;
    rwa [siFragment_leastMC_eq] at h₁;

/-- `L.greatestMC` is a modal companion of `L`.
- [CZ98, Theorem 9.57] -/
theorem greatestMC_isModalCompanionOf : L.greatestMC.IsModalCompanionOf L := by
  intro A;
  constructor;
  · exact gödelTranslate_mem_greatestMC;
  · intro h;
    have h₁ : A ∈ L.greatestMC.siFragment := h;
    rwa [siFragment_greatestMC_eq] at h₁;

end

end Logic

end Propositional

end
