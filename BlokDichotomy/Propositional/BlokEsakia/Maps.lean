module

public import BlokDichotomy.Propositional.ModalCompanion

/-!
# The superintuitionistic fragment and the modal companions `leastMC` and `greatestMC`

The superintuitionistic fragment of a normal extension of `𝐒𝟒`, and the least normal extensions
`𝐒𝟒 ⊕ Lᵍ` and `𝐆𝐫𝐳 ⊕ Lᵍ` of `𝐒𝟒` and `𝐆𝐫𝐳` containing the Gödel translations of a
superintuitionistic logic `L`. They are the least and the greatest modal companion of `L`.

## References

- [CZ98, §9.6]
-/

@[expose] public section

universe v

namespace Propositional

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

/-- The translation of a substitution instance is the substitution instance of the translation,
for the substitution of translations, up to equivalence. -/
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
def _root_.NormalLogic.siFragment (L : NormalLogic α) [L.IsNExt 𝐒𝟒] : Logic α where
  carrier := {A | Aᵍ ∈ L}
  mdp hA hAB := NormalLogic.mem_mdp hA <| NormalLogic.mem_mdp hAB NormalLogic.axiomT
  subst {A s} hA :=
    (NormalLogic.mem_iff_of_iff (gödelTranslate_subst A s)).mpr <| NormalLogic.mem_subst hA

section

variable [L.IsNExt 𝐒𝟒]

@[simp] lemma _root_.NormalLogic.mem_siFragment : A ∈ L.siFragment ↔ Aᵍ ∈ L := Iff.rfl

instance : L.siFragment.IsExt 𝐈𝐧𝐭 :=
  ⟨fun _ hA => NormalLogic.IsNExt.logic_le <| gödelTranslate_mem_logicS4_iff.mp hA⟩

end

lemma _root_.NormalLogic.siFragment_mono {L₁ L₂ : NormalLogic α} [L₁.IsNExt 𝐒𝟒] [L₂.IsNExt 𝐒𝟒]
    (h : L₁ ≤ L₂) : L₁.siFragment ≤ L₂.siFragment :=
  fun _ hA => h hA

namespace Logic

variable {L L₁ L₂ : Logic α} {L' : NormalLogic α}

/-- `𝐆𝐫𝐳 ⊕ Lᵍ`, the least normal extension of `𝐆𝐫𝐳` containing the Gödel translations of the
formulas of `L`; it is written `σ L` in [CZ98, §9.6].

For `L ⊇ 𝐈𝐧𝐭` it is a modal companion of `L` (`isModalCompanion_greatestMC`). By Esakia's theorem
it is the greatest modal companion of `L`; that theorem is not formalized here.
- [CZ98, Corollary 9.64]
- [Esa76] -/
def greatestMC (L : Logic α) : NormalLogic α :=
  (𝐆𝐫𝐳 : NormalLogic α) + Formula.gödelTranslate '' (L : Set (Formula α))

/-- `𝐒𝟒 ⊕ Lᵍ`, the least normal extension of `𝐒𝟒` containing the Gödel translations of the
formulas of `L`; it is written `τ L` in [CZ98, §9.6].

For `L ⊇ 𝐈𝐧𝐭` it is the least modal companion of `L`: it is a modal companion
(`isModalCompanion_leastMC`) and is contained in every normal extension of `𝐒𝟒` whose
superintuitionistic fragment contains `L` (`leastMC_le`).
- [CZ98, §9.6] -/
def leastMC (L : Logic α) : NormalLogic α :=
  (𝐒𝟒 : NormalLogic α) + Formula.gödelTranslate '' (L : Set (Formula α))

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

end Logic

end Propositional

end
