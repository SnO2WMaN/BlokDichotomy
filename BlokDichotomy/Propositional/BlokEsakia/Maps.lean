module

public import BlokDichotomy.Propositional.ModalCompanion

/-!
# The maps `ρ`, `σ` and `τ`

The superintuitionistic fragment `ρ L'` of a normal extension `L'` of `𝐒𝟒`, and the least normal
extensions `σ L = 𝐆𝐫𝐳 ⊕ Lᵍ` and `τ L = 𝐒𝟒 ⊕ Lᵍ` of `𝐆𝐫𝐳` and `𝐒𝟒` containing the Gödel
translations of a superintuitionistic logic `L`.

## References

- [CZ98, §9.6]
-/

@[expose] public section

universe v

namespace Propositional

variable {α : Type v} {L L' : NormalLogic α} {A B : Formula α}

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

/-- `ρ L'`, the superintuitionistic fragment of a normal extension `L'` of `𝐒𝟒`: the formulas
whose Gödel translation lies in `L'`.
- [CZ98, §9.6] -/
def _root_.NormalLogic.rho (L' : NormalLogic α) [L'.IsNExt 𝐒𝟒] : Logic α where
  carrier := {A | Aᵍ ∈ L'}
  mdp hA hAB := NormalLogic.mem_mdp hA <| NormalLogic.mem_mdp hAB NormalLogic.axiomT
  subst {A s} hA :=
    (NormalLogic.mem_iff_of_iff (gödelTranslate_subst A s)).mpr <| NormalLogic.mem_subst hA

section

variable [L'.IsNExt 𝐒𝟒]

@[simp] lemma _root_.NormalLogic.mem_rho : A ∈ L'.rho ↔ Aᵍ ∈ L' := Iff.rfl

instance : L'.rho.IsExt 𝐈𝐧𝐭 :=
  ⟨fun _ hA => NormalLogic.IsNExt.logic_le <| gödelTranslate_mem_logicS4_iff.mp hA⟩

end

lemma _root_.NormalLogic.rho_mono [L.IsNExt 𝐒𝟒] [L'.IsNExt 𝐒𝟒] (h : L ≤ L') : L.rho ≤ L'.rho :=
  fun _ hA => h hA

namespace Logic

variable {L L₁ L₂ : Logic α}

/-- `σ L = 𝐆𝐫𝐳 ⊕ Lᵍ`, the least normal extension of `𝐆𝐫𝐳` containing the Gödel translations
of the formulas of `L`.
- [CZ98, §9.6] -/
def sigma (L : Logic α) : NormalLogic α :=
  (𝐆𝐫𝐳 : NormalLogic α) + Formula.gödelTranslate '' (L : Set (Formula α))

/-- `τ L = 𝐒𝟒 ⊕ Lᵍ`, the least normal extension of `𝐒𝟒` containing the Gödel translations of
the formulas of `L`.
- [CZ98, §9.6] -/
def tau (L : Logic α) : NormalLogic α :=
  (𝐒𝟒 : NormalLogic α) + Formula.gödelTranslate '' (L : Set (Formula α))

instance : L.sigma.IsNExt 𝐆𝐫𝐳 := ⟨NormalLogic.le_add⟩

instance : L.tau.IsNExt 𝐒𝟒 := ⟨NormalLogic.le_add⟩

lemma gödelTranslate_mem_sigma (h : A ∈ L) : Aᵍ ∈ L.sigma := NormalLogic.mem_add ⟨A, h, rfl⟩

lemma gödelTranslate_mem_tau (h : A ∈ L) : Aᵍ ∈ L.tau := NormalLogic.mem_add ⟨A, h, rfl⟩

lemma tau_le_sigma : L.tau ≤ L.sigma :=
  NormalLogic.add_mono NormalLogic.logicS4_le_logicGrz subset_rfl

lemma sigma_mono (h : L₁ ≤ L₂) : L₁.sigma ≤ L₂.sigma :=
  NormalLogic.add_mono le_rfl <| Set.image_mono h

lemma le_rho_sigma : L ≤ L.sigma.rho := fun _ hA => gödelTranslate_mem_sigma hA

lemma le_rho_tau : L ≤ L.tau.rho := fun _ hA => gödelTranslate_mem_tau hA

lemma sigma_le [L'.IsNExt 𝐆𝐫𝐳] (h : L ≤ L'.rho) : L.sigma ≤ L' :=
  NormalLogic.add_le NormalLogic.IsNExt.logic_le <| by
    rintro _ ⟨A, hA, rfl⟩;
    exact h hA;

lemma tau_le [L'.IsNExt 𝐒𝟒] (h : L ≤ L'.rho) : L.tau ≤ L' :=
  NormalLogic.add_le NormalLogic.IsNExt.logic_le <| by
    rintro _ ⟨A, hA, rfl⟩;
    exact h hA;

end Logic

end Propositional

end
