module

public import BlokDichotomy.GeneralFrame.Canonical
public import BlokDichotomy.Propositional.BlokEsakia.Injective
public import BlokDichotomy.Propositional.BlokEsakia.MainLemma
public import BlokDichotomy.Propositional.BlokEsakia.NormalForm
public import BlokDichotomy.ToMathlib.Data.Fintype.EquivFin

/-!
# Surjectivity of `σ`

Every normal extension `L₁` of `𝐆𝐫𝐳` over an infinite set of variables is `σ ρ L₁`. The proof
refutes a formula `A ∉ L₁` by a substitution instance of `A` whose variables are replaced by
`◇`-free combinations of boxed formulas, using the main lemma on the canonical general frame, and
then transports this instance back to a formula over variables standing for the boxed formulas.

## References

- [CZ98, Theorem 9.66]
- [BC22, Theorem 4.2]
-/

@[expose] public section

universe v

namespace Propositional

variable {α : Type v}

/-- The admissible sets of `σ ρ` of the canonical general frame of an extension of `𝐒𝟒` are the
truth sets of the `◇`-free combinations of boxed formulas. -/
lemma exists_of_mem_toIntuitionistic_toModal_adm {L₂ : NormalLogic α} [L₂.IsNExt 𝐒𝟒]
    {X : Set L₂.MaximalConsistentSet}
    (hX : X ∈ L₂.canonicalGeneralFrame.toIntuitionistic.toModal.Adm) :
    ∃ β : _root_.Formula (_root_.Formula α), β.depth = 0 ∧ X = {x | β⟦(□·)⟧ ∈ x} := by
  have hX' : X ∈ BooleanSubalgebra.closure L₂.canonicalGeneralFrame.toIntuitionistic.Adm := hX
  clear hX
  induction hX' using BooleanSubalgebra.closure_bot_sup_induction with
  | mem Y hY =>
    obtain ⟨B, rfl⟩ := NormalLogic.canonicalGeneralFrame.mem_upAdm_iff.mp hY;
    exact ⟨#B, rfl, rfl⟩;
  | bot =>
    refine ⟨⊥, rfl, ?_⟩;
    ext x;
    simp [x.bot_not_mem];
  | sup Y _ Z _ ihY ihZ =>
    obtain ⟨β₁, h₁, rfl⟩ := ihY;
    obtain ⟨β₂, h₂, rfl⟩ := ihZ;
    use β₁ ⋎ β₂;
    and_intros;
    · simp [h₁, h₂];
    · ext x;
      simp [x.or_mem_iff];
  | compl Y _ ih =>
    obtain ⟨β, h, rfl⟩ := ih;
    use ∼β;
    and_intros;
    · simpa using h;
    · ext x;
      simp [x.neg_mem_iff];

/-- A formula outside an extension of `𝐆𝐫𝐳` has a substitution instance outside it, obtained by
substituting `◇`-free combinations of boxed formulas. -/
theorem exists_subst_not_mem [Nonempty α] (L₂ : NormalLogic α) [L₂.IsNExt 𝐆𝐫𝐳]
    {A : _root_.Formula α} (h : A ∉ L₂) :
    ∃ (s : _root_.Formula.Substitution α α) (β : α → _root_.Formula (_root_.Formula α)),
      (∀ p, (β p).depth = 0 ∧ s p = (β p)⟦(□·)⟧) ∧ A⟦s⟧ ∉ L₂ := by
  have hGrz : L₂.canonicalGeneralFrame ⊧ (𝐆𝐫𝐳 : NormalLogic α) := fun B hB =>
    NormalLogic.canonicalGeneralFrame.validates_iff.mpr (NormalLogic.IsNExt.logic_le hB);
  have hA : L₂.canonicalGeneralFrame ⊭ A := fun h₀ =>
    h (NormalLogic.canonicalGeneralFrame.validates_iff.mp h₀);
  have h₁ := GeneralFrame.not_validates_toIntuitionistic_toModal_of_not_validates hGrz hA;
  obtain ⟨V, hV, x, hx⟩ : ∃ V, L₂.canonicalGeneralFrame.toIntuitionistic.toModal.IsAdmissible V ∧
      ∃ x, ¬ x ⊩[L₂.canonicalGeneralFrame.toIntuitionistic.toModal.model V] A := by
    by_contra h₂;
    push Not at h₂;
    exact h₁ fun V hV x => h₂ V hV x;
  choose β hβ using fun p => exists_of_mem_toIntuitionistic_toModal_adm (hV p);
  use fun p => (β p)⟦(□·)⟧, β;
  and_intros;
  · exact fun p => ⟨(hβ p).1, rfl⟩;
  · intro hmem;
    have h₂ : V = fun w p => w ⊩[L₂.canonicalModel] (β p)⟦(□·)⟧ := by
      funext w p;
      apply propext;
      have h₃ := congrArg (w ∈ ·) (hβ p).2;
      simpa [NormalLogic.canonicalModel.truthlemma] using h₃;
    apply hx;
    have h₄ := NormalLogic.canonicalModel_validates_of_mem hmem x;
    have h₅ := (_root_.Model.World.forces_subst (fun p => (β p)⟦(□·)⟧)).mp h₄;
    subst h₂;
    exact h₅

/-- - [CZ98, Theorem 9.66]
- [BC22, Theorem 4.2] -/
theorem sigma_rho_eq [Infinite α] (L₁ : NormalLogic α) [L₁.IsNExt 𝐆𝐫𝐳] : L₁.rho.sigma = L₁ := by
  classical
  apply le_antisymm (Logic.sigma_le le_rfl);
  intro A hA;
  by_contra hA₂;
  obtain ⟨s, β, hβ, hs⟩ := exists_subst_not_mem L₁.rho.sigma hA₂;
  let t : Finset (_root_.Formula α) := A.atoms.biUnion fun p => (β p).atoms;
  obtain ⟨f, hf⟩ := Infinite.exists_injOn (α := α) t;
  let g : α → _root_.Formula α := Function.invFunOn f t;
  have hg : ∀ B ∈ t, g (f B) = B := fun B hB => hf.leftInvOn_invFunOn hB;
  let E : _root_.Formula α := A⟦fun p => (β p).map f⟧;
  have h₁ : E⟦fun q => □(#q)⟧ ∈ L₁ := NormalLogic.mem_subst <| NormalLogic.mem_subst hA;
  obtain ⟨γ, hγ, hiff⟩ := exists_subst_box_iff_gödelTranslate E;
  have h₂ : γ⟦(·ᵍ)⟧ ∈ L₁ :=
    (NormalLogic.mem_iff_of_iff (NormalLogic.mem_of_mem_logicK hiff)).mp h₁;
  have h₃ : γ⟦(·ᵍ)⟧ ∈ L₁.rho.sigma :=
    Logic.tau_le_sigma <| subst_gödelTranslate_mem_tau_rho γ hγ h₂;
  have h₄ : E⟦fun q => □(#q)⟧ ∈ L₁.rho.sigma :=
    (NormalLogic.mem_iff_of_iff (NormalLogic.mem_of_mem_logicK hiff)).mpr h₃;
  have h₅ := NormalLogic.mem_subst (s := g) h₄;
  have h₆ : (E⟦fun q => □(#q)⟧)⟦g⟧ = A⟦s⟧ := by
    simp only [E, _root_.Formula.subst_subst];
    apply Formula.subst_congr_of_atoms;
    intro p hp;
    rw [(hβ p).2, _root_.Formula.subst_map];
    apply Formula.subst_congr_of_atoms;
    intro B hB;
    have hB' : B ∈ t := Finset.mem_biUnion.mpr ⟨p, hp, hB⟩;
    simp [hg B hB'];
  exact hs (h₆ ▸ h₅)

end Propositional

end
