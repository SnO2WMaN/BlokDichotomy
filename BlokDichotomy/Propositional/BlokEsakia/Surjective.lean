module

public import BlokDichotomy.GeneralFrame.Canonical
public import BlokDichotomy.Propositional.BlokEsakia.MainLemma
public import BlokDichotomy.Propositional.BlokEsakia.NormalForm
public import BlokDichotomy.ToMathlib.Data.Fintype.EquivFin

/-!
# Surjectivity of `greatestMC`

Every normal extension `L₁` of `𝐆𝐫𝐳` over an infinite set of variables is
`L₁.siFragment.greatestMC`. The proof refutes a formula `A ∉ L₁` by a substitution instance of `A`
whose variables are replaced by `◇`-free combinations of boxed formulas, using the main lemma on
the canonical general frame, and then transports this instance back to a formula over variables
standing for the boxed formulas.

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
  replace hX : X ∈ BooleanSubalgebra.closure L₂.canonicalGeneralFrame.toIntuitionistic.Adm := hX
  induction hX using BooleanSubalgebra.closure_bot_sup_induction with
  | mem Y hY =>
    obtain ⟨B, rfl⟩ := NormalLogic.canonicalGeneralFrame.mem_upAdm_iff.mp hY;
    exact ⟨#B, rfl, rfl⟩;
  | bot =>
    use ⊥;
    and_intros;
    · rfl;
    · ext x;
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
  have hA : L₂.canonicalGeneralFrame ⊭ A := by
    by_contra h₀;
    exact h (NormalLogic.canonicalGeneralFrame.validates_iff.mp h₀);
  obtain ⟨V, hV, x, hx⟩ := _root_.GeneralFrame.not_validates_iff.mp
    (_root_.GeneralFrame.not_validates_toIntuitionistic_toModal_of_not_validates hGrz hA);
  choose β hβ using fun p => exists_of_mem_toIntuitionistic_toModal_adm (hV p);
  use fun p => (β p)⟦(□·)⟧, β;
  and_intros;
  · intro p;
    exact ⟨(hβ p).1, rfl⟩;
  · by_contra hmem;
    have h₂ := NormalLogic.canonicalGeneralFrame.eq_forces_of_forall_setOf_eq fun p => (hβ p).2;
    have h₃ := NormalLogic.canonicalModel_validates_of_mem hmem x;
    have h₄ := (_root_.Model.World.forces_subst (fun p => (β p)⟦(□·)⟧)).mp h₃;
    subst h₂;
    exact hx h₄

/-- Substituting boxed formulas for the variables of `A`, and then the original formulas back
along a left inverse of the renaming, gives the original substitution instance. -/
private lemma subst_box_map_subst_eq [DecidableEq α] {A : _root_.Formula α}
    {β : α → _root_.Formula (_root_.Formula α)} {s : _root_.Formula.Substitution α α}
    (hs : ∀ p, s p = (β p)⟦(□·)⟧) {f : _root_.Formula α → α} {g : α → _root_.Formula α}
    (hg : ∀ p ∈ A.atoms, ∀ B ∈ (β p).atoms, g (f B) = B) :
    (A⟦fun p => (β p).map f⟧⟦fun q => □(#q)⟧)⟦g⟧ = A⟦s⟧ := by
  simp only [_root_.Formula.subst_subst];
  apply Formula.subst_congr_of_atoms;
  intro p hp;
  rw [hs p, _root_.Formula.subst_map];
  apply Formula.subst_congr_of_atoms;
  intro B hB;
  simp [hg p hp B hB]

/-- Every normal extension `L₁` of `𝐆𝐫𝐳` over infinitely many variables is
`L₁.siFragment.greatestMC`.
- [CZ98, Theorem 9.66]
- [BC22, Theorem 4.2] -/
theorem greatestMC_siFragment_eq [Infinite α] (L : NormalLogic α) [L.IsNExt 𝐆𝐫𝐳] :
    L.siFragment.greatestMC = L := by
  classical
  apply le_antisymm (Logic.greatestMC_le le_rfl);
  intro A hA;
  by_contra hA₂;
  obtain ⟨s, β, hβ, hs⟩ := exists_subst_not_mem L.siFragment.greatestMC hA₂;
  obtain ⟨f, hf⟩ := Infinite.exists_injOn (α := α) (A.atoms.biUnion fun p => (β p).atoms);
  obtain ⟨g, hg⟩ : ∃ g : α → _root_.Formula α, ∀ p ∈ A.atoms, ∀ B ∈ (β p).atoms, g (f B) = B := by
    use Function.invFunOn f (A.atoms.biUnion fun p => (β p).atoms);
    intro p hp B hB;
    exact hf.leftInvOn_invFunOn <| Finset.mem_coe.mpr <| Finset.mem_biUnion.mpr ⟨p, hp, hB⟩;
  have h₁ : (A⟦fun p => (β p).map f⟧)⟦fun q => □(#q)⟧ ∈ L :=
    NormalLogic.mem_subst <| NormalLogic.mem_subst hA;
  have h₂ := NormalLogic.mem_subst (s := g) <| subst_box_mem_greatestMC_siFragment _ h₁;
  rw [subst_box_map_subst_eq (fun p => (hβ p).2) hg] at h₂;
  exact hs h₂

end Propositional

end
