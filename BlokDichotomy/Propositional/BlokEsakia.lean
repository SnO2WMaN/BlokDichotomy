module

public import BlokDichotomy.GeneralFrame.Canonical
public import BlokDichotomy.Logic.CNF
public import BlokDichotomy.Propositional.BlokEsakia.Basic
public import BlokDichotomy.Propositional.BlokEsakia.MainLemma
public import BlokDichotomy.ToMathlib.Data.Fintype.EquivFin

/-!
# The Blok–Esakia theorem

The map `L ↦ 𝐆𝐫𝐳 ⊕ Lᵍ` is an order isomorphism `beIsomorphism` from the superintuitionistic logics
onto the normal extensions of `𝐆𝐫𝐳`, over infinitely many variables, with inverse
`L ↦ L.siFragment`. In particular `𝐈𝐧𝐭.greatestMC = 𝐆𝐫𝐳`, `𝐈𝐧𝐭.leastMC = 𝐒𝟒`, and
`𝐒𝟒.siFragment = 𝐆𝐫𝐳.siFragment = 𝐈𝐧𝐭`.

The file also contains the normal forms of boxed substitution instances (every formula with each
variable replaced by a boxed variable is equivalent in `𝐊` to a `◇`-free combination of Gödel
translations of intuitionistic formulas) and the surjectivity of `greatestMC`: every normal
extension `L` of `𝐆𝐫𝐳` over infinitely many variables is `L.siFragment.greatestMC`.

## References

- [Blo76]
- [Esa76]
- [CZ98, §9.6]
- [CZ98, Theorem 9.66]
- [BC22, Theorem 4.2]
-/

@[expose] public section

universe v

namespace Propositional

variable {α : Type v}

section

variable {L : NormalLogic α} [L.IsNExt 𝐊]

lemma gödelTranslate_conj (l : List (Formula α)) :
    (Formula.conj l)ᵍ 🡘 ⋀ (l.map (·ᵍ)) ∈ L := by
  induction l using List.induction_with_singleton with
  | nil =>
    exact NormalLogic.iff_of_imp (NormalLogic.imp_of_mem NormalLogic.verum_mem)
      (NormalLogic.imp_of_mem NormalLogic.box_top);
  | singleton => exact NormalLogic.iff_refl;
  | cons A l hl ih =>
    rw [Formula.conj_cons_of_ne_nil hl, List.map_cons, _root_.Formula.conj_cons_of_ne_nil
      (by simpa using hl), Formula.gödelTranslate_and];
    exact NormalLogic.and_iff_congr NormalLogic.iff_refl ih;

lemma gödelTranslate_disj (l : List (Formula α)) :
    (Formula.disj l)ᵍ 🡘 ⋁ (l.map (·ᵍ)) ∈ L := by
  induction l using List.induction_with_singleton with
  | nil => exact NormalLogic.iff_refl;
  | singleton => exact NormalLogic.iff_refl;
  | cons A l hl ih =>
    rw [Formula.disj_cons_of_ne_nil hl, List.map_cons, _root_.Formula.disj_cons_of_ne_nil
      (by simpa using hl), Formula.gödelTranslate_or];
    exact NormalLogic.or_iff_congr NormalLogic.iff_refl ih;

/-- A clause of the conjunctive normal form over translations is the translation of an
implication, up to a box. -/
lemma box_clause_iff (I J : List (Formula α)) :
    □(⋀ (I.map (·ᵍ)) 🡒 ⋁ (J.map (·ᵍ))) 🡘 (Formula.conj I 🡒 Formula.disj J)ᵍ ∈ L := by
  rw [Formula.gödelTranslate_imp];
  exact NormalLogic.box_congr <| NormalLogic.imp_iff_congr
    (NormalLogic.iff_symm (gödelTranslate_conj I)) (NormalLogic.iff_symm (gödelTranslate_disj J));

end

/-- The box of a `◇`-free combination of translations is the conjunction of the translations of
the clauses of its conjunctive normal form. -/
private lemma box_subst_gödelTranslate_iff_conj [DecidableEq (Formula α)]
    {γ : _root_.Formula (Formula α)} (hγ : γ.depth = 0) {s : Finset (Formula α)}
    (hs : γ.atoms ⊆ s) :
    □(γ⟦(·ᵍ)⟧) 🡘 ⋀ ((Formula.refutingSets s γ).toList.map fun I =>
      (Formula.conj I.toList 🡒 Formula.disj (s \ I).toList)ᵍ) ∈ 𝐊 := by
  have h₁ := NormalLogic.box_congr <| Formula.cnf_iff_mem (L := 𝐊) hγ hs (·ᵍ);
  rw [Formula.subst_cnf] at h₁;
  have h₂ := NormalLogic.box_conj (L := 𝐊)
    (l := (Formula.refutingSets s γ).toList.map
      fun I => ⋀ (I.toList.map (·ᵍ)) 🡒 ⋁ ((s \ I).toList.map (·ᵍ)));
  have h₃ := NormalLogic.conj_map_iff_congr (L := 𝐊)
    (l := (Formula.refutingSets s γ).toList)
    (f := fun I => □(⋀ (I.toList.map (·ᵍ)) 🡒 ⋁ ((s \ I).toList.map (·ᵍ))))
    (g := fun I => (Formula.conj I.toList 🡒 Formula.disj (s \ I).toList)ᵍ)
    fun I _ => box_clause_iff I.toList (s \ I).toList;
  simp only [List.map_map, Function.comp_def] at h₂;
  exact NormalLogic.iff_trans h₁ <| NormalLogic.iff_trans h₂ h₃

/-- Boxing a `◇`-free combination of translations gives again such a combination. -/
theorem exists_box_subst_gödelTranslate_iff (γ : _root_.Formula (Formula α)) (hγ : γ.depth = 0) :
    ∃ δ : _root_.Formula (Formula α), δ.depth = 0 ∧
      □(γ⟦(·ᵍ)⟧) 🡘 δ⟦(·ᵍ)⟧ ∈ 𝐊 := by
  classical
  use ⋀ ((Formula.refutingSets γ.atoms γ).toList.map fun I =>
    #(Formula.conj I.toList 🡒 Formula.disj (γ.atoms \ I).toList));
  and_intros;
  · apply Formula.depth_conj_eq_zero;
    intro B hB;
    obtain ⟨I, -, rfl⟩ := List.mem_map.mp hB;
    rfl;
  · simpa [List.map_map, Function.comp_def] using
      box_subst_gödelTranslate_iff_conj hγ (subset_refl γ.atoms)

/-- Every formula whose variables are replaced by boxed variables is equivalent in `𝐊` to a
`◇`-free combination of translations. -/
theorem exists_subst_box_iff_gödelTranslate (E : _root_.Formula α) :
    ∃ γ : _root_.Formula (Formula α), γ.depth = 0 ∧
      E⟦fun q => □(#q)⟧ 🡘 γ⟦(·ᵍ)⟧ ∈ 𝐊 := by
  induction E with
  | atom q => exact ⟨#(#q), rfl, NormalLogic.iff_refl⟩;
  | falsum => exact ⟨⊥, rfl, NormalLogic.iff_refl⟩;
  | imp E₁ E₂ ih₁ ih₂ =>
    obtain ⟨γ₁, h₁, i₁⟩ := ih₁;
    obtain ⟨γ₂, h₂, i₂⟩ := ih₂;
    use γ₁ 🡒 γ₂;
    and_intros;
    · simp [h₁, h₂];
    · simpa using NormalLogic.imp_iff_congr i₁ i₂;
  | dia E₁ ih =>
    obtain ⟨γ₁, h₁, i₁⟩ := ih;
    obtain ⟨γ₂, h₂, i₂⟩ := exists_box_subst_gödelTranslate_iff (∼γ₁) (by simpa using h₁);
    use ∼γ₂;
    and_intros;
    · simp [h₂];
    · have h₃ := NormalLogic.iff_trans (NormalLogic.dia_congr i₁) NormalLogic.diaDual;
      have h₄ : ∼□(∼(γ₁⟦(·ᵍ)⟧)) 🡘 ∼(γ₂⟦(·ᵍ)⟧) ∈ 𝐊 :=
        NormalLogic.neg_iff_congr i₂;
      exact NormalLogic.iff_trans h₃ h₄;

/-- A `◇`-free combination of translations in `L₁` is in `L₁.siFragment.leastMC`. -/
theorem subst_gödelTranslate_mem_leastMC_siFragment {L₁ : NormalLogic α} [L₁.IsNExt 𝐒𝟒]
    (γ : _root_.Formula (Formula α)) (hγ : γ.depth = 0) (h : γ⟦(·ᵍ)⟧ ∈ L₁) :
    γ⟦(·ᵍ)⟧ ∈ L₁.siFragment.leastMC := by
  classical
  let s := γ.atoms;
  have h₁ := Formula.cnf_iff_mem (L := L₁) hγ (subset_refl s) (·ᵍ);
  have h₂ := (NormalLogic.mem_iff_of_iff h₁).mp h;
  rw [Formula.subst_cnf, NormalLogic.conj_mem_iff] at h₂;
  have h₃ : (γ.cnf s)⟦(·ᵍ)⟧ ∈ L₁.siFragment.leastMC := by
    rw [Formula.subst_cnf, NormalLogic.conj_mem_iff];
    intro C hC;
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hC;
    have h₄ := h₂ _ hC;
    have h₅ : (Formula.conj I.toList 🡒 Formula.disj (s \ I).toList)ᵍ ∈ L₁ :=
      (NormalLogic.mem_iff_of_iff (box_clause_iff I.toList (s \ I).toList)).mp
        (NormalLogic.mem_nec h₄);
    have h₆ := Logic.gödelTranslate_mem_leastMC (L := L₁.siFragment) (A := Formula.conj I.toList 🡒
      Formula.disj (s \ I).toList) h₅;
    exact NormalLogic.mem_mdp
      ((NormalLogic.mem_iff_of_iff (box_clause_iff I.toList (s \ I).toList)).mpr h₆)
      NormalLogic.axiomT;
  exact (NormalLogic.mem_iff_of_iff
    (Formula.cnf_iff_mem (L := L₁.siFragment.leastMC) hγ (subset_refl s) (·ᵍ))).mpr h₃

/-- A substitution instance by boxed variables that lies in an extension `L₁` of `𝐒𝟒` lies in
`L₁.siFragment.greatestMC`. -/
theorem subst_box_mem_greatestMC_siFragment {L₁ : NormalLogic α} [L₁.IsNExt 𝐒𝟒]
    (E : _root_.Formula α) (h : E⟦fun q => □(#q)⟧ ∈ L₁) :
    E⟦fun q => □(#q)⟧ ∈ L₁.siFragment.greatestMC := by
  obtain ⟨γ, hγ, hiff⟩ := exists_subst_box_iff_gödelTranslate E;
  have h₁ : γ⟦(·ᵍ)⟧ ∈ L₁ :=
    (NormalLogic.mem_iff_of_iff (NormalLogic.mem_of_mem_logicK hiff)).mp h;
  have h₂ : γ⟦(·ᵍ)⟧ ∈ L₁.siFragment.greatestMC :=
    Logic.leastMC_le_greatestMC <| subst_gödelTranslate_mem_leastMC_siFragment γ hγ h₁;
  exact (NormalLogic.mem_iff_of_iff (NormalLogic.mem_of_mem_logicK hiff)).mpr h₂


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
  have hGrz : L₂.canonicalGeneralFrame ⊧ logicGrz (α := α) := fun B hB =>
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


/-- The Blok–Esakia isomorphism between the superintuitionistic logics and the normal extensions
of `𝐆𝐫𝐳`, `L ↦ 𝐆𝐫𝐳 ⊕ Lᵍ`, with inverse `L ↦ {A | Aᵍ ∈ L}`.
- [Blo76]
- [Esa76]
- [CZ98, Theorem 9.66] -/
noncomputable def beIsomorphism (α : Type v) [Infinite α] :
    Ext (α := α) 𝐈𝐧𝐭 ≃o NExt (α := α) 𝐆𝐫𝐳 where
  toFun L := ⟨L.1.greatestMC, inferInstance⟩
  invFun L := ⟨L.1.siFragment, inferInstance⟩
  left_inv L := Subtype.ext (Logic.siFragment_greatestMC_eq L.1)
  right_inv L := Subtype.ext (greatestMC_siFragment_eq L.1)
  map_rel_iff' {L₁ L₂} := by
    constructor;
    · intro h;
      have h₁ := NormalLogic.siFragment_mono (L₁ := L₁.1.greatestMC) (L₂ := L₂.1.greatestMC) h;
      rwa [Logic.siFragment_greatestMC_eq, Logic.siFragment_greatestMC_eq] at h₁;
    · exact Logic.greatestMC_mono

@[simp] lemma beIsomorphism_apply [Infinite α] (L : Ext 𝐈𝐧𝐭) :
    (beIsomorphism α L).1 = L.1.greatestMC := rfl

@[simp] lemma beIsomorphism_symm_apply [Infinite α] (L : NExt 𝐆𝐫𝐳) :
    ((beIsomorphism α).symm L).1 = L.1.siFragment := rfl

namespace Logic

/-- `𝐈𝐧𝐭.leastMC = 𝐒𝟒`.
- [CZ98, §3.9, Example 9.63] -/
theorem leastMC_logicInt : 𝐈𝐧𝐭.leastMC (α := α) = 𝐒𝟒 :=
  le_antisymm (leastMC_le fun _ hA => gödelTranslate_mem_logicS4_iff.mp hA) NormalLogic.le_add

/-- `𝐈𝐧𝐭.greatestMC = 𝐆𝐫𝐳`.
- [CZ98, §3.9, Example 9.63] -/
theorem greatestMC_logicInt : 𝐈𝐧𝐭.greatestMC (α := α) = 𝐆𝐫𝐳 :=
  le_antisymm
    (greatestMC_le fun _ hA =>
      NormalLogic.logicS4_le_logicGrz (gödelTranslate_mem_logicS4_iff.mp hA))
    NormalLogic.le_add

end Logic

/-- `𝐒𝟒.siFragment = 𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem _root_.NormalLogic.siFragment_logicS4 : 𝐒𝟒.siFragment (α := α) = 𝐈𝐧𝐭 :=
  SetLike.ext fun _ => gödelTranslate_mem_logicS4_iff.symm

/-- `𝐆𝐫𝐳.siFragment = 𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem _root_.NormalLogic.siFragment_logicGrz : 𝐆𝐫𝐳.siFragment (α := α) = 𝐈𝐧𝐭 := by
  apply SetLike.ext;
  intro A;
  have h : Aᵍ ∈ 𝐈𝐧𝐭.greatestMC (α := α) ↔ A ∈ 𝐈𝐧𝐭 := by
    rw [← NormalLogic.mem_siFragment, Logic.siFragment_greatestMC_eq];
  rw [NormalLogic.mem_siFragment, ← Logic.greatestMC_logicInt];
  exact h

/-- `𝐆𝐫𝐳` is a modal companion of `𝐈𝐧𝐭`.
- [CZ98, §3.9, Example 9.63] -/
theorem logicGrz_isModalCompanionOf_logicInt : 𝐆𝐫𝐳.IsModalCompanionOf (α := α) 𝐈𝐧𝐭 :=
  fun A => (Iff.of_eq (congrArg (A ∈ ·) NormalLogic.siFragment_logicGrz.symm)).trans
    NormalLogic.mem_siFragment

end Propositional

end
