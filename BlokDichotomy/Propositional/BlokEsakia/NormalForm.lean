module

public import BlokDichotomy.Logic.CNF
public import BlokDichotomy.Propositional.BlokEsakia.Maps

/-!
# Normal forms of boxed substitution instances

Every formula with each variable replaced by a boxed variable is equivalent in `𝐊` to a
`◇`-free combination of Gödel translations of intuitionistic formulas. A `◇`-free combination of
translations that belongs to a normal extension `L₁` of `𝐒𝟒` belongs to `τ ρ L₁`.

## References

- [CZ98, §9.6]
-/

@[expose] public section

universe v

namespace Propositional

variable {α : Type v}

section

variable {L : NormalLogic α} [L.IsNExt 𝐊]

lemma gödelTranslate_conj (l : List (Formula α)) :
    (Formula.conj l)ᵍ 🡘 ⋀ (l.map (·ᵍ)) ∈ L := by
  induction l with
  | nil =>
    exact NormalLogic.iff_of_imp (NormalLogic.imp_of_mem NormalLogic.verum_mem)
      (NormalLogic.imp_of_mem NormalLogic.box_top);
  | cons A l ih =>
    simpa [Formula.conj] using NormalLogic.and_iff_congr NormalLogic.iff_refl ih;

lemma gödelTranslate_disj (l : List (Formula α)) :
    (Formula.disj l)ᵍ 🡘 ⋁ (l.map (·ᵍ)) ∈ L := by
  induction l with
  | nil => exact NormalLogic.iff_refl;
  | cons A l ih =>
    simpa [Formula.disj] using NormalLogic.or_iff_congr NormalLogic.iff_refl ih;

/-- A clause of the conjunctive normal form over translations is the translation of an
implication, up to a box. -/
lemma box_clause_iff (I J : List (Formula α)) :
    □(⋀ (I.map (·ᵍ)) 🡒 ⋁ (J.map (·ᵍ))) 🡘 (Formula.conj I 🡒 Formula.disj J)ᵍ ∈ L := by
  rw [Formula.gödelTranslate_imp];
  exact NormalLogic.box_congr <| NormalLogic.imp_iff_congr
    (NormalLogic.iff_symm (gödelTranslate_conj I)) (NormalLogic.iff_symm (gödelTranslate_disj J));

end

/-- Boxing a `◇`-free combination of translations gives again such a combination. -/
theorem exists_box_subst_gödelTranslate_iff (γ : _root_.Formula (Formula α)) (hγ : γ.depth = 0) :
    ∃ γ' : _root_.Formula (Formula α), γ'.depth = 0 ∧
      □(γ⟦(·ᵍ)⟧) 🡘 γ'⟦(·ᵍ)⟧ ∈ (𝐊 : NormalLogic α) := by
  classical
  let s := γ.atoms
  let c : Finset (Formula α) → Formula α := fun I =>
    Formula.conj I.toList 🡒 Formula.disj (s \ I).toList
  use ⋀ ((Formula.refutingSets s γ).toList.map fun I => #(c I));
  and_intros;
  · apply Formula.depth_conj_eq_zero;
    intro B hB;
    obtain ⟨I, -, rfl⟩ := List.mem_map.mp hB;
    rfl;
  · have h₁ := NormalLogic.box_congr <| Formula.cnf_iff_mem (L := (𝐊 : NormalLogic α)) hγ
      (subset_refl s) (·ᵍ);
    rw [Formula.subst_cnf] at h₁;
    have h₂ := NormalLogic.box_conj (L := (𝐊 : NormalLogic α))
      (l := (Formula.refutingSets s γ).toList.map
        fun I => ⋀ (I.toList.map (·ᵍ)) 🡒 ⋁ ((s \ I).toList.map (·ᵍ)));
    have h₃ := NormalLogic.conj_map_iff_congr (L := (𝐊 : NormalLogic α))
      (l := (Formula.refutingSets s γ).toList)
      (f := fun I => □(⋀ (I.toList.map (·ᵍ)) 🡒 ⋁ ((s \ I).toList.map (·ᵍ))))
      (g := fun I => (c I)ᵍ) fun I _ => box_clause_iff I.toList (s \ I).toList;
    simp only [List.map_map, Function.comp_def] at h₂;
    have h₄ := NormalLogic.iff_trans h₁ <| NormalLogic.iff_trans h₂ h₃;
    simpa [List.map_map, Function.comp_def] using h₄;

/-- Every formula whose variables are replaced by boxed variables is equivalent in `𝐊` to a
`◇`-free combination of translations. -/
theorem exists_subst_box_iff_gödelTranslate (E : _root_.Formula α) :
    ∃ γ : _root_.Formula (Formula α), γ.depth = 0 ∧
      E⟦fun q => □(#q)⟧ 🡘 γ⟦(·ᵍ)⟧ ∈ (𝐊 : NormalLogic α) := by
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
      have h₄ : ∼□(∼(γ₁⟦(·ᵍ)⟧)) 🡘 ∼(γ₂⟦(·ᵍ)⟧) ∈ (𝐊 : NormalLogic α) :=
        NormalLogic.neg_iff_congr i₂;
      exact NormalLogic.iff_trans h₃ h₄;

/-- A `◇`-free combination of translations in `L₁` is in `τ ρ L₁`. -/
theorem subst_gödelTranslate_mem_tau_rho {L₁ : NormalLogic α} [L₁.IsNExt 𝐒𝟒]
    (γ : _root_.Formula (Formula α)) (hγ : γ.depth = 0) (h : γ⟦(·ᵍ)⟧ ∈ L₁) :
    γ⟦(·ᵍ)⟧ ∈ L₁.rho.tau := by
  classical
  let s := γ.atoms
  have h₁ := Formula.cnf_iff_mem (L := L₁) hγ (subset_refl s) (·ᵍ)
  have h₂ := (NormalLogic.mem_iff_of_iff h₁).mp h
  rw [Formula.subst_cnf, NormalLogic.conj_mem_iff] at h₂
  have h₃ : (γ.cnf s)⟦(·ᵍ)⟧ ∈ L₁.rho.tau := by
    rw [Formula.subst_cnf, NormalLogic.conj_mem_iff];
    intro C hC;
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hC;
    have h₄ := h₂ _ hC;
    have h₅ : (Formula.conj I.toList 🡒 Formula.disj (s \ I).toList)ᵍ ∈ L₁ :=
      (NormalLogic.mem_iff_of_iff (box_clause_iff I.toList (s \ I).toList)).mp
        (NormalLogic.mem_nec h₄);
    have h₆ := Logic.gödelTranslate_mem_tau (L := L₁.rho) (A := Formula.conj I.toList 🡒
      Formula.disj (s \ I).toList) h₅;
    exact NormalLogic.mem_mdp
      ((NormalLogic.mem_iff_of_iff (box_clause_iff I.toList (s \ I).toList)).mpr h₆)
      NormalLogic.axiomT;
  exact (NormalLogic.mem_iff_of_iff (Formula.cnf_iff_mem hγ (subset_refl s) (·ᵍ))).mpr h₃

end Propositional

end
