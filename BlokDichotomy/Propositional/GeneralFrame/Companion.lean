module

public import BlokDichotomy.Propositional.GeneralFrame.Basic
public import BlokDichotomy.Propositional.ModalCompanion
public import BlokDichotomy.ToMathlib.Order.BooleanSubalgebra

/-!
# Modal and intuitionistic general frames

The intuitionistic general frame `ρ G` of the admissible upsets of a modal general frame `G` on a
preorder, the modal general frame `σ H` of the Boolean combinations of the admissible sets of an
intuitionistic general frame `H`, the skeleton lemmas relating validity of `Aᵍ` and `A`, and the
validity of `𝐆𝐫𝐳` in every `σ H`.

## References

- [CZ98, §8.3]
-/

@[expose] public section

universe u v

namespace Propositional

variable {κ : Type u} {α : Type v}

/-- `ρ G`: the intuitionistic general frame of the admissible upsets of a modal general frame on
a preorder.
- [CZ98, §8.3] -/
def _root_.GeneralFrame.toIntuitionistic (G : _root_.GeneralFrame κ) [IsPreorder κ G.Rel] :
    Propositional.GeneralFrame κ where
  toFrame := G.toFrame
  refl := Frame.rel_refl
  trans := Frame.rel_trans
  Adm := G.upAdm
  isUpset_of_mem h := h.2
  empty_mem := ⟨G.empty_mem, Frame.isUpset_empty⟩
  inter_mem hX hY := ⟨G.inter_mem hX.1 hY.1, hX.2.inter hY.2⟩
  union_mem hX hY := ⟨G.union_mem hX.1 hY.1, hX.2.union hY.2⟩
  himpSet_mem hX hY := _root_.GeneralFrame.himpSet_mem_upAdm hX.1 hY.1

namespace GeneralFrame

open BooleanSubalgebra

/-- `σ H`: the modal general frame whose admissible sets are the Boolean combinations of those of
the intuitionistic general frame `H`.
- [CZ98, §8.3] -/
def toModal (H : Propositional.GeneralFrame κ) : _root_.GeneralFrame κ where
  toFrame := H.toFrame
  Adm := (closure H.Adm : Set (Set κ))
  univ_mem := (closure H.Adm).top_mem
  inter_mem hX hY := (closure H.Adm).inf_mem hX hY
  compl_mem hX := (closure H.Adm).compl_mem hX
  diaSet_mem hX := Frame.diaSet_mem_closure H.isSublattice_adm H.himpSet_mem H.empty_mem hX

variable {H : Propositional.GeneralFrame κ}

instance : IsPreorder κ H.toModal.Rel :=
  inferInstanceAs (IsPreorder κ H.Rel)

lemma subset_toModal_adm : H.Adm ⊆ H.toModal.Adm := subset_closure

/-- An admissible upset of `σ H` is admissible in `H`. -/
lemma mem_adm_of_isUpset_of_mem_toModal {X : Set κ} (hX : X ∈ H.toModal.Adm)
    (h : H.toFrame.IsUpset X) : X ∈ H.Adm :=
  Frame.mem_of_isUpset_of_mem_closure H.isSublattice_adm H.himpSet_mem H.empty_mem hX h

end GeneralFrame

section

variable {G : _root_.GeneralFrame κ} [IsPreorder κ G.Rel]

/-- `σ ρ G` has fewer admissible sets than `G`. -/
lemma _root_.GeneralFrame.toIntuitionistic_toModal_adm_subset :
    G.toIntuitionistic.toModal.Adm ⊆ G.Adm := by
  intro X hX;
  have h : BooleanSubalgebra.closure G.toIntuitionistic.Adm ≤ G.admSubalgebra :=
    BooleanSubalgebra.closure_le.mpr _root_.GeneralFrame.upAdm_subset_adm;
  exact h hX

lemma _root_.GeneralFrame.logic_le_toIntuitionistic_toModal :
    (G.logic : NormalLogic α) ≤ G.toIntuitionistic.toModal.logic := by
  intro A hA V hV;
  exact hA V fun a => _root_.GeneralFrame.toIntuitionistic_toModal_adm_subset (hV a)

end

/-- The valuation `V` has the same truth sets as `□#a` in `⟨F, V⟩` when `V` is hereditary. -/
private lemma iff_forces_box_of_hereditary {F : Frame κ} [Std.Refl F.Rel] {V : κ → α → Prop}
    (hV : ∀ {x y : κ}, F.Rel x y → ∀ {a}, V x a → V y a) (x : κ) (a : α) :
    V x a ↔ x ⊩[(⟨F, V⟩ : _root_.Model κ α)] □(#a) := by
  rw [_root_.Model.World.forces_box];
  constructor;
  · exact fun hx y Rxy => hV Rxy hx;
  · exact fun hx => hx x (Std.Refl.refl x)

namespace GeneralFrame

variable {H : Propositional.GeneralFrame κ} {A : Formula α}

/-- A modal formula `Aᵍ` is valid in `σ H` iff `A` is valid in `H`.
- [CZ98, Lemma 8.28] -/
theorem toModal_validates_gödelTranslate_iff : H.toModal ⊧ Aᵍ ↔ H ⊧ A := by
  constructor;
  · intro h W hW x;
    exact (Model.forces_gödelTranslate_iff_of_val (F := H.toFrame) (V := W)
      (hW := hW.hereditary) (iff_forces_box_of_hereditary hW.hereditary)).mpr
      (h W (fun a => subset_toModal_adm (hW a)) x);
  · intro h V hV x;
    have hW : H.IsAdmissible fun w a => w ⊩[H.toModal.model V] □(#a) := by
      intro a;
      rw [_root_.GeneralFrame.truthSet_box];
      exact mem_adm_of_isUpset_of_mem_toModal (_root_.GeneralFrame.boxSet_mem (hV a))
        (Frame.isUpset_boxSet _);
    exact (Model.forces_gödelTranslate_iff_of_val (F := H.toFrame) (V := V)
      (hW := hW.hereditary) (fun _ _ => Iff.rfl)).mp (h _ hW x)

end GeneralFrame

section

variable {G : _root_.GeneralFrame κ} [IsPreorder κ G.Rel] {A : Formula α}

/-- A modal formula `Aᵍ` is valid in `G` iff `A` is valid in `ρ G`.
- [CZ98, Lemma 8.28] -/
theorem _root_.GeneralFrame.validates_gödelTranslate_iff_toIntuitionistic :
    G ⊧ Aᵍ ↔ G.toIntuitionistic ⊧ A := by
  constructor;
  · intro h W hW x;
    have hW' : G.IsAdmissible W := fun a => _root_.GeneralFrame.upAdm_subset_adm (hW a);
    exact (Model.forces_gödelTranslate_iff_of_val (F := G.toFrame) (V := W)
      (hW := hW.hereditary) (iff_forces_box_of_hereditary hW.hereditary)).mpr (h W hW' x);
  · intro h V hV x;
    have hW : G.toIntuitionistic.IsAdmissible fun w a => w ⊩[G.model V] □(#a) := by
      intro a;
      rw [_root_.GeneralFrame.truthSet_box];
      exact _root_.GeneralFrame.boxSet_mem_upAdm (hV a);
    exact (Model.forces_gödelTranslate_iff_of_val (F := G.toFrame) (V := V)
      (hW := hW.hereditary) (fun _ _ => Iff.rfl)).mp (h _ hW x)

end

namespace GeneralFrame

variable {H : Propositional.GeneralFrame κ}

/-- Above a point outside a Boolean combination `X` of admissible upsets there is a point outside
`X` from which one never re-enters `X`. -/
lemma exists_rel_not_mem_of_mem_toModal_adm {X : Set H.World} (hX : X ∈ H.toModal.Adm)
    {x : H.World} (hx : x ∉ X) :
    ∃ z : H.World, x ≺ z ∧ z ∉ X ∧ ∀ u v : H.World, z ≺ u → u ≺ v → u ∈ X → v ∈ X := by
  obtain ⟨𝒵, h𝒵, hdet⟩ := BooleanSubalgebra.exists_finset_determines hX;
  exact Frame.exists_rel_not_mem_of_finset_determines
    (fun Z hZ => H.isUpset_of_mem (h𝒵 hZ)) hdet hx

/-- The Grzegorczyk axiom is valid in `σ H`. -/
theorem toModal_validates_grz (A : _root_.Formula α) :
    H.toModal ⊧ □(□(A 🡒 □A) 🡒 A) 🡒 A := by
  intro V hV x;
  rw [_root_.Model.World.forces_imp];
  by_cases hA : x ⊩[H.toModal.model V] A;
  · exact Or.inr hA;
  · left;
    by_contra hbox;
    obtain ⟨z, Rxz, hz, hstep⟩ :=
      exists_rel_not_mem_of_mem_toModal_adm (_root_.GeneralFrame.truthSet_mem hV A) hA;
    have h₁ : z ⊩[H.toModal.model V] □(A 🡒 □A) := by
      rw [_root_.Model.World.forces_box];
      intro u Rzu;
      rw [_root_.Model.World.forces_imp];
      by_cases hu : u ⊩[H.toModal.model V] A;
      · right;
        rw [_root_.Model.World.forces_box];
        intro v Ruv;
        exact hstep u v Rzu Ruv hu;
      · exact Or.inl hu;
    have h₂ := (_root_.Model.World.forces_box.mp hbox) z Rxz;
    rw [_root_.Model.World.forces_imp] at h₂;
    rcases h₂ with h₂ | h₂;
    · exact h₂ h₁;
    · exact hz h₂

/-- - [CZ98, §8.3]
- [BC22, §1.5] -/
theorem toModal_validates_logicGrz : H.toModal ⊧ (𝐆𝐫𝐳 : NormalLogic α) := by
  apply _root_.GeneralFrame.validatesLogic_add _root_.GeneralFrame.validates_logicS4;
  rintro _ ⟨A, rfl⟩;
  exact toModal_validates_grz A

end GeneralFrame

end Propositional

end
