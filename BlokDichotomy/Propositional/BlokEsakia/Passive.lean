module

public import BlokDichotomy.Propositional.GeneralFrame.Companion

/-!
# Passive points

A point `y ∈ U` is passive in `U` if one cannot leave `U` from `y` and come back. The set of
passive points of an admissible set `U` is a Boolean combination of admissible upsets, and in a
general frame validating the Grzegorczyk axiom every point of `U` has a passive point above it.

## References

- [BC22, §1.5]
-/

@[expose] public section

universe u v

variable {κ : Type u} {α : Type v}

/-- The points of `U` from which one cannot leave `U` and come back.
- [BC22, §1.5] -/
def Frame.passive (F : Frame κ) (U : Set F.World) : Set F.World :=
  F.diaSet U ∩ F.boxSet (U ∪ F.boxSet Uᶜ)

namespace Frame

variable {F : Frame κ} {U : Set F.World} {y : F.World}

section

variable [IsPreorder κ F.Rel]

lemma mem_passive_iff :
    y ∈ F.passive U ↔ y ∈ U ∧ ∀ u v : F.World, y ≺ u → u ≺ v → u ∉ U → v ∉ U := by
  constructor;
  · rintro ⟨⟨v, Ryv, hv⟩, hbox⟩;
    have hyU : y ∈ U := by
      rcases hbox y (rel_refl y) with hy | hy;
      · exact hy;
      · exact absurd hv (hy v Ryv);
    and_intros;
    · exact hyU;
    · intro u w Ryu Ruw hu;
      rcases hbox u Ryu with hu' | hu';
      · exact absurd hu' hu;
      · exact hu' w Ruw;
  · rintro ⟨hyU, h⟩;
    and_intros;
    · exact ⟨y, rel_refl y, hyU⟩;
    · intro u Ryu;
      by_cases hu : u ∈ U;
      · exact Or.inl hu;
      · exact Or.inr fun v Ruv => h u v Ryu Ruv hu;

lemma passive_subset : F.passive U ⊆ U := fun _ hy => (mem_passive_iff.mp hy).1

end

end Frame

namespace GeneralFrame

variable {G : GeneralFrame κ} [IsPreorder κ G.Rel] {U : Set G.World}

/-- The passive points of an admissible set are admissible in `σ ρ G`. -/
lemma passive_mem_toIntuitionistic_toModal (hU : U ∈ G.Adm) :
    G.toFrame.passive U ∈ G.toIntuitionistic.toModal.Adm := by
  have h₁ : G.toFrame.boxSet Uᶜ ∈ G.toIntuitionistic.toModal.Adm :=
    Propositional.GeneralFrame.subset_toModal_adm (G.boxSet_mem_upAdm (G.compl_mem hU));
  have h₂ : G.toFrame.boxSet (U ∪ G.toFrame.boxSet Uᶜ) ∈ G.toIntuitionistic.toModal.Adm :=
    Propositional.GeneralFrame.subset_toModal_adm
      (G.boxSet_mem_upAdm (G.union_mem hU (G.boxSet_mem (G.compl_mem hU))));
  have h₃ : G.toFrame.diaSet U ∈ G.toIntuitionistic.toModal.Adm := by
    rw [Frame.diaSet_eq];
    exact G.toIntuitionistic.toModal.compl_mem h₁;
  exact G.toIntuitionistic.toModal.inter_mem h₃ h₂

/-- Under the Grzegorczyk axiom, every point of an admissible set `U` has a passive point of `U`
above it.
- [BC22, Theorem 1.12] -/
lemma exists_passive_of_grz {a : α} (hGrz : G ⊧ □(□(#a 🡒 □#a) 🡒 #a) 🡒 #a) (hU : U ∈ G.Adm)
    {x : G.World} (hx : x ∈ U) : ∃ y : G.World, x ≺ y ∧ y ∈ G.toFrame.passive U := by
  have hV : G.IsAdmissible fun w (_ : α) => w ∉ U := fun _ => G.compl_mem hU;
  have h₁ := hGrz _ hV x;
  rw [Model.World.forces_imp] at h₁;
  rcases h₁ with h₁ | h₁;
  · rw [Model.World.not_forces_box] at h₁;
    obtain ⟨y, Rxy, hy⟩ := h₁;
    rw [Model.World.not_forces_imp, Model.World.forces_box] at hy;
    have h₂ : y ∈ U := by
      by_contra hyU;
      exact hy.2 hyU;
    have h₃ : ∀ u v : G.World, y ≺ u → u ≺ v → u ∉ U → v ∉ U := by
      intro u v Ryu Ruv hu;
      rcases (Model.World.forces_imp.mp (hy.1 u Ryu)) with h | h;
      · exact absurd (not_not.mp h) hu;
      · exact (Model.World.forces_box.mp h) v Ruv;
    exact ⟨y, Rxy, Frame.mem_passive_iff.mpr ⟨h₂, h₃⟩⟩;
  · exact absurd hx h₁

end GeneralFrame

end
