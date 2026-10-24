module

public import BlokDichotomy.GeneralFrame.Preorder

/-!
# The canonical general frame

The canonical frame of a normal logic equipped with the sets `{x | B ∈ x}` as admissible sets.
It validates exactly the formulas of the logic, and for extensions of `𝐒𝟒` its admissible upsets
are the sets `{x | □B ∈ x}`.

## References

- [CZ98, §8.4]
-/

@[expose] public section

universe v

namespace NormalLogic

variable {α : Type v} (L : NormalLogic α) [L.IsNExt 𝐊]

open Model.World

/-- The canonical general frame of `L`: the canonical frame with the admissible sets
`{x | B ∈ x}`.
- [CZ98, §8.4] -/
def canonicalGeneralFrame : GeneralFrame L.MaximalConsistentSet where
  toFrame := L.canonicalModel.toFrame
  Adm := Set.range fun B : Formula α => {x : L.MaximalConsistentSet | B ∈ x}
  univ_mem := by
    use ⊤;
    ext x;
    simpa using x.top_mem;
  inter_mem := by
    rintro _ _ ⟨B, rfl⟩ ⟨C, rfl⟩;
    use B ⋏ C;
    ext x;
    simp [x.and_mem_iff];
  compl_mem := by
    rintro _ ⟨B, rfl⟩;
    use ∼B;
    ext x;
    simp [x.neg_mem_iff];
  diaSet_mem := by
    rintro _ ⟨B, rfl⟩;
    use ◇B;
    ext x;
    simp only [Frame.diaSet, Set.mem_ofPred_eq];
    rw [← canonicalModel.truthlemma, forces_dia];
    simp [canonicalModel.truthlemma]

namespace canonicalGeneralFrame

variable {L}

lemma mem_adm_iff {X : Set L.MaximalConsistentSet} :
    X ∈ L.canonicalGeneralFrame.Adm ↔ ∃ B : Formula α, X = {x | B ∈ x} := by
  constructor;
  · rintro ⟨B, rfl⟩;
    exact ⟨B, rfl⟩;
  · rintro ⟨B, rfl⟩;
    exact ⟨B, rfl⟩

lemma truthSet_eq (B : Formula α) :
    {x : L.MaximalConsistentSet | B ∈ x} = {x | x ⊩[L.canonicalModel] B} := by
  ext x;
  exact canonicalModel.truthlemma.symm

lemma canonicalVal_isAdmissible :
    L.canonicalGeneralFrame.IsAdmissible L.canonicalModel.Val :=
  fun a => ⟨#a, rfl⟩

lemma model_canonicalVal :
    L.canonicalGeneralFrame.model L.canonicalModel.Val = L.canonicalModel := rfl

theorem validates_iff {A : Formula α} : L.canonicalGeneralFrame ⊧ A ↔ A ∈ L := by
  constructor;
  · intro h;
    apply mem_iff_canonicalModel_validates.mpr;
    exact h _ canonicalVal_isAdmissible;
  · intro h V hV;
    choose B hB using hV;
    have h₁ : L.canonicalGeneralFrame.model V =
        ⟨L.canonicalModel.toFrame, fun w a => w ⊩[L.canonicalModel] B a⟩ := by
      have h₂ : V = fun w a => w ⊩[L.canonicalModel] B a := by
        funext w a;
        apply propext;
        have h₃ := congrArg (w ∈ ·) (hB a);
        simpa [canonicalModel.truthlemma] using h₃.symm;
      subst h₂;
      rfl;
    rw [h₁];
    intro x;
    exact (forces_subst B).mp <| canonicalModel_validates_of_mem (mem_subst h) x

lemma validatesLogic_self : L.canonicalGeneralFrame ⊧ L :=
  fun _ hA => validates_iff.mpr hA

instance [L.IsNExt 𝐒𝟒] : IsPreorder L.MaximalConsistentSet L.canonicalGeneralFrame.Rel :=
  inferInstanceAs (IsPreorder L.MaximalConsistentSet L.canonicalModel.Rel)

lemma boxSet_truthSet (B : Formula α) :
    L.canonicalGeneralFrame.toFrame.boxSet {x | B ∈ x} = {x | □B ∈ x} := by
  ext x;
  simp only [Frame.boxSet, Set.mem_ofPred_eq];
  rw [← canonicalModel.truthlemma, forces_box];
  simp only [canonicalModel.truthlemma];
  exact Iff.rfl

/-- The admissible upsets of the canonical frame are the sets `{x | □B ∈ x}`. -/
lemma mem_upAdm_iff [L.IsNExt 𝐒𝟒] {X : Set L.MaximalConsistentSet} :
    X ∈ L.canonicalGeneralFrame.upAdm ↔ ∃ B : Formula α, X = {x | □B ∈ x} := by
  constructor;
  · rintro ⟨hX, hup⟩;
    obtain ⟨B, rfl⟩ := mem_adm_iff.mp hX;
    use B;
    rw [← boxSet_truthSet];
    exact hup.boxSet_eq.symm;
  · rintro ⟨B, rfl⟩;
    rw [← boxSet_truthSet];
    exact GeneralFrame.boxSet_mem_upAdm ⟨B, rfl⟩

end canonicalGeneralFrame

end NormalLogic

end
