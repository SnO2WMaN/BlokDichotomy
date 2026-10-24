module

public import BlokDichotomy.Propositional.GeneralFrame.Basic
public import BlokDichotomy.Propositional.Kripke.Completeness

/-!
# The canonical intuitionistic general frame

The canonical frame of a superintuitionistic logic equipped with the sets `{x | A ∈ x}` as
admissible sets. It validates exactly the formulas of the logic.

## References

- [CZ98, §8.4]
-/

@[expose] public section

universe v

namespace Propositional.Logic

variable {α : Type v} (L : Logic α) [L.IsExt 𝐈𝐧𝐭]

open _root_.Propositional.Model.World

/-- The canonical general frame of `L`: the prime theories ordered by inclusion, with the
admissible sets `{x | A ∈ x}`.
- [CZ98, §8.4] -/
def canonicalGeneralFrame : GeneralFrame L.PrimeTheory where
  toFrame := L.canonicalModel.toFrame
  refl _ := subset_rfl
  trans := subset_trans
  Adm := Set.range fun A : Formula α => {x : L.PrimeTheory | A ∈ x}
  isUpset_of_mem := by
    rintro _ ⟨A, rfl⟩ x y Rxy hx;
    exact Rxy hx;
  empty_mem := by
    use ⊥;
    ext x;
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false];
    exact x.bot_not_mem;
  inter_mem := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩;
    use A ⋏ B;
    ext x;
    simp [x.and_mem_iff];
  union_mem := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩;
    use A ⋎ B;
    ext x;
    simp [x.or_mem_iff];
  himpSet_mem := by
    rintro _ _ ⟨A, rfl⟩ ⟨B, rfl⟩;
    use A 🡒 B;
    ext x;
    simp only [Frame.himpSet, Set.mem_ofPred_eq, ← canonicalModel.truthlemma];
    exact forces_imp

namespace canonicalGeneralFrame

variable {L}

lemma mem_adm_iff {X : Set L.PrimeTheory} :
    X ∈ L.canonicalGeneralFrame.Adm ↔ ∃ A : Formula α, X = {x | A ∈ x} := by
  constructor;
  · rintro ⟨A, rfl⟩;
    exact ⟨A, rfl⟩;
  · rintro ⟨A, rfl⟩;
    exact ⟨A, rfl⟩

lemma truthSet_eq (A : Formula α) :
    {x : L.PrimeTheory | A ∈ x} = {x | x ⊩[L.canonicalModel] A} := by
  ext x;
  exact canonicalModel.truthlemma.symm

lemma canonicalVal_isAdmissible :
    L.canonicalGeneralFrame.IsAdmissible L.canonicalModel.Val :=
  fun a => ⟨#a, rfl⟩

lemma model_canonicalVal :
    L.canonicalGeneralFrame.model L.canonicalModel.Val canonicalVal_isAdmissible =
      L.canonicalModel := rfl

/-- - [CZ98, §8.4] -/
theorem validates_iff {A : Formula α} : L.canonicalGeneralFrame ⊧ A ↔ A ∈ L := by
  constructor;
  · intro h;
    exact mem_iff_canonicalModel_validates.mpr <| h _ canonicalVal_isAdmissible;
  · intro h V hV;
    obtain ⟨B, hB⟩ : ∃ B : α → Formula α, ∀ a, {w | V w a} = {x | B a ∈ x} := by
      choose B hB using hV;
      exact ⟨B, fun a => (hB a).symm⟩;
    have h₁ : V = fun w a => w ⊩[L.canonicalModel] B a := by
      funext w a;
      apply propext;
      have h₂ := congrArg (w ∈ ·) (hB a);
      simpa [canonicalModel.truthlemma] using h₂;
    subst h₁;
    intro x;
    exact (forces_subst B fun Rxy => forces_of_rel Rxy).mp <|
      mem_iff_canonicalModel_validates.mp (mem_subst h) x

lemma validatesLogic_self : L.canonicalGeneralFrame ⊧ L :=
  fun _ hA => validates_iff.mpr hA

end canonicalGeneralFrame

end Propositional.Logic

end
