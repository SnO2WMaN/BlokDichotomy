module

public import BlokDichotomy.GeneralFrame.Preorder
public import BlokDichotomy.Propositional.Kripke.Basic
public import BlokDichotomy.Propositional.Kripke.Completeness

/-!
# Intuitionistic general frames

General frames for intuitionistic logic: a preorder together with a family of admissible upward
closed sets closed under `∩`, `∪` and the Heyting implication, validity of formulas and logics in
them, and the closure of validity under substitution. The canonical general frame of a
superintuitionistic logic, whose admissible sets are the sets `{x | A ∈ x}`, validates exactly the
formulas of the logic.

## References

- [CZ98, §8.1]
- [CZ98, §8.4]
-/

@[expose] public section

universe u v

namespace Propositional

variable {κ : Type u} {α : Type v}

/-- An intuitionistic general frame: a preorder together with a family `Adm` of admissible upward
closed sets that contains `∅` and is closed under `∩`, `∪` and `Frame.himpSet`.
- [CZ98, §8.1] -/
structure GeneralFrame (κ : Type u) extends Frame κ where
  refl (x : toFrame.World) : x ≺ x
  trans {x y z : toFrame.World} : x ≺ y → y ≺ z → x ≺ z
  Adm : Set (Set toFrame.World)
  isUpwardClosed_of_mem {X : Set toFrame.World} : X ∈ Adm → toFrame.IsUpwardClosed X
  empty_mem : ∅ ∈ Adm
  inter_mem {X Y : Set toFrame.World} : X ∈ Adm → Y ∈ Adm → X ∩ Y ∈ Adm
  union_mem {X Y : Set toFrame.World} : X ∈ Adm → Y ∈ Adm → X ∪ Y ∈ Adm
  himpSet_mem {X Y : Set toFrame.World} : X ∈ Adm → Y ∈ Adm → toFrame.himpSet X Y ∈ Adm

namespace GeneralFrame

variable {H : GeneralFrame κ}

instance : IsPreorder _ H.Rel where
  refl := H.refl
  trans _ _ _ := H.trans

lemma univ_mem : Set.univ ∈ H.Adm := by
  simpa [Frame.himpSet] using H.himpSet_mem H.empty_mem H.empty_mem

lemma isSublattice_adm : IsSublattice H.Adm := by
  constructor;
  · intro X hX Y hY;
    exact H.union_mem hX hY;
  · intro X hX Y hY;
    exact H.inter_mem hX hY

/-- `V` is admissible when `{w | V w a} ∈ H.Adm` for every `a`. -/
def IsAdmissible (H : GeneralFrame κ) (V : H.World → α → Prop) : Prop :=
  ∀ a, {w | V w a} ∈ H.Adm

variable {V : H.World → α → Prop}

lemma IsAdmissible.hereditary (hV : H.IsAdmissible V) {x y : H.World} (Rxy : x ≺ y) {a : α}
    (h : V x a) : V y a :=
  H.isUpwardClosed_of_mem (hV a) Rxy h

/-- The intuitionistic model on `H` with an admissible valuation. -/
def model (H : GeneralFrame κ) (V : H.World → α → Prop) (hV : H.IsAdmissible V) :
    Model κ α :=
  ⟨H.toFrame, V, hV.hereditary⟩

open _root_.Propositional.Model.World

variable {A B : Formula α}

lemma truthSet_mem (hV : H.IsAdmissible V) (A : Formula α) :
    {w | w ⊩[H.model V hV] A} ∈ H.Adm := by
  induction A with
  | falsum => simpa using H.empty_mem;
  | atom a => exact hV a;
  | and A B ihA ihB =>
    convert H.inter_mem ihA ihB using 1;
    ext w;
    simp [forces_and];
  | or A B ihA ihB =>
    convert H.union_mem ihA ihB using 1;
    ext w;
    simp [forces_or];
  | imp A B ihA ihB =>
    convert H.himpSet_mem ihA ihB using 1;
    ext w;
    simp [forces_imp, Frame.himpSet, model];

/-- `A` is true at every point under every admissible valuation.
- [CZ98, §8.1] -/
def Validates (H : GeneralFrame κ) (A : Formula α) : Prop :=
  ∀ (V : H.World → α → Prop) (hV : H.IsAdmissible V), H.model V hV ⊧ A
scoped[Propositional] infix:50 " ⊧ " => GeneralFrame.Validates

abbrev NotValidates (H : GeneralFrame κ) (A : Formula α) : Prop := ¬(H ⊧ A)
scoped[Propositional] infix:50 " ⊭ " => GeneralFrame.NotValidates

/-- `H` validates every formula of `L`. -/
def ValidatesLogic (H : GeneralFrame κ) (L : Logic α) : Prop := ∀ A ∈ L, H ⊧ A
scoped[Propositional] infix:50 " ⊧ " => GeneralFrame.ValidatesLogic

lemma isAdmissible_subst (hV : H.IsAdmissible V) (s : Formula.Substitution α α) :
    H.IsAdmissible fun w a => w ⊩[H.model V hV] s a :=
  fun a => truthSet_mem hV (s a)

lemma Validates.subst (h : H ⊧ A) (s : Formula.Substitution α α) : H ⊧ A⟦s⟧ := by
  intro V hV x;
  exact (forces_subst s (isAdmissible_subst hV s).hereditary).mpr
    (h _ (isAdmissible_subst hV s) x)

lemma validates_of_mem_logicInt (h : A ∈ 𝐈𝐧𝐭) : H ⊧ A := by
  intro V hV x;
  exact Frame.validates_of_mem_logicInt (F := H.toFrame) h V hV.hereditary x

end GeneralFrame

end Propositional

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
  isUpwardClosed_of_mem := by
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

lemma canonicalVal_isAdmissible :
    L.canonicalGeneralFrame.IsAdmissible L.canonicalModel.Val :=
  fun a => ⟨#a, rfl⟩

/-- A formula is valid in the canonical general frame of `L` iff it belongs to `L`.
- [CZ98, §8.4] -/
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
