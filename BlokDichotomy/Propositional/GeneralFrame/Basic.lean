module

public import BlokDichotomy.GeneralFrame.Preorder
public import BlokDichotomy.Propositional.Kripke.Basic

/-!
# Intuitionistic general frames

General frames for intuitionistic logic: a preorder together with a family of admissible upsets
closed under `∩`, `∪` and the Heyting implication, validity of formulas and logics in them, and
the closure of validity under substitution.

## References

- [CZ98, §8.1]
-/

@[expose] public section

universe u v

namespace Propositional

variable {κ : Type u} {α : Type v}

/-- An intuitionistic general frame: a preorder together with a family `Adm` of admissible upsets
that contains `∅` and is closed under `∩`, `∪` and `Frame.himpSet`.
- [CZ98, §8.1] -/
structure GeneralFrame (κ : Type u) extends Frame κ where
  refl (x : toFrame.World) : x ≺ x
  trans {x y z : toFrame.World} : x ≺ y → y ≺ z → x ≺ z
  Adm : Set (Set κ)
  isUpset_of_mem {X : Set κ} : X ∈ Adm → toFrame.IsUpset X
  empty_mem : ∅ ∈ Adm
  inter_mem {X Y : Set κ} : X ∈ Adm → Y ∈ Adm → X ∩ Y ∈ Adm
  union_mem {X Y : Set κ} : X ∈ Adm → Y ∈ Adm → X ∪ Y ∈ Adm
  himpSet_mem {X Y : Set κ} : X ∈ Adm → Y ∈ Adm → toFrame.himpSet X Y ∈ Adm

namespace GeneralFrame

variable {H : GeneralFrame κ}

instance : IsPreorder κ H.Rel where
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
  H.isUpset_of_mem (hV a) Rxy h

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

end
