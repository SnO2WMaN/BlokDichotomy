module

public import BlokDichotomy.Kripke.Basic
public import BlokDichotomy.Propositional.Logic.Basic

/-!
# Kripke semantics of intuitionistic logic

Intuitionistic Kripke models over the frames `Frame κ` of modal logic, the forcing relation, its
heredity, validity in models and frames, and the soundness of `𝐈𝐧𝐭` for reflexive transitive
frames.

CZ98 takes intuitionistic frames to be partial orders. Here they are the reflexive transitive
frames, which are also the frames of `𝐒𝟒`; `𝐈𝐧𝐭` is complete for either class, since its
canonical frame is a partial order.

## References

- [CZ98, §2.2, Proposition 2.1, Theorem 2.43]
-/

@[expose] public section

universe u v

namespace Propositional

variable {κ : Type u} {α : Type v}

/-- An intuitionistic Kripke model: a frame together with a valuation whose truth sets are
upward closed.
- [CZ98, §2.2] -/
structure Model (κ : Type u) (α : Type v) extends Frame κ where
  Val : toFrame.World → α → Prop
  hereditary : ∀ {x y : toFrame.World}, x ≺ y → ∀ {a}, Val x a → Val y a

variable {M : Model κ α} {x y : M.World} {A B : Formula α}


namespace Model

attribute [grind =>] hereditary

end Model

namespace Model.World

/-- - [CZ98, §2.2] -/
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | #a    => M.Val x a
  | ⊥     => False
  | A ⋏ B => Forces M x A ∧ Forces M x B
  | A ⋎ B => Forces M x A ∨ Forces M x B
  | A 🡒 B => ∀ y : M.World, x ≺ y → Forces M y A → Forces M y B
scoped[Propositional] notation:80 x:50 " ⊩[" M "] " A:50 => Model.World.Forces M x A
scoped[Propositional] infix:50 " ⊩ " => Model.World.Forces _

abbrev NotForces (M : Model κ α) (x : M.World) (A : Formula α) : Prop := ¬(x ⊩[M] A)
scoped[Propositional] notation:80 x:50 " ⊮[" M "] " A:50 => Model.World.NotForces M x A
scoped[Propositional] infix:50 " ⊮ " => Model.World.NotForces _

@[simp, grind =] lemma forces_atom {a : α} : x ⊩[M] #a ↔ M.Val x a := Iff.rfl
@[simp, grind .] lemma not_forces_bot : x ⊮[M] ⊥ := id
@[simp, grind .] lemma forces_top : x ⊩[M] ⊤ := fun _ _ => id
@[simp, grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := Iff.rfl
@[simp, grind =] lemma forces_or : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := Iff.rfl
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ ∀ y : M.World, x ≺ y → y ⊩ A → y ⊩ B := Iff.rfl
@[grind =] lemma forces_neg : x ⊩ ∼A ↔ ∀ y : M.World, x ≺ y → y ⊮ A := Iff.rfl

@[grind =] lemma not_forces_and : x ⊮ A ⋏ B ↔ x ⊮ A ∨ x ⊮ B := by grind
@[grind =] lemma not_forces_or : x ⊮ A ⋎ B ↔ x ⊮ A ∧ x ⊮ B := by grind
@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ ∃ y : M.World, x ≺ y ∧ y ⊩ A ∧ y ⊮ B := by grind
@[grind =] lemma not_forces_neg : x ⊮ ∼A ↔ ∃ y : M.World, x ≺ y ∧ y ⊩ A := by grind

/-- Truth is preserved along the accessibility relation.
- [CZ98, Proposition 2.1] -/
@[grind →]
lemma forces_of_rel [IsTrans κ M.Rel] (Rxy : x ≺ y) (h : x ⊩ A) : y ⊩ A := by
  induction A generalizing x y <;> grind;

lemma not_forces_of_rel [IsTrans κ M.Rel] (Rxy : x ≺ y) (h : y ⊮ A) : x ⊮ A := by
  by_contra hx;
  exact h <| forces_of_rel Rxy hx;

lemma forces_subst (s : Formula.Substitution α α)
    (hV : ∀ {x y : κ}, M.Rel x y → ∀ {a}, (x ⊩[M] s a) → y ⊩[M] s a) :
    x ⊩[M] A⟦s⟧ ↔ x ⊩[(⟨M.toFrame, fun w a => w ⊩[M] s a, hV⟩ : Model κ α)] A := by
  induction A generalizing x <;> grind;

end Model.World

namespace Model

@[grind]
def Validates (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
scoped[Propositional] infix:50 " ⊧ " => Model.Validates

lemma not_validates_iff : ¬M ⊧ A ↔ ∃ x : M.World, x ⊮ A := by
  simp [Validates]

end Model

namespace Frame

variable {F : Frame κ}

/-- `A` is true at every point of every intuitionistic model on `F`.
- [CZ98, §2.2] -/
@[grind]
def Validates (F : Frame κ) (A : Formula α) : Prop :=
  ∀ (V : κ → α → Prop) (hV : ∀ {x y : κ}, F.Rel x y → ∀ {a}, V x a → V y a),
    (⟨F, V, hV⟩ : Model κ α) ⊧ A
scoped[Propositional] infix:50 " ⊧ " => Frame.Validates

abbrev NotValidates (F : Frame κ) (A : Formula α) : Prop := ¬(F ⊧ A)
scoped[Propositional] infix:50 " ⊭ " => Frame.NotValidates

@[grind]
def ValidatesSet (F : Frame κ) (X : FormulaSet α) : Prop := ∀ A ∈ X, F ⊧ A
scoped[Propositional] infix:50 " ⊧ " => Frame.ValidatesSet

abbrev ValidateLogic (F : Frame κ) (L : Logic α) : Prop := F ⊧ L.carrier
scoped[Propositional] infix:50 " ⊧ " => Frame.ValidateLogic

abbrev NotValidateLogic (F : Frame κ) (L : Logic α) : Prop := ¬(F ⊧ L)
scoped[Propositional] infix:50 " ⊭ " => Frame.NotValidateLogic

lemma not_validates_iff :
    F ⊭ A ↔ ∃ V, ∃ hV : ∀ {x y : κ}, F.Rel x y → ∀ {a}, V x a → V y a,
      ¬(⟨F, V, hV⟩ : Model κ α) ⊧ A := by
  simp [NotValidates, Validates]

lemma not_validatesSet_iff {X : FormulaSet α} : ¬F ⊧ X ↔ ∃ A ∈ X, F ⊭ A := by
  simp [ValidatesSet, NotValidates]

lemma not_validateLogic_iff {L : Logic α} : F ⊭ L ↔ ∃ A ∈ L, F ⊭ A :=
  not_validatesSet_iff

/-- The logic of a reflexive transitive frame. -/
def logic (F : Frame κ) [IsPreorder κ F.Rel] : Logic α where
  carrier := { A | F ⊧ A }
  mdp := by
    intro A B hA hAB V hV x;
    exact hAB V hV x x (Std.Refl.refl x) (hA V hV x);
  subst := by
    intro A s h V hV x;
    have hV' : ∀ {x y : κ}, F.Rel x y → ∀ {a},
        (x ⊩[(⟨F, V, hV⟩ : Model κ α)] s a) → y ⊩[(⟨F, V, hV⟩ : Model κ α)] s a := by
      grind [Model.World.forces_of_rel (M := ⟨F, V, hV⟩)];
    exact (Model.World.forces_subst (M := ⟨F, V, hV⟩) s hV').mpr <| h _ hV' x;

/-- Every reflexive transitive frame validates `𝐈𝐧𝐭`.
- [CZ98, Theorem 2.43] -/
theorem logicInt_le_logic [IsPreorder κ F.Rel] : 𝐈𝐧𝐭 ≤ Frame.logic (α := α) F := by
  apply Logic.ofSet_le;
  intro A hA V hV x;
  cases hA <;> grind [Model.World.forces_of_rel (M := ⟨F, V, hV⟩)];

/-- - [CZ98, Theorem 2.43] -/
theorem validates_of_mem_logicInt [IsPreorder κ F.Rel] (h : A ∈ 𝐈𝐧𝐭) : F ⊧ A :=
  logicInt_le_logic h

end Frame

end Propositional

end
