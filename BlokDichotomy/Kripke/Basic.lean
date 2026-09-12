module

public import BlokDichotomy.Formula.Substitution
public import BlokDichotomy.Logic.Basic
public import Mathlib.Order.SetNotation

@[expose]
public section

variable {κ : Type u} {α β : Type v}

structure Frame (κ : Type u) where
  Rel'      : κ → κ → Prop
namespace Frame

variable {F : Frame κ}

abbrev World {_ : Frame κ} := κ

abbrev Rel {F : Frame κ} : F.World → F.World → Prop := F.Rel'
infixl:60 " ≺ " => Rel

end Frame



structure Model (κ : Type u) (α : Type v) extends Frame κ where
  Val'      : κ → α → Prop

namespace Model

variable {M : Model κ α}

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

end Model


namespace Model.World

variable {M : Model κ α} {x y: M.World} {A B : Formula α}

@[grind =]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
| #a    => M.Val x a
| ⊥     => False
| A 🡒 B => Forces M x A → Forces M x B
| ◇A    => ∃ y : M.World, x ≺ y ∧ Forces _ y A
notation:80 x:50 " ⊩[" M "] " A:50 => Forces M x A
infix:50 " ⊩ " => Forces _

abbrev NotForces (M : Model κ α) (x : M.World) (A : Formula α) : Prop := ¬(x ⊩ A)
notation:80 x:50 " ⊮[" M "] " A:50 => NotForces M x A
infix:50 " ⊮ " => NotForces _

@[simp, grind .] lemma forces_top : x ⊩ ⊤ := by grind;
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y : M.World, x ≺ y ∧ y ⊩ A := by grind;

@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := by tauto;
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by grind;
@[grind =] lemma forces_or  : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y : M.World, x ≺ y → y ⊩ A := by grind;

@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := by tauto;
@[grind =] lemma not_forces_and : x ⊮ A ⋏ B ↔ x ⊮ A ∨ x ⊮ B := by grind;
@[grind =] lemma not_forces_or  : x ⊮ A ⋎ B ↔ x ⊮ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_neg : x ⊮ ∼A ↔ x ⊩ A := by grind;
@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_dia : x ⊮ ◇A ↔ ∀ y : M.World, x ≺ y → y ⊮ A := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y : M.World, x ≺ y ∧ y ⊮ A := by grind;

@[grind =]
lemma forces_subst {M : Model κ β} {x : M.World} {A : Formula α} (σ : Formula.Substitution α β) :
  x ⊩[M] A⟦σ⟧ ↔ x ⊩[⟨M.toFrame, fun w a => w ⊩[M] σ a⟩] A := by
  induction A generalizing x <;> grind;

end Model.World


namespace Model

variable {M : Model κ α} {A : Formula α}

@[grind]
def Validates (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validates

end Model



namespace Frame

variable {F : Frame κ} {A : Formula α}

@[grind =]
def Validates (F : Frame κ) (A : Formula α) : Prop := ∀ V, (Model.mk F V) ⊧ A
infix:50 " ⊧ " => Frame.Validates

@[grind]
def ValidatesSet (F : Frame κ) (X : Set (Formula α)) : Prop := ∀ A ∈ X, F.Validates A
infix:50 " ⊧ " => Frame.ValidatesSet

abbrev ValidateLogic (F : Frame κ) (L : NormalLogic α) : Prop := F ⊧ L.carrier
infix:50 " ⊧ " => Frame.ValidateLogic

lemma mdp (hA : F ⊧ A) (hAB : F ⊧ A 🡒 B) : F ⊧ B := by
  intro V x;
  exact hAB V x $ hA V x;

lemma nec (h : F ⊧ A) : F ⊧ □A := by grind;

lemma subst {σ : Formula.Substitution α α} (h : F ⊧ A) : F ⊧ A⟦σ⟧ := by
  intro V x;
  exact Model.World.forces_subst σ |>.mpr $ h (fun w a => w ⊩[⟨F, V⟩] σ a) x

abbrev logic (F : Frame κ) : NormalLogic α where
  carrier := { A | F ⊧ A }
  mdp := mdp
  nec := nec
  subst := subst

end Frame


namespace Logic

def Incomplete (L : NormalLogic α) : Prop := ∃ A : Formula α, (∀ F : Frame κ, F ⊧ L → F ⊧ A) ∧ (A ∉ L.carrier)

end Logic

end
