module

public import Mathlib.Tactic.DeriveCountable
public import Mathlib.Tactic.ScopedNS
public import BlokDichotomy.ToMathlib.Data.List.Induction

/-!
# Formulas of intuitionistic propositional logic

Formulas built from variables, `⊥`, `⋏`, `⋎` and `🡒`, and their substitutions. The connectives
share their notation with modal formulas (`Modal.Formula`); the notation is scoped to the namespace
`Propositional`, and the expected type tells the two apart.

## References

- [CZ98, §1.1]
-/

@[expose] public section

universe u w

namespace Propositional

inductive Formula (α : Type u) where
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

deriving instance Countable for Formula

abbrev FormulaSet (α : Type u) := Set (Formula α)

namespace Formula

section

variable {α : Type u} {A A₁ A₂ B B₁ B₂ : Formula α}

instance : Bot (Formula α) := ⟨falsum⟩

scoped[Propositional] prefix:max "#" => Formula.atom
scoped[Propositional] infixr:60 " 🡒 " => Formula.imp
scoped[Propositional] infixr:69 " ⋏ " => Formula.and
scoped[Propositional] infixr:68 " ⋎ " => Formula.or

@[match_pattern] abbrev neg (A : Formula α) : Formula α := A 🡒 ⊥
scoped[Propositional] prefix:75 "∼" => Formula.neg

@[match_pattern] abbrev verum : Formula α := ∼⊥

instance : Top (Formula α) := ⟨verum⟩

@[match_pattern] abbrev iff (A B : Formula α) : Formula α := (A 🡒 B) ⋏ (B 🡒 A)
scoped[Propositional] infix:61 " 🡘 " => Formula.iff

lemma falsum_eq : (⊥ : Formula α) = falsum := rfl
lemma verum_eq : (⊤ : Formula α) = verum := rfl
@[grind =] lemma eq_verum_neg_falsum : ⊤ = ∼(⊥ : Formula α) := rfl
attribute [grind =_] falsum_eq verum_eq

@[grind =] lemma inj_and : A₁ ⋏ A₂ = B₁ ⋏ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp
@[grind =] lemma inj_or : A₁ ⋎ A₂ = B₁ ⋎ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp
@[grind =] lemma inj_imp : A₁ 🡒 A₂ = B₁ 🡒 B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp
@[grind =] lemma inj_neg : ∼A = ∼B ↔ A = B := by simp [neg]

@[induction_eliminator]
def rec' {motive : Formula α → Sort w}
    (falsum : motive ⊥)
    (atom : ∀ a, motive (#a))
    (and : ∀ A B, motive A → motive B → motive (A ⋏ B))
    (or : ∀ A B, motive A → motive B → motive (A ⋎ B))
    (imp : ∀ A B, motive A → motive B → motive (A 🡒 B))
    : (A : Formula α) → motive A
  | ⊥     => falsum
  | #a    => atom a
  | A ⋏ B => and A B (rec' falsum atom and or imp A) (rec' falsum atom and or imp B)
  | A ⋎ B => or A B (rec' falsum atom and or imp A) (rec' falsum atom and or imp B)
  | A 🡒 B => imp A B (rec' falsum atom and or imp A) (rec' falsum atom and or imp B)

end

section

variable {α β γ : Type*}

abbrev Substitution (α β) := α → Formula β

@[grind]
def subst (s : Substitution α β) : Formula α → Formula β
  | #a    => s a
  | ⊥     => ⊥
  | A ⋏ B => subst s A ⋏ subst s B
  | A ⋎ B => subst s A ⋎ subst s B
  | A 🡒 B => subst s A 🡒 subst s B
scoped[Propositional] notation:95 A "⟦" s "⟧" => Formula.subst s A

variable {s : Substitution α β} {A B : Formula α}

@[simp, grind =] lemma subst_atom {a : α} : (#a)⟦s⟧ = s a := rfl
@[simp, grind =] lemma subst_bot : (⊥ : Formula α)⟦s⟧ = ⊥ := rfl
@[simp, grind =] lemma subst_and : (A ⋏ B)⟦s⟧ = A⟦s⟧ ⋏ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_or : (A ⋎ B)⟦s⟧ = A⟦s⟧ ⋎ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_imp : (A 🡒 B)⟦s⟧ = A⟦s⟧ 🡒 B⟦s⟧ := rfl
@[simp, grind =] lemma subst_neg : (∼A)⟦s⟧ = ∼(A⟦s⟧) := rfl
@[simp, grind =] lemma subst_top : (⊤ : Formula α)⟦s⟧ = ⊤ := rfl
@[simp, grind =] lemma subst_iff : (A 🡘 B)⟦s⟧ = A⟦s⟧ 🡘 B⟦s⟧ := rfl

@[grind =]
lemma subst_subst {t : Substitution α β} {s : Substitution β γ} :
    (A⟦t⟧)⟦s⟧ = A⟦fun a => (t a)⟦s⟧⟧ := by
  induction A <;> grind

@[simp, grind =]
lemma subst_id : A⟦(#·)⟧ = A := by induction A <;> grind

end

section

variable {α : Type u} {A B : Formula α} {l : List (Formula α)}

/-- The conjunction of a list of formulas; `⊤` for the empty list and the formula itself for a
singleton. -/
def conj : List (Formula α) → Formula α
  | [] => ⊤
  | [A] => A
  | A :: B :: l => A ⋏ conj (B :: l)

/-- The disjunction of a list of formulas; `⊥` for the empty list and the formula itself for a
singleton. -/
def disj : List (Formula α) → Formula α
  | [] => ⊥
  | [A] => A
  | A :: B :: l => A ⋎ disj (B :: l)

@[simp, grind =] lemma conj_nil : conj ([] : List (Formula α)) = ⊤ := rfl
@[simp, grind =] lemma conj_singleton : conj [A] = A := rfl
@[simp, grind =] lemma conj_cons_cons : conj (A :: B :: l) = A ⋏ conj (B :: l) := rfl
@[simp, grind =] lemma disj_nil : disj ([] : List (Formula α)) = ⊥ := rfl
@[simp, grind =] lemma disj_singleton : disj [A] = A := rfl
@[simp, grind =] lemma disj_cons_cons : disj (A :: B :: l) = A ⋎ disj (B :: l) := rfl

lemma conj_cons_of_ne_nil (h : l ≠ []) : conj (A :: l) = A ⋏ conj l := by
  obtain ⟨B, l, rfl⟩ := List.exists_cons_of_ne_nil h;
  exact conj_cons_cons

lemma disj_cons_of_ne_nil (h : l ≠ []) : disj (A :: l) = A ⋎ disj l := by
  obtain ⟨B, l, rfl⟩ := List.exists_cons_of_ne_nil h;
  exact disj_cons_cons

end

end Formula

end Propositional

end
