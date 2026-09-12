module

public import Mathlib.Data.Finset.Basic

@[expose] public section

/-- Formulas of propositional modal logic. -/
inductive Formula (α : Type u) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | dia  : Formula α → Formula α
  deriving DecidableEq

abbrev FormulaSet (α : Type u) := Set (Formula α)

abbrev FormulaFinset (α : Type u) := Finset (Formula α)

namespace Formula

variable {α : Type u} {n : ℕ} {A A₁ A₂ B B₁ B₂ : Formula α}

instance : Bot (Formula α) := ⟨falsum⟩

prefix:max "#" => Formula.atom
infixr:60 " 🡒 " => Formula.imp
prefix:95 "◇" => dia

@[match_pattern] abbrev neg (A : Formula α) : Formula α := imp A ⊥
prefix:75 "∼" => Formula.neg

@[match_pattern] abbrev verum : Formula α := neg ⊥

instance : Top (Formula α) := ⟨verum⟩

@[match_pattern] abbrev or (A B : Formula α) : Formula α := ∼A 🡒 B
infixr:68 " ⋎ " => Formula.or

@[match_pattern] abbrev and (A B : Formula α) : Formula α := ∼(A 🡒 ∼B)
infixr:69 " ⋏ " => Formula.and

@[match_pattern]
abbrev box (A : Formula α) : Formula α := ∼◇(∼A)
prefix:95 "□" => box

@[match_pattern] abbrev iff (A B : Formula α) : Formula α := (A 🡒 B) ⋏ (B 🡒 A)
infix:61 " 🡘 " => Formula.iff

end Formula


namespace Formula

variable {α : Type u} {n : ℕ} {A A₁ A₂ B B₁ B₂ : Formula α}

@[grind =] lemma eq_verum_neg_falsum : ⊤ = ∼(⊥ : Formula α) := rfl

lemma falsum_eq : (⊥ : Formula α) = falsum := rfl
lemma verum_eq : (⊤ : Formula α) = verum := rfl
lemma iff_eq : A 🡘 B = (A 🡒 B) ⋏ (B 🡒 A) := rfl
attribute [grind =_] falsum_eq verum_eq iff_eq

@[grind =] lemma inj_and : A₁ ⋏ A₂ = B₁ ⋏ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp [and]
@[grind =] lemma inj_or : A₁ ⋎ A₂ = B₁ ⋎ B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp [or]
@[grind =] lemma inj_imp : A₁ 🡒 A₂ = B₁ 🡒 B₂ ↔ A₁ = B₁ ∧ A₂ = B₂ := by simp
@[grind =] lemma inj_neg : ∼A = ∼B ↔ A = B := by simp [neg]
@[grind =] lemma inj_box : □A = □B ↔ A = B := by simp
@[grind =] lemma inj_dia : ◇A = ◇B ↔ A = B := by simp

/-- Formula complexity. -/
@[grind =]
def complexity : Formula α → ℕ
  | atom _ => 0
  | ⊥      => 0
  | A 🡒 B  => max A.complexity B.complexity + 1
  | ◇A     => A.complexity + 1

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a, C (atom a))
    (himp : ∀ A B, C (A 🡒 B))
    (hdia : ∀ A, C (◇A))
    : (A : Formula α) → C A
  | ⊥      => hfalsum
  | atom a => hatom a
  | ◇A     => hdia A
  | A 🡒 B  => himp A B

@[induction_eliminator]
def rec' {C : Formula α → Sort w}
    (falsum : C ⊥)
    (atom : ∀ a, C (atom a))
    (imp : ∀ A B, C A → C B → C (A 🡒 B))
    (dia : ∀ A, C A → C (◇A))
    : (A : Formula α) → C A
  | ⊥      => falsum
  | #a => atom a
  | A 🡒 B  => imp A B (rec' falsum atom imp dia A) (rec' falsum atom imp dia B)
  | ◇A     => dia A (rec' falsum atom imp dia A)

/-- Iterated `□`. -/
abbrev multibox (n : ℕ) : Formula α → Formula α := (□·)^[n]
notation:76 "□^[" n "]" A:80 => Formula.multibox n A

/-- Iterated `◇`. -/
abbrev multidia (n : ℕ) : Formula α → Formula α := (◇·)^[n]
notation:76 "◇^[" n "]" A:80 => Formula.multidia n A

@[simp, grind =] lemma multibox_zero : (□^[0]A) = A := rfl
@[simp, grind =] lemma multibox_succ : (□^[n + 1]A) = □(□^[n]A) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multibox_add {m : ℕ} : (□^[n](□^[m]A)) = □^[n + m]A :=
  (Function.iterate_add_apply _ n m A).symm

@[simp, grind =] lemma multidia_zero : (◇^[0]A) = A := rfl
@[simp, grind =] lemma multidia_succ : (◇^[n + 1]A) = ◇(◇^[n]A) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multidia_add {m : ℕ} : (◇^[n](◇^[m]A)) = ◇^[n + m]A :=
  (Function.iterate_add_apply _ n m A).symm

end Formula

end
