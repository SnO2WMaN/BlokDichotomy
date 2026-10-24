module

public import BlokDichotomy.Propositional.Formula
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Superintuitionistic logics

Sets of formulas closed under modus ponens and substitution, the intuitionistic logic `𝐈𝐧𝐭`,
derivability from hypotheses (deduction theorem, compactness), and derived rules.

## References

- [CZ98, §2.6, §4.1]
-/

@[expose] public section

universe v

namespace Propositional

variable {α : Type v}

inductive FormulaSet.closure (X : FormulaSet α) : FormulaSet α
| mem {A} : A ∈ X → closure X A
| mdp {A B} : closure X A → closure X (A 🡒 B) → closure X B
| subst {A s} : closure X A → closure X (A⟦s⟧)

/-- A set of formulas closed under modus ponens and substitution; it is a superintuitionistic
logic when it moreover contains `𝐈𝐧𝐭` (`IsExt L 𝐈𝐧𝐭`).
- [CZ98, §4.1] -/
structure Logic (α : Type*) where
  carrier : FormulaSet α
  mdp {A B} : A ∈ carrier → A 🡒 B ∈ carrier → B ∈ carrier
  subst {A s} : A ∈ carrier → A⟦s⟧ ∈ carrier

namespace Logic

instance : SetLike (Logic α) (Formula α) where
  coe L := L.carrier
  coe_injective := by rintro ⟨_, _, _⟩ ⟨_, _, _⟩ rfl; rfl

instance : PartialOrder (Logic α) := PartialOrder.ofSetLike _

variable {L L₀ : Logic α} {X : FormulaSet α} {A B : Formula α}

@[simp, grind =] lemma mem_carrier : A ∈ L.carrier ↔ A ∈ L := Iff.rfl

@[grind →] lemma mem_mdp : A ∈ L → A 🡒 B ∈ L → B ∈ L := L.mdp
@[grind <=] lemma mem_subst {s : Formula.Substitution α α} : A ∈ L → A⟦s⟧ ∈ L := L.subst

def ofSet (X : FormulaSet α) : Logic α where
  carrier := X.closure
  mdp := .mdp
  subst := .subst

@[grind →] lemma mem_ofSet (h : A ∈ X) : A ∈ ofSet X := FormulaSet.closure.mem h

/-- `ofSet X` is the least logic containing `X`. -/
lemma ofSet_le (h : ∀ A ∈ X, A ∈ L) : ofSet X ≤ L := by
  intro A hA;
  induction hA with
  | mem h' => exact h _ h';
  | mdp _ _ ih₁ ih₂ => exact L.mdp ih₁ ih₂;
  | subst _ ih => exact L.subst ih;

/-- `L` extends `L₀`. -/
class IsExt (L L₀ : Logic α) : Prop where
  logic_le : L₀ ≤ L

instance : L.IsExt L := ⟨le_rfl⟩

/-- The extensions of `L₀`, ordered by inclusion. The superintuitionistic logics are `Ext 𝐈𝐧𝐭`. -/
abbrev _root_.Propositional.Ext (L₀ : Logic α) : Type v := {L : Logic α // L.IsExt L₀}

instance (L₀ : Logic α) (L : Ext L₀) : L.1.IsExt L₀ := L.2

end Logic

inductive axiomsInt : FormulaSet α
| imply₁ {A B}   : axiomsInt <| A 🡒 B 🡒 A
| imply₂ {A B C} : axiomsInt <| (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| andElim₁ {A B} : axiomsInt <| A ⋏ B 🡒 A
| andElim₂ {A B} : axiomsInt <| A ⋏ B 🡒 B
| andIntro {A B} : axiomsInt <| A 🡒 B 🡒 A ⋏ B
| orIntro₁ {A B} : axiomsInt <| A 🡒 A ⋎ B
| orIntro₂ {A B} : axiomsInt <| B 🡒 A ⋎ B
| orElim {A B C} : axiomsInt <| (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C)
| efq {A}        : axiomsInt <| ⊥ 🡒 A

abbrev logicInt : Logic α := Logic.ofSet axiomsInt
notation "𝐈𝐧𝐭" => logicInt

namespace Logic

/-- `Γ ⊢[L] A`: `A` is derivable from `Γ` using the theorems of `L` and modus ponens. -/
inductive Derives (L : Logic α) (Γ : FormulaSet α) : Formula α → Prop
  | mem {A} : A ∈ Γ → Derives L Γ A
  | thm {A} : A ∈ L → Derives L Γ A
  | mdp {A B} : Derives L Γ A → Derives L Γ (A 🡒 B) → Derives L Γ B
attribute [grind .] Derives.mem Derives.thm
attribute [grind →] Derives.mdp
scoped[Propositional] notation:50 Γ:51 " ⊢[" L "] " A:60 => Logic.Derives L Γ A

abbrev NotDerives (L : Logic α) (Γ : FormulaSet α) (A : Formula α) : Prop := ¬ Γ ⊢[L] A

scoped[Propositional] notation:50 Γ:51 " ⊬[" L "] " A:60 => Logic.NotDerives L Γ A

variable {L : Logic α} {Γ Δ : FormulaSet α} {A B C : Formula α}

namespace Derives

lemma mono (hΓ : Γ ⊆ Δ) (h : Γ ⊢[L] A) : Δ ⊢[L] A := by
  induction h <;> grind;

lemma of_imp_mem (h : A 🡒 B ∈ L) (hA : Γ ⊢[L] A) : Γ ⊢[L] B := mdp hA <| thm h

@[simp]
lemma empty_iff : ∅ ⊢[L] A ↔ A ∈ L where
  mp h := by
    induction h <;> grind;
  mpr := thm

/-- Compactness. -/
lemma exists_finite (h : Γ ⊢[L] A) : ∃ Δ ⊆ Γ, Δ.Finite ∧ Δ ⊢[L] A := by
  induction h with
  | @mem A h => exact ⟨{A}, by simpa using h, Set.finite_singleton A, mem rfl⟩;
  | thm h => exact ⟨∅, Set.empty_subset _, Set.finite_empty, thm h⟩;
  | mdp _ _ ihA ihAB =>
    obtain ⟨Δ₁, h₁, f₁, d₁⟩ := ihA;
    obtain ⟨Δ₂, h₂, f₂, d₂⟩ := ihAB;
    exact ⟨Δ₁ ∪ Δ₂, Set.union_subset h₁ h₂, f₁.union f₂,
      mdp (d₁.mono Set.subset_union_left) (d₂.mono Set.subset_union_right)⟩;

end Derives

section Reasoning

variable [L.IsExt 𝐈𝐧𝐭]

lemma mem_of_mem_logicInt (h : A ∈ 𝐈𝐧𝐭) : A ∈ L := IsExt.logic_le h

lemma imply₁ : A 🡒 B 🡒 A ∈ L := mem_of_mem_logicInt <| mem_ofSet .imply₁
lemma imply₂ : (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) ∈ L := mem_of_mem_logicInt <| mem_ofSet .imply₂
lemma andElim₁ : A ⋏ B 🡒 A ∈ L := mem_of_mem_logicInt <| mem_ofSet .andElim₁
lemma andElim₂ : A ⋏ B 🡒 B ∈ L := mem_of_mem_logicInt <| mem_ofSet .andElim₂
lemma andIntro : A 🡒 B 🡒 A ⋏ B ∈ L := mem_of_mem_logicInt <| mem_ofSet .andIntro
lemma orIntro₁ : A 🡒 A ⋎ B ∈ L := mem_of_mem_logicInt <| mem_ofSet .orIntro₁
lemma orIntro₂ : B 🡒 A ⋎ B ∈ L := mem_of_mem_logicInt <| mem_ofSet .orIntro₂
lemma orElim : (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C) ∈ L := mem_of_mem_logicInt <| mem_ofSet .orElim
lemma efq : ⊥ 🡒 A ∈ L := mem_of_mem_logicInt <| mem_ofSet .efq

lemma imp_self : A 🡒 A ∈ L :=
  mem_mdp (imply₁ (B := A)) <| mem_mdp imply₁ imply₂

namespace Derives

/-- The deduction theorem.
- [CZ98, Theorem 2.42] -/
lemma deduction (h : insert A Γ ⊢[L] B) : Γ ⊢[L] A 🡒 B := by
  induction h with
  | mem h =>
    rcases h with rfl | h;
    · exact thm imp_self;
    · exact of_imp_mem imply₁ <| mem h;
  | thm h => exact of_imp_mem imply₁ <| thm h;
  | mdp _ _ ihA ihAB => exact mdp ihA <| mdp ihAB <| thm imply₂;

lemma deduction_iff : insert A Γ ⊢[L] B ↔ Γ ⊢[L] A 🡒 B :=
  ⟨deduction, fun h => mdp (mem <| Set.mem_insert A Γ) <| h.mono <| Set.subset_insert A Γ⟩

lemma efq (h : Γ ⊢[L] ⊥) : Γ ⊢[L] A := of_imp_mem Logic.efq h

lemma and_intro (h₁ : Γ ⊢[L] A) (h₂ : Γ ⊢[L] B) : Γ ⊢[L] A ⋏ B :=
  mdp h₂ <| mdp h₁ <| thm andIntro

lemma and_left (h : Γ ⊢[L] A ⋏ B) : Γ ⊢[L] A := of_imp_mem andElim₁ h

lemma and_right (h : Γ ⊢[L] A ⋏ B) : Γ ⊢[L] B := of_imp_mem andElim₂ h

lemma or_inl (h : Γ ⊢[L] A) : Γ ⊢[L] A ⋎ B := of_imp_mem orIntro₁ h

lemma or_inr (h : Γ ⊢[L] B) : Γ ⊢[L] A ⋎ B := of_imp_mem orIntro₂ h

lemma or_elim (h : Γ ⊢[L] A ⋎ B) (h₁ : insert A Γ ⊢[L] C) (h₂ : insert B Γ ⊢[L] C) :
    Γ ⊢[L] C := by
  have h₃ : Γ ⊢[L] A ⋎ B 🡒 C :=
    mdp (deduction h₂) <| mdp (deduction h₁) <| thm orElim;
  exact mdp h h₃;

end Derives

end Reasoning

end Logic

end Propositional

end
