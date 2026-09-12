module

public import BlokDichotomy.Formula.Basic
public import BlokDichotomy.Formula.Substitution
public import Mathlib.Order.SetNotation

@[expose]
public section

variable {α : Type v}

inductive FormulaSet.normalClosure (X : FormulaSet α) : FormulaSet α
| mem {A} : A ∈ X → normalClosure X A
| mdp {A B} : (normalClosure X A) → (normalClosure X (A 🡒 B)) → normalClosure X B
| nec {A} : normalClosure X A → normalClosure X (□A)
| subst {A σ} : normalClosure X A → normalClosure X (A⟦σ⟧)

structure NormalLogic (α : Type*) where
  carrier : FormulaSet α
  mdp {A B} : A ∈ carrier → (A 🡒 B) ∈ carrier → B ∈ carrier
  nec {A} : A ∈ carrier → □A ∈ carrier
  subst {A σ} : A ∈ carrier → (A⟦σ⟧) ∈ carrier
alias ExtK := NormalLogic

namespace Logic

def ofSet (X : FormulaSet α) : NormalLogic α where
  carrier := X.normalClosure
  mdp := FormulaSet.normalClosure.mdp
  nec := FormulaSet.normalClosure.nec
  subst := FormulaSet.normalClosure.subst

def inter (L₁ L₂ : NormalLogic α) : NormalLogic α where
  carrier := L₁.carrier ∩ L₂.carrier
  mdp := by
    rintro A B ⟨hA₁, hA₂⟩ ⟨hAB₁, hAB₂⟩;
    constructor;
    . exact L₁.mdp hA₁ hAB₁;
    . exact L₂.mdp hA₂ hAB₂;
  nec := by
    rintro A ⟨hA₁, hA₂⟩;
    constructor;
    . exact L₁.nec hA₁;
    . exact L₂.nec hA₂;
  subst := by
    rintro A σ ⟨hA₁, hA₂⟩;
    constructor;
    . exact L₁.subst hA₁;
    . exact L₂.subst hA₂;
instance : Inter (NormalLogic α) := ⟨inter⟩
instance : SupSet (NormalLogic α) where
  sSup F := ofSet $ Set.sUnion ((·.carrier) '' F)

def oplus (L₁ L₂ : NormalLogic α) : NormalLogic α := ofSet (L₁.carrier ∪ L₂.carrier)

end Logic


abbrev LogicK : NormalLogic α := SupSet.sSup Set.univ


structure ExtK4 (α : Type*) extends NormalLogic α where
  mem_4 {A} : □A 🡒 □□A ∈ carrier



end
