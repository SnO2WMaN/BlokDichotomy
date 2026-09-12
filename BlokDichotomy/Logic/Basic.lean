module

public import BlokDichotomy.Formula.Basic
public import BlokDichotomy.Formula.Substitution
public import Mathlib.Order.SetNotation
public import Mathlib.Data.SetLike.Basic

@[expose]
public section

variable {α : Type v}

inductive FormulaSet.normalClosure (X : FormulaSet α) : FormulaSet α
| mem {A} : A ∈ X → normalClosure X A
| mdp {A B} : (normalClosure X A) → (normalClosure X (A 🡒 B)) → normalClosure X B
| nec {A} : normalClosure X A → normalClosure X (□A)
| subst {A σ} : normalClosure X A → normalClosure X (A⟦σ⟧)

/-- Axiom schemes of `K`: classical propositional calculus plus the distribution axiom. -/
inductive FormulaSet.axiomsK : FormulaSet α
| imply₁ {A B}     : axiomsK $ A 🡒 B 🡒 A
| imply₂ {A B C}   : axiomsK $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| dne {A}          : axiomsK $ ∼∼A 🡒 A
| distribute {A B} : axiomsK $ □(A 🡒 B) 🡒 □A 🡒 □B

structure NormalLogic (α : Type*) where
  carrier : FormulaSet α
  mdp {A B} : A ∈ carrier → (A 🡒 B) ∈ carrier → B ∈ carrier
  nec {A} : A ∈ carrier → □A ∈ carrier
  subst {A σ} : A ∈ carrier → (A⟦σ⟧) ∈ carrier
alias ExtK := NormalLogic

namespace NormalLogic

instance : SetLike (NormalLogic α) (Formula α) where
  coe L := L.carrier
  coe_injective := by rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ rfl; rfl

instance : PartialOrder (NormalLogic α) := PartialOrder.ofSetLike _ _

variable {L L₁ L₂ : NormalLogic α} {X Y : FormulaSet α} {A B : Formula α}

@[simp, grind =] lemma mem_carrier : A ∈ L.carrier ↔ A ∈ L := Iff.rfl
@[simp, grind =] lemma coe_carrier : (L : FormulaSet α) = L.carrier := rfl

@[grind →] lemma mem_mdp : A ∈ L → (A 🡒 B) ∈ L → B ∈ L := L.mdp
@[grind →] lemma mem_nec : A ∈ L → □A ∈ L := L.nec
lemma mem_subst {σ : Formula.Substitution α α} : A ∈ L → (A⟦σ⟧) ∈ L := L.subst

@[grind =] lemma le_iff : L₁ ≤ L₂ ↔ ∀ A ∈ L₁, A ∈ L₂ := Iff.rfl

def ofSet (X : FormulaSet α) : NormalLogic α where
  carrier := X.normalClosure
  mdp := FormulaSet.normalClosure.mdp
  nec := FormulaSet.normalClosure.nec
  subst := FormulaSet.normalClosure.subst

@[grind →] lemma mem_ofSet (h : A ∈ X) : A ∈ ofSet X := FormulaSet.normalClosure.mem h

/-- `ofSet X` is the least normal logic containing `X`. -/
lemma ofSet_le (h : ∀ A ∈ X, A ∈ L) : ofSet X ≤ L := by
  rintro A hA;
  induction hA with
  | mem h' => exact h _ h';
  | mdp _ _ ihA ihAB => exact L.mdp ihA ihAB;
  | nec _ ih => exact L.nec ih;
  | subst _ ih => exact L.subst ih;

@[gcongr]
lemma ofSet_mono (h : X ⊆ Y) : ofSet X ≤ ofSet Y := ofSet_le fun _ hA => mem_ofSet (h hA)

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

def oadd (L : NormalLogic α) (X : FormulaSet α) := ofSet (L.carrier ∪ X)

lemma mem_oadd_of_mem (h : A ∈ L) : A ∈ L.oadd X := mem_ofSet (Or.inl h)
lemma le_oadd : L ≤ L.oadd X := fun _ hA => mem_oadd_of_mem hA
lemma mem_oadd (h : A ∈ X) : A ∈ L.oadd X := mem_ofSet (Or.inr h)

@[gcongr]
lemma oadd_mono (hL : L₁ ≤ L₂) (hX : X ⊆ Y) : L₁.oadd X ≤ L₂.oadd Y :=
  ofSet_mono $ Set.union_subset_union hL hX

lemma oadd_le (hL : L₁ ≤ L₂) (hX : ∀ A ∈ X, A ∈ L₂) : L₁.oadd X ≤ L₂ := by
  apply ofSet_le;
  rintro A (hA | hA);
  . exact hL hA;
  . exact hX _ hA;

def Consistent (L : NormalLogic α) := L.carrier ≠ Set.univ

lemma consistent_iff : L.Consistent ↔ ∃ A : Formula α, A ∉ L := by
  unfold Consistent;
  simp [Set.eq_univ_iff_forall.not]

lemma Consistent.of_le (h : L₁ ≤ L₂) (h₂ : L₂.Consistent) : L₁.Consistent := by
  obtain ⟨A, hA⟩ := consistent_iff.mp h₂;
  exact consistent_iff.mpr ⟨A, fun hA₁ => hA $ h hA₁⟩;

end NormalLogic


abbrev logicK : NormalLogic α := NormalLogic.ofSet FormulaSet.axiomsK


structure ExtK4 (α : Type*) extends NormalLogic α where
  mem_4 {A} : □A 🡒 □□A ∈ carrier

end
