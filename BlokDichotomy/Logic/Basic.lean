module

public import BlokDichotomy.Formula
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.SetNotation

/-!
# Normal logics

Normal logics, the smallest normal logic `𝐊`, normal extensions, derivability from hypotheses
(deduction theorem, compactness), and derived propositional and modal rules.

## References

- [CZ98, §4.1, Theorem 1.12, Theorem 1.16, Theorem 1.19, §3.7]
-/

@[expose] public section

universe v

variable {α : Type v}

inductive FormulaSet.normalClosure (X : FormulaSet α) : FormulaSet α
| mem {φ} : φ ∈ X → normalClosure X φ
| mdp {φ ψ} : normalClosure X φ → normalClosure X (φ 🡒 ψ) → normalClosure X ψ
| nec {φ} : normalClosure X φ → normalClosure X (□φ)
| subst {φ s} : normalClosure X φ → normalClosure X (φ⟦s⟧)

structure NormalLogic (α : Type*) where
  carrier : FormulaSet α
  mdp {φ ψ} : φ ∈ carrier → φ 🡒 ψ ∈ carrier → ψ ∈ carrier
  nec {φ} : φ ∈ carrier → □φ ∈ carrier
  subst {φ s} : φ ∈ carrier → φ⟦s⟧ ∈ carrier

namespace NormalLogic

instance : SetLike (NormalLogic α) (Formula α) where
  coe L := L.carrier
  coe_injective := by rintro ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ rfl; rfl

instance : PartialOrder (NormalLogic α) := PartialOrder.ofSetLike _

variable {L L₁ L₂ : NormalLogic α} {X Y : FormulaSet α} {φ ψ : Formula α} {n : ℕ}

@[simp, grind =] lemma mem_carrier : φ ∈ L.carrier ↔ φ ∈ L := Iff.rfl
@[simp, grind =] lemma coe_carrier : (L : FormulaSet α) = L.carrier := rfl

@[grind →] lemma mem_mdp : φ ∈ L → φ 🡒 ψ ∈ L → ψ ∈ L := L.mdp
@[grind →] lemma mem_nec : φ ∈ L → □φ ∈ L := L.nec
lemma mem_subst {s : Formula.Substitution α α} : φ ∈ L → φ⟦s⟧ ∈ L := L.subst

lemma multibox_mem (h : φ ∈ L) : □^[n]φ ∈ L := by
  induction n with
  | zero => exact h;
  | succ n ih => simpa using mem_nec ih;

@[grind =] lemma le_iff : L₁ ≤ L₂ ↔ ∀ φ ∈ L₁, φ ∈ L₂ := Iff.rfl

def ofSet (X : FormulaSet α) : NormalLogic α where
  carrier := X.normalClosure
  mdp := .mdp
  nec := .nec
  subst := .subst

@[grind →] lemma mem_ofSet (h : φ ∈ X) : φ ∈ ofSet X := FormulaSet.normalClosure.mem h

/-- `ofSet X` is the least normal logic containing `X`. -/
lemma ofSet_le (h : ∀ φ ∈ X, φ ∈ L) : ofSet X ≤ L := by
  intro φ hφ;
  induction hφ with
  | mem h' => exact h _ h';
  | mdp _ _ ih₁ ih₂ => exact L.mdp ih₁ ih₂;
  | nec _ ih => exact L.nec ih;
  | subst _ ih => exact L.subst ih;

@[gcongr]
lemma ofSet_mono (h : X ⊆ Y) : ofSet X ≤ ofSet Y := ofSet_le fun _ hA => mem_ofSet (h hA)

def inter (L₁ L₂ : NormalLogic α) : NormalLogic α where
  carrier := L₁.carrier ∩ L₂.carrier
  mdp := fun ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => ⟨L₁.mdp h₁ h₃, L₂.mdp h₂ h₄⟩
  nec := fun ⟨h₁, h₂⟩ => ⟨L₁.nec h₁, L₂.nec h₂⟩
  subst := fun ⟨h₁, h₂⟩ => ⟨L₁.subst h₁, L₂.subst h₂⟩

instance : Inter (NormalLogic α) := ⟨inter⟩

instance : SupSet (NormalLogic α) where
  sSup F := ofSet <| Set.sUnion ((·.carrier) '' F)

instance : HAdd (NormalLogic α) (FormulaSet α) (NormalLogic α) := ⟨fun L X => ofSet (L.carrier ∪ X)⟩

/-- The join of two normal logics. -/
instance : Add (NormalLogic α) := ⟨fun L₁ L₂ => L₁ + L₂.carrier⟩

lemma mem_add_of_mem (h : φ ∈ L) : φ ∈ L + X := mem_ofSet (Or.inl h)
lemma le_add : L ≤ L + X := fun _ hA => mem_add_of_mem hA
lemma mem_add (h : φ ∈ X) : φ ∈ L + X := mem_ofSet (Or.inr h)

lemma add_mono (hL : L₁ ≤ L₂) (hX : X ⊆ Y) : L₁ + X ≤ L₂ + Y :=
  ofSet_mono <| Set.union_subset_union hL hX

lemma add_le (hL : L₁ ≤ L₂) (hX : ∀ φ ∈ X, φ ∈ L₂) : (L₁ + X : NormalLogic α) ≤ L₂ :=
  ofSet_le <| by rintro φ (h | h) <;> grind

def Consistent (L : NormalLogic α) := L.carrier ≠ Set.univ

lemma consistent_iff : L.Consistent ↔ ∃ φ : Formula α, φ ∉ L := by
  unfold Consistent;
  simp [Set.eq_univ_iff_forall.not]

lemma Consistent.of_le (h : L₁ ≤ L₂) (h₂ : L₂.Consistent) : L₁.Consistent := by
  obtain ⟨φ, hφ⟩ := consistent_iff.mp h₂;
  exact consistent_iff.mpr ⟨φ, fun h₁ => hφ <| h h₁⟩;

end NormalLogic

/-- The axiom schemes of `𝐊`. -/
inductive FormulaSet.axiomsK : FormulaSet α
| imply₁ {φ ψ}     : axiomsK <| φ 🡒 ψ 🡒 φ
| imply₂ {φ ψ χ}   : axiomsK <| (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 (φ 🡒 χ)
| dne {φ}          : axiomsK <| ∼∼φ 🡒 φ
| distribute {φ ψ} : axiomsK <| □(φ 🡒 ψ) 🡒 □φ 🡒 □ψ
| diaDual {φ}      : axiomsK <| ◇φ 🡘 ∼□(∼φ)

/-- The smallest normal logic `𝐊`. -/
abbrev logicK : NormalLogic α := NormalLogic.ofSet FormulaSet.axiomsK
notation "𝐊" => logicK

/-- The normal logic `𝐊𝟒 = 𝐊 ⊕ □φ 🡒 □□φ`. -/
abbrev logicK4 : NormalLogic α :=
  (𝐊 : NormalLogic α) + {□φ 🡒 □□φ | (φ : Formula α)}
notation "𝐊𝟒" => logicK4

/-- The normal logic `𝐒𝟒 = 𝐊𝟒 ⊕ □φ 🡒 φ`. -/
abbrev logicS4 : NormalLogic α :=
  (𝐊𝟒 : NormalLogic α) + {□φ 🡒 φ | (φ : Formula α)}
notation "𝐒𝟒" => logicS4

namespace NormalLogic

/-- `L` is a normal extension of `L₀`. -/
class IsNExt (L L₀ : NormalLogic α) : Prop where
  logic_le : L₀ ≤ L

/-- `Γ ⊢[L] φ`: `φ` is derivable from `Γ` using the theorems of `L` and modus ponens, without
necessitation on hypotheses. -/
inductive Derives (L : NormalLogic α) (Γ : FormulaSet α) : Formula α → Prop
  | mem {φ} : φ ∈ Γ → Derives L Γ φ
  | thm {φ} : φ ∈ L → Derives L Γ φ
  | mdp {φ ψ} : Derives L Γ φ → Derives L Γ (φ 🡒 ψ) → Derives L Γ ψ

notation:50 Γ:51 " ⊢[" L "] " φ:60 => Derives L Γ φ

abbrev NotDerives (L : NormalLogic α) (Γ : FormulaSet α) (φ : Formula α) : Prop := ¬ Γ ⊢[L] φ

notation:50 Γ:51 " ⊬[" L "] " φ:60 => NotDerives L Γ φ

variable {L L₀ L₁ L₂ : NormalLogic α} {X : FormulaSet α} {Γ Δ : FormulaSet α}
  {φ ψ χ θ : Formula α} {l : List (Formula α)} {n : ℕ}

instance : L.IsNExt L := ⟨le_rfl⟩

instance [L₁.IsNExt L₀] [L₂.IsNExt L₀] : (L₁ ∩ L₂).IsNExt L₀ :=
  ⟨fun _ hA => ⟨IsNExt.logic_le hA, IsNExt.logic_le hA⟩⟩

instance [L.IsNExt L₀] : (L + X).IsNExt L₀ :=
  ⟨fun _ hA => le_add (IsNExt.logic_le hA)⟩

/-- `L` contains every formula. -/
def Inconsistent (L : NormalLogic α) : Prop := ¬L.Consistent

lemma inconsistent_iff : L.Inconsistent ↔ ∀ φ : Formula α, φ ∈ L := by
  simp [Inconsistent, consistent_iff]

lemma not_inconsistent_iff : ¬L.Inconsistent ↔ L.Consistent := not_not

namespace Inconsistent

lemma mem (h : L.Inconsistent) (φ : Formula α) : φ ∈ L := inconsistent_iff.mp h φ

lemma isNExt (h : L.Inconsistent) : L.IsNExt L₀ := ⟨fun φ _ => h.mem φ⟩

end Inconsistent

lemma mdp₂ (h : φ 🡒 ψ 🡒 χ ∈ L) (hA : φ ∈ L) (hB : ψ ∈ L) : χ ∈ L :=
  mem_mdp hB <| mem_mdp hA h

namespace Derives

lemma mono (hΓ : Γ ⊆ Δ) (h : Γ ⊢[L] φ) : Δ ⊢[L] φ := by
  induction h with
  | mem h => exact mem <| hΓ h;
  | thm h => exact thm h;
  | mdp _ _ ihφ ihφψ => exact mdp ihφ ihφψ;

lemma mdp₂ (h : Γ ⊢[L] φ 🡒 ψ 🡒 χ) (hA : Γ ⊢[L] φ) (hB : Γ ⊢[L] ψ) : Γ ⊢[L] χ :=
  mdp hB <| mdp hA h

lemma of_imp_mem (h : φ 🡒 ψ ∈ L) (hA : Γ ⊢[L] φ) : Γ ⊢[L] ψ := mdp hA <| thm h

lemma neg_elim (h₁ : Γ ⊢[L] φ) (h₂ : Γ ⊢[L] ∼φ) : Γ ⊢[L] ⊥ := mdp h₁ h₂

@[simp]
lemma empty_iff : ∅ ⊢[L] φ ↔ φ ∈ L where
  mp h := by
    induction h with
    | mem h => exact h.elim;
    | thm h => exact h;
    | mdp _ _ ihφ ihφψ => exact L.mdp ihφ ihφψ;
  mpr := thm

/--
Compactness.
- [CZ98, Theorem 1.19]
-/
lemma exists_finite (h : Γ ⊢[L] φ) : ∃ Δ ⊆ Γ, Δ.Finite ∧ Δ ⊢[L] φ := by
  induction h with
  | @mem φ h => exact ⟨{φ}, by simpa using h, Set.finite_singleton φ, mem rfl⟩;
  | thm h => exact ⟨∅, Set.empty_subset _, Set.finite_empty, thm h⟩;
  | mdp _ _ ihφ ihφψ =>
    obtain ⟨Δ₁, h₁, f₁, d₁⟩ := ihφ;
    obtain ⟨Δ₂, h₂, f₂, d₂⟩ := ihφψ;
    exact ⟨Δ₁ ∪ Δ₂, Set.union_subset h₁ h₂, f₁.union f₂,
      mdp (d₁.mono Set.subset_union_left) (d₂.mono Set.subset_union_right)⟩;

lemma trans (hΓ : ∀ ψ ∈ Γ, Δ ⊢[L] ψ) (h : Γ ⊢[L] φ) : Δ ⊢[L] φ := by
  induction h with
  | mem h => exact hΓ _ h;
  | thm h => exact thm h;
  | mdp _ _ ihφ ihφψ => exact mdp ihφ ihφψ;

end Derives

section Reasoning

variable [L.IsNExt 𝐊]

lemma mem_of_mem_logicK (h : φ ∈ 𝐊) : φ ∈ L := IsNExt.logic_le h

lemma imply₁ : φ 🡒 ψ 🡒 φ ∈ L := mem_of_mem_logicK <| mem_ofSet .imply₁
lemma imply₂ : (φ 🡒 ψ 🡒 χ) 🡒 (φ 🡒 ψ) 🡒 (φ 🡒 χ) ∈ L := mem_of_mem_logicK <| mem_ofSet .imply₂
lemma dne : ∼∼φ 🡒 φ ∈ L := mem_of_mem_logicK <| mem_ofSet .dne
lemma distribute : □(φ 🡒 ψ) 🡒 □φ 🡒 □ψ ∈ L := mem_of_mem_logicK <| mem_ofSet .distribute
lemma diaDual : ◇φ 🡘 ∼□(∼φ) ∈ L := mem_of_mem_logicK <| mem_ofSet .diaDual

lemma imp_self : φ 🡒 φ ∈ L := mem_mdp (imply₁ (ψ := φ)) <| mem_mdp imply₁ imply₂

lemma imp_of_mem (h : ψ ∈ L) : φ 🡒 ψ ∈ L := mem_mdp h imply₁

lemma imp_trans (h₁ : φ 🡒 ψ ∈ L) (h₂ : ψ 🡒 χ ∈ L) : φ 🡒 χ ∈ L :=
  mem_mdp h₁ <| mem_mdp (imp_of_mem h₂) imply₂

lemma efq : ⊥ 🡒 φ ∈ L := imp_trans imply₁ dne

lemma consistent_iff_bot_not_mem : L.Consistent ↔ ⊥ ∉ L := by
  rw [consistent_iff];
  exact ⟨fun ⟨φ, hφ⟩ hbot => hφ <| mem_mdp hbot efq, fun h => ⟨⊥, h⟩⟩;

namespace Derives

/--
The deduction theorem.
- [CZ98, Theorem 1.12]
-/
lemma deduction (h : insert φ Γ ⊢[L] ψ) : Γ ⊢[L] φ 🡒 ψ := by
  induction h with
  | mem h =>
    rcases h with rfl | h;
    · exact thm imp_self;
    · exact of_imp_mem imply₁ <| mem h;
  | thm h => exact thm <| imp_of_mem h;
  | mdp _ _ ihφ ihφψ => exact mdp₂ (thm imply₂) ihφψ ihφ;

lemma deduction_iff : insert φ Γ ⊢[L] ψ ↔ Γ ⊢[L] φ 🡒 ψ :=
  ⟨deduction, fun h => mdp (mem <| Set.mem_insert φ Γ) <| h.mono <| Set.subset_insert φ Γ⟩

lemma cut (hA : Γ ⊢[L] φ) (hB : insert φ Γ ⊢[L] ψ) : Γ ⊢[L] ψ :=
  mdp hA <| deduction hB

lemma efq (h : Γ ⊢[L] ⊥) : Γ ⊢[L] φ := of_imp_mem NormalLogic.efq h

lemma by_contra (h : insert (∼φ) Γ ⊢[L] ⊥) : Γ ⊢[L] φ := of_imp_mem dne (deduction h)

lemma and_left (h : Γ ⊢[L] φ ⋏ ψ) : Γ ⊢[L] φ := by
  apply Derives.by_contra;
  apply neg_elim (φ := φ 🡒 ∼ψ);
  · apply deduction;
    apply Derives.efq;
    exact neg_elim (φ := φ) (mem <| by simp) (mem <| by simp);
  · exact h.mono <| Set.subset_insert _ _;

lemma and_right (h : Γ ⊢[L] φ ⋏ ψ) : Γ ⊢[L] ψ := by
  apply Derives.by_contra;
  apply neg_elim (φ := φ 🡒 ∼ψ);
  · exact deduction <| mem <| by simp;
  · exact h.mono <| Set.subset_insert _ _;

lemma and_intro (h₁ : Γ ⊢[L] φ) (h₂ : Γ ⊢[L] ψ) : Γ ⊢[L] φ ⋏ ψ := by
  apply deduction;
  apply neg_elim (φ := ψ) (h₂.mono <| Set.subset_insert _ _);
  exact Derives.mdp (h₁.mono <| Set.subset_insert _ _) (mem <| by simp);

lemma or_inl (h : Γ ⊢[L] φ) : Γ ⊢[L] φ ⋎ ψ :=
  deduction <| Derives.efq <| neg_elim (φ := φ) (h.mono <| Set.subset_insert _ _) (mem <| by simp)

lemma or_inr (h : Γ ⊢[L] ψ) : Γ ⊢[L] φ ⋎ ψ := deduction <| h.mono <| Set.subset_insert _ _

lemma or_elim (hA : Γ ⊢[L] φ ⋎ ψ) (hB : insert φ Γ ⊢[L] χ) (hC : insert ψ Γ ⊢[L] χ) :
    Γ ⊢[L] χ := by
  apply Derives.by_contra;
  have hφ : insert (∼χ) Γ ⊢[L] ∼φ := by
    apply deduction;
    apply neg_elim (φ := χ);
    · exact hB.mono <| Set.insert_subset_insert <| Set.subset_insert _ _;
    · exact mem <| by simp;
  have hψ : insert (∼χ) Γ ⊢[L] ψ := Derives.mdp hφ <| hA.mono <| Set.subset_insert _ _;
  apply neg_elim (φ := χ) _ (mem <| by simp);
  exact cut hψ <| hC.mono <| Set.insert_subset_insert <| Set.subset_insert _ _;

end Derives

open Derives

lemma derives_imp_iff_mem : {φ} ⊢[L] ψ ↔ φ 🡒 ψ ∈ L := by
  rw [← empty_iff, ← deduction_iff, insert_empty_eq];

section Propositional

open Formula

lemma verum_mem : ⊤ ∈ L := imp_self

lemma dni : φ 🡒 ∼∼φ ∈ L :=
  empty_iff.mp <| deduction <| deduction <|
    neg_elim (φ := φ) (.mem <| by simp) (.mem <| by simp)

lemma contra : (φ 🡒 ψ) 🡒 ∼ψ 🡒 ∼φ ∈ L :=
  empty_iff.mp <| deduction <| deduction <| deduction <|
    neg_elim (φ := ψ) (.mdp (φ := φ) (.mem <| by simp) (.mem <| by simp))
      (.mem <| by simp)

lemma imp_comm : (φ 🡒 ψ 🡒 χ) 🡒 ψ 🡒 φ 🡒 χ ∈ L :=
  empty_iff.mp <| deduction <| deduction <| deduction <|
    .mdp (φ := ψ) (.mem <| by simp) (.mdp (φ := φ) (.mem <| by simp) (.mem <| by simp))

lemma imp_contract : (φ 🡒 φ 🡒 ψ) 🡒 φ 🡒 ψ ∈ L :=
  empty_iff.mp <| deduction <| deduction <|
    .mdp (φ := φ) (.mem <| by simp) (.mdp (φ := φ) (.mem <| by simp) (.mem <| by simp))

lemma syllogism : (φ 🡒 ψ) 🡒 (ψ 🡒 χ) 🡒 φ 🡒 χ ∈ L :=
  empty_iff.mp <| deduction <| deduction <| deduction <|
    .mdp (φ := ψ) (.mdp (φ := φ) (.mem <| by simp) (.mem <| by simp)) (.mem <| by simp)

lemma neg_efq : ∼φ 🡒 φ 🡒 ψ ∈ L :=
  empty_iff.mp <| deduction <| deduction <| Derives.efq <|
    neg_elim (φ := φ) (.mem <| by simp) (.mem <| by simp)

lemma and_left : φ ⋏ ψ 🡒 φ ∈ L :=
  derives_imp_iff_mem.mp <| Derives.and_left <| mem rfl

lemma and_right : φ ⋏ ψ 🡒 ψ ∈ L :=
  derives_imp_iff_mem.mp <| Derives.and_right <| mem rfl

lemma and_intro : φ 🡒 ψ 🡒 φ ⋏ ψ ∈ L :=
  empty_iff.mp <| deduction <| deduction <|
    Derives.and_intro (.mem <| by simp) (.mem <| by simp)

lemma or_left : φ 🡒 φ ⋎ ψ ∈ L :=
  empty_iff.mp <| deduction <| Derives.or_inl <| .mem <| by simp

lemma or_right : ψ 🡒 φ ⋎ ψ ∈ L :=
  empty_iff.mp <| deduction <| Derives.or_inr <| .mem <| by simp

lemma or_elim : (φ 🡒 χ) 🡒 (ψ 🡒 χ) 🡒 φ ⋎ ψ 🡒 χ ∈ L := by
  apply empty_iff.mp;
  repeat apply deduction;
  apply Derives.or_elim (φ := φ) (ψ := ψ) (.mem <| by simp);
  · exact .mdp (φ := φ) (.mem <| by simp) (.mem <| by simp);
  · exact .mdp (φ := ψ) (.mem <| by simp) (.mem <| by simp);

lemma lem : φ ⋎ ∼φ ∈ L := imp_self

lemma iff_intro : (φ 🡒 ψ) 🡒 (ψ 🡒 φ) 🡒 φ 🡘 ψ ∈ L :=
  empty_iff.mp <| deduction <| deduction <|
    Derives.and_intro (.mem <| by simp) (.mem <| by simp)

lemma iff_left : φ 🡘 ψ 🡒 φ 🡒 ψ ∈ L := and_left

lemma iff_right : φ 🡘 ψ 🡒 ψ 🡒 φ ∈ L := and_right

lemma imp_disj_of_mem (h : φ ∈ l) : φ 🡒 ⋁l ∈ L := by
  induction l with
  | nil => simp at h;
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h;
    · exact or_left;
    · exact imp_trans (ih h) or_right;

lemma conj_imp_of_mem (h : φ ∈ l) : ⋀l 🡒 φ ∈ L := by
  induction l with
  | nil => simp at h;
  | cons a l ih =>
    rcases List.mem_cons.mp h with rfl | h;
    · exact and_left;
    · exact imp_trans and_right (ih h);

lemma contrapose (h : φ 🡒 ψ ∈ L) : ∼ψ 🡒 ∼φ ∈ L := mem_mdp h contra

lemma of_contrapose (h : ∼ψ 🡒 ∼φ ∈ L) : φ 🡒 ψ ∈ L := by
  have key : (∼ψ 🡒 ∼φ) 🡒 φ 🡒 ψ ∈ L := by
    apply empty_iff.mp;
    repeat apply deduction;
    apply Derives.by_contra;
    exact neg_elim (φ := φ) (.mem <| by simp)
      (.mdp (φ := ∼ψ) (.mem <| by simp) (.mem <| by simp));
  exact mem_mdp h key

lemma imp_swap (h : φ 🡒 ψ 🡒 χ ∈ L) : ψ 🡒 φ 🡒 χ ∈ L := mem_mdp h imp_comm

lemma and_mem_iff : φ ⋏ ψ ∈ L ↔ φ ∈ L ∧ ψ ∈ L :=
  ⟨fun h => ⟨mem_mdp h and_left, mem_mdp h and_right⟩, fun h => mdp₂ and_intro h.1 h.2⟩

lemma iff_mem_iff : φ 🡘 ψ ∈ L ↔ φ 🡒 ψ ∈ L ∧ ψ 🡒 φ ∈ L := and_mem_iff

lemma iff_of_imp (h₁ : φ 🡒 ψ ∈ L) (h₂ : ψ 🡒 φ ∈ L) : φ 🡘 ψ ∈ L :=
  iff_mem_iff.mpr ⟨h₁, h₂⟩

lemma iff_mp (h : φ 🡘 ψ ∈ L) : φ 🡒 ψ ∈ L := (iff_mem_iff.mp h).1

lemma iff_mpr (h : φ 🡘 ψ ∈ L) : ψ 🡒 φ ∈ L := (iff_mem_iff.mp h).2

lemma iff_refl : φ 🡘 φ ∈ L := iff_of_imp imp_self imp_self

lemma neg_neg_iff : ∼∼φ 🡘 φ ∈ L := iff_of_imp dne dni

lemma iff_symm (h : φ 🡘 ψ ∈ L) : ψ 🡘 φ ∈ L := iff_of_imp (iff_mpr h) (iff_mp h)

lemma iff_trans (h₁ : φ 🡘 ψ ∈ L) (h₂ : ψ 🡘 χ ∈ L) : φ 🡘 χ ∈ L :=
  iff_of_imp (imp_trans (iff_mp h₁) (iff_mp h₂)) (imp_trans (iff_mpr h₂) (iff_mpr h₁))

lemma mem_iff_of_iff (h : φ 🡘 ψ ∈ L) : φ ∈ L ↔ ψ ∈ L :=
  ⟨fun hA => mem_mdp hA <| iff_mp h, fun hB => mem_mdp hB <| iff_mpr h⟩

lemma imp_and_intro (h₁ : χ 🡒 φ ∈ L) (h₂ : χ 🡒 ψ ∈ L) : χ 🡒 φ ⋏ ψ ∈ L :=
  derives_imp_iff_mem.mp <|
    Derives.and_intro (.of_imp_mem h₁ <| .mem rfl) (.of_imp_mem h₂ <| .mem rfl)

lemma or_imp_intro (h₁ : φ 🡒 χ ∈ L) (h₂ : ψ 🡒 χ ∈ L) : φ ⋎ ψ 🡒 χ ∈ L :=
  mdp₂ or_elim h₁ h₂

lemma and_iff_congr (h₁ : φ 🡘 χ ∈ L) (h₂ : ψ 🡘 θ ∈ L) : φ ⋏ ψ 🡘 χ ⋏ θ ∈ L := by
  apply iff_of_imp;
  · exact derives_imp_iff_mem.mp <| Derives.and_intro
      (.of_imp_mem (iff_mp h₁) <| Derives.and_left <| .mem rfl)
      (.of_imp_mem (iff_mp h₂) <| Derives.and_right <| .mem rfl);
  · exact derives_imp_iff_mem.mp <| Derives.and_intro
      (.of_imp_mem (iff_mpr h₁) <| Derives.and_left <| .mem rfl)
      (.of_imp_mem (iff_mpr h₂) <| Derives.and_right <| .mem rfl);

lemma imp_iff_congr (h₁ : φ 🡘 χ ∈ L) (h₂ : ψ 🡘 θ ∈ L) : (φ 🡒 ψ) 🡘 (χ 🡒 θ) ∈ L := by
  apply iff_of_imp;
  · apply derives_imp_iff_mem.mp;
    apply deduction;
    apply of_imp_mem (iff_mp h₂);
    apply Derives.mdp (φ := φ) _ (.mem <| by simp);
    exact .of_imp_mem (iff_mpr h₁) <| .mem <| by simp;
  · apply derives_imp_iff_mem.mp;
    apply deduction;
    apply of_imp_mem (iff_mpr h₂);
    apply Derives.mdp (φ := χ) _ (.mem <| by simp);
    exact .of_imp_mem (iff_mp h₁) <| .mem <| by simp;

lemma neg_iff_congr (h : φ 🡘 ψ ∈ L) : ∼φ 🡘 ∼ψ ∈ L := imp_iff_congr h iff_refl

lemma or_iff_congr (h₁ : φ 🡘 χ ∈ L) (h₂ : ψ 🡘 θ ∈ L) : φ ⋎ ψ 🡘 χ ⋎ θ ∈ L :=
  imp_iff_congr (neg_iff_congr h₁) h₂

lemma conj_mem_iff : ⋀l ∈ L ↔ ∀ φ ∈ l, φ ∈ L := by
  induction l with
  | nil => simp [verum_mem];
  | cons a l ih => simp [and_mem_iff, ih];

lemma imp_conj (h : ∀ φ ∈ l, ψ 🡒 φ ∈ L) : ψ 🡒 ⋀l ∈ L := by
  induction l with
  | nil => exact imp_of_mem verum_mem;
  | cons a l ih => exact imp_and_intro (h a <| by simp) (ih fun φ hA => h φ <| by simp [hA]);

lemma disj_imp (h : ∀ φ ∈ l, φ 🡒 ψ ∈ L) : ⋁l 🡒 ψ ∈ L := by
  induction l with
  | nil => exact efq;
  | cons a l ih => exact or_imp_intro (h a <| by simp) (ih fun φ hA => h φ <| by simp [hA]);

lemma Derives.conj (h : ∀ φ ∈ l, Γ ⊢[L] φ) : Γ ⊢[L] ⋀l := by
  induction l with
  | nil => exact thm verum_mem;
  | cons φ l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h;
    exact Derives.and_intro h.1 (ih h.2);

lemma derives_iff_exists_conj :
    Γ ⊢[L] φ ↔ ∃ l : List (Formula α), (∀ ψ ∈ l, ψ ∈ Γ) ∧ ⋀l 🡒 φ ∈ L := by
  constructor;
  · intro h;
    induction h with
    | @mem φ h => exact ⟨[φ], by simpa using h, conj_imp_of_mem <| List.mem_singleton_self φ⟩;
    | thm h => exact ⟨[], by simp, imp_of_mem h⟩;
    | @mdp φ ψ _ _ ihφ ihφψ =>
      obtain ⟨l₁, hl₁, h₁⟩ := ihφ;
      obtain ⟨l₂, hl₂, h₂⟩ := ihφψ;
      use l₁ ++ l₂;
      constructor;
      · simp_all [or_imp];
      · apply derives_imp_iff_mem.mp;
        have c₁ : {⋀(l₁ ++ l₂)} ⊢[L] ⋀l₁ :=
          .of_imp_mem (imp_conj fun _ hA => conj_imp_of_mem <| List.mem_append_left _ hA) <|
            .mem rfl;
        have c₂ : {⋀(l₁ ++ l₂)} ⊢[L] ⋀l₂ :=
          .of_imp_mem (imp_conj fun _ hA => conj_imp_of_mem <| List.mem_append_right _ hA) <|
            .mem rfl;
        exact .mdp (.of_imp_mem h₁ c₁) (.of_imp_mem h₂ c₂);
  · rintro ⟨l, hl, h⟩;
    exact of_imp_mem h <| conj fun ψ hB => mem <| hl ψ hB;

end Propositional

section Modal

open Formula

lemma box_mono (h : φ 🡒 ψ ∈ L) : □φ 🡒 □ψ ∈ L := mem_mdp (mem_nec h) distribute

lemma box_congr (h : φ 🡘 ψ ∈ L) : □φ 🡘 □ψ ∈ L :=
  iff_of_imp (box_mono <| iff_mp h) (box_mono <| iff_mpr h)

lemma box_top : □⊤ ∈ L := mem_nec verum_mem

lemma box_and : □(φ ⋏ ψ) 🡘 □φ ⋏ □ψ ∈ L := by
  apply iff_of_imp;
  · exact imp_and_intro (box_mono and_left) (box_mono and_right);
  · apply derives_imp_iff_mem.mp;
    have h : □φ 🡒 □(ψ 🡒 φ ⋏ ψ) ∈ L := box_mono and_intro;
    exact Derives.mdp (Derives.and_right <| .mem rfl) <|
      Derives.mdp (of_imp_mem h <| Derives.and_left <| .mem rfl) <| .thm distribute;

lemma box_conj : □(⋀l) 🡘 ⋀(l.map (□·)) ∈ L := by
  induction l with
  | nil => exact iff_of_imp (imp_of_mem verum_mem) (imp_of_mem box_top);
  | cons φ l ih =>
    simp only [List.map_cons, conj_cons];
    exact iff_trans box_and <| and_iff_congr iff_refl ih;

lemma box_conj_mem_iff : □(⋀l) ∈ L ↔ ∀ φ ∈ l, □φ ∈ L := by
  rw [mem_iff_of_iff box_conj, conj_mem_iff];
  simp;

lemma multibox_mono (h : φ 🡒 ψ ∈ L) : □^[n]φ 🡒 □^[n]ψ ∈ L := by
  induction n with
  | zero => exact h;
  | succ n ih => simpa using box_mono ih;

lemma Derives.box (h : Γ ⊢[L] φ) : (□·) '' Γ ⊢[L] □φ := by
  induction h with
  | mem h => exact mem <| Set.mem_image_of_mem _ h;
  | thm h => exact thm <| mem_nec h;
  | mdp _ _ ihφ ihφψ => exact Derives.mdp₂ (thm distribute) ihφψ ihφ;

lemma neg_dia_iff_box_neg : ∼◇φ 🡘 □(∼φ) ∈ L :=
  iff_trans (neg_iff_congr diaDual) neg_neg_iff

lemma neg_box_iff_dia_neg : ∼□φ 🡘 ◇(∼φ) ∈ L := neg_neg_iff

lemma dia_mono (h : φ 🡒 ψ ∈ L) : ◇φ 🡒 ◇ψ ∈ L :=
  imp_trans (imp_trans (iff_mp diaDual) <| contrapose <| box_mono <| contrapose h)
    (iff_mpr diaDual)

lemma dia_congr (h : φ 🡘 ψ ∈ L) : ◇φ 🡘 ◇ψ ∈ L :=
  iff_of_imp (dia_mono <| iff_mp h) (dia_mono <| iff_mpr h)

lemma dia_bot : ◇⊥ 🡘 ⊥ ∈ L := by
  apply iff_of_imp;
  · apply derives_imp_iff_mem.mp;
    have h : □(∼⊥) ∈ L := box_top;
    exact Derives.mdp (thm h) <| of_imp_mem (iff_mp diaDual) <| .mem rfl;
  · exact efq;

lemma neg_dia_bot : ∼◇⊥ ∈ L := iff_mp dia_bot

lemma box_imp_dia_imp : □(φ 🡒 ψ) 🡒 ◇φ 🡒 ◇ψ ∈ L := by
  have h : □(φ 🡒 ψ) 🡒 □(∼ψ) 🡒 □(∼φ) ∈ L := imp_trans (box_mono contra) distribute;
  apply empty_iff.mp;
  apply deduction;
  apply deduction;
  apply of_imp_mem (iff_mpr diaDual);
  apply deduction;
  apply Derives.mdp (φ := □(∼φ));
  · exact .mdp (φ := □(∼ψ)) (.mem <| by simp) <| .of_imp_mem h <| .mem <| by simp;
  · exact .of_imp_mem (iff_mp diaDual) <| .mem <| by simp;

lemma box_dia_and : □φ ⋏ ◇ψ 🡒 ◇(φ ⋏ ψ) ∈ L := by
  have h : □φ 🡒 ◇ψ 🡒 ◇(φ ⋏ ψ) ∈ L := imp_trans (box_mono and_intro) box_imp_dia_imp;
  apply derives_imp_iff_mem.mp;
  exact .mdp (.and_right <| .mem rfl) <| .of_imp_mem h <| .and_left <| .mem rfl;

lemma dia_or : ◇(φ ⋎ ψ) 🡘 ◇φ ⋎ ◇ψ ∈ L := by
  have h₀ : ∼φ ⋏ ∼ψ 🡒 ∼(φ ⋎ ψ) ∈ L := by
    apply derives_imp_iff_mem.mp;
    apply deduction;
    apply neg_elim (φ := ψ);
    · exact .mdp (φ := ∼φ) (Derives.and_left (ψ := ∼ψ) <| .mem <| by simp) (.mem <| by simp);
    · exact Derives.and_right (φ := ∼φ) <| .mem <| by simp;
  have h : □(∼φ) ⋏ □(∼ψ) 🡒 □(∼(φ ⋎ ψ)) ∈ L := imp_trans (iff_mpr box_and) (box_mono h₀);
  apply iff_of_imp;
  · apply derives_imp_iff_mem.mp;
    apply deduction;
    apply of_imp_mem (iff_mpr diaDual);
    apply deduction;
    apply Derives.mdp (φ := □(∼(φ ⋎ ψ)));
    · exact .of_imp_mem h <| .and_intro
        (.of_imp_mem (iff_mp neg_dia_iff_box_neg) <| .mem <| by simp) (.mem <| by simp);
    · exact .of_imp_mem (iff_mp diaDual) <| .mem <| by simp;
  · exact or_imp_intro (dia_mono or_left) (dia_mono or_right);

lemma dia_disj : ◇(⋁l) 🡘 ⋁(l.map (◇·)) ∈ L := by
  induction l with
  | nil => exact dia_bot;
  | cons φ l ih =>
    simp only [List.map_cons, disj_cons];
    exact iff_trans dia_or <| or_iff_congr iff_refl ih;

lemma multidia_mono (h : φ 🡒 ψ ∈ L) : ◇^[n]φ 🡒 ◇^[n]ψ ∈ L := by
  induction n with
  | zero => exact h;
  | succ n ih => simpa using dia_mono ih;

end Modal

end Reasoning

end NormalLogic

end
