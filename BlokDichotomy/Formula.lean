module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.DeriveCountable
public import BlokDichotomy.ToMathlib.Order.Notation

/-!
# Formulas of propositional modal logic

Formulas, substitutions, modal depth, variables, finite conjunctions and disjunctions, renaming
of variables, and subformulas.
-/

@[expose] public section

universe u w

inductive Formula (α : Type u) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | dia  : Formula α → Formula α
  deriving DecidableEq

deriving instance Countable for Formula

abbrev FormulaSet (α : Type u) := Set (Formula α)

abbrev FormulaFinset (α : Type u) := Finset (Formula α)

namespace Formula

section

variable {α : Type u} {n : ℕ} {φ φ₁ φ₂ ψ ψ₁ ψ₂ : Formula α}

instance : Bot (Formula α) := ⟨falsum⟩

prefix:max "#" => Formula.atom
infixr:60 " 🡒 " => Formula.imp

instance : Dia (Formula α) := ⟨dia⟩

@[simp, grind _=_] lemma dia_eq : dia φ = ◇φ := rfl

@[match_pattern] abbrev neg (φ : Formula α) : Formula α := imp φ ⊥
prefix:75 "∼" => Formula.neg

@[match_pattern] abbrev verum : Formula α := neg ⊥

instance : Top (Formula α) := ⟨verum⟩

@[match_pattern] abbrev or (φ ψ : Formula α) : Formula α := ∼φ 🡒 ψ
infixr:68 " ⋎ " => Formula.or

@[match_pattern] abbrev and (φ ψ : Formula α) : Formula α := ∼(φ 🡒 ∼ψ)
infixr:69 " ⋏ " => Formula.and

@[match_pattern]
abbrev box (φ : Formula α) : Formula α := ∼◇(∼φ)

instance : Box (Formula α) := ⟨box⟩

@[grind =] lemma box_eq : □φ = ∼◇(∼φ) := rfl

@[match_pattern] abbrev iff (φ ψ : Formula α) : Formula α := (φ 🡒 ψ) ⋏ (ψ 🡒 φ)
infix:61 " 🡘 " => Formula.iff

@[grind =] lemma eq_verum_neg_falsum : ⊤ = ∼(⊥ : Formula α) := rfl

lemma falsum_eq : (⊥ : Formula α) = falsum := rfl
lemma verum_eq : (⊤ : Formula α) = verum := rfl
lemma iff_eq : φ 🡘 ψ = (φ 🡒 ψ) ⋏ (ψ 🡒 φ) := rfl
attribute [grind =_] falsum_eq verum_eq iff_eq

@[grind =] lemma inj_and : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [and]
@[grind =] lemma inj_or : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [or]
@[grind =] lemma inj_imp : φ₁ 🡒 φ₂ = ψ₁ 🡒 ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp
@[grind =] lemma inj_neg : ∼φ = ∼ψ ↔ φ = ψ := by simp [neg]
@[simp, grind =] lemma inj_dia : ◇φ = ◇ψ ↔ φ = ψ := ⟨fun h => dia.inj h, congrArg _⟩
@[simp, grind =] lemma inj_box : □φ = □ψ ↔ φ = ψ := by simp [box_eq]

@[grind =]
def complexity : Formula α → ℕ
  | atom _ => 0
  | ⊥      => 0
  | φ 🡒 ψ  => max φ.complexity ψ.complexity + 1
  | ◇φ     => φ.complexity + 1

@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom : ∀ a, C (atom a))
    (himp : ∀ φ ψ, C (φ 🡒 ψ))
    (hdia : ∀ φ, C (◇φ))
    : (φ : Formula α) → C φ
  | ⊥      => hfalsum
  | atom a => hatom a
  | ◇φ     => hdia φ
  | φ 🡒 ψ  => himp φ ψ

@[induction_eliminator]
def rec' {C : Formula α → Sort w}
    (falsum : C ⊥)
    (atom : ∀ a, C (atom a))
    (imp : ∀ φ ψ, C φ → C ψ → C (φ 🡒 ψ))
    (dia : ∀ φ, C φ → C (◇φ))
    : (φ : Formula α) → C φ
  | ⊥      => falsum
  | #a => atom a
  | φ 🡒 ψ  => imp φ ψ (rec' falsum atom imp dia φ) (rec' falsum atom imp dia ψ)
  | ◇φ     => dia φ (rec' falsum atom imp dia φ)

abbrev multibox (n : ℕ) : Formula α → Formula α := (□·)^[n]
notation:76 "□^[" n "]" φ:80 => Formula.multibox n φ

abbrev multidia (n : ℕ) : Formula α → Formula α := (◇·)^[n]
notation:76 "◇^[" n "]" φ:80 => Formula.multidia n φ

@[simp, grind =] lemma multibox_zero : (□^[0]φ) = φ := rfl
@[simp, grind =] lemma multibox_succ : (□^[n + 1]φ) = □(□^[n]φ) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multibox_add {m : ℕ} : (□^[n](□^[m]φ)) = □^[n + m]φ :=
  (Function.iterate_add_apply _ n m φ).symm

@[simp, grind =] lemma multidia_zero : (◇^[0]φ) = φ := rfl
@[simp, grind =] lemma multidia_succ : (◇^[n + 1]φ) = ◇(◇^[n]φ) := Function.iterate_succ_apply' ..
@[simp, grind =] lemma multidia_add {m : ℕ} : (◇^[n](◇^[m]φ)) = ◇^[n + m]φ :=
  (Function.iterate_add_apply _ n m φ).symm

end

section

variable {α β γ : Type*}

abbrev Substitution (α β) := α → Formula β

@[grind]
def subst (s : Substitution α β) : Formula α → Formula β
| #a    => s a
| ⊥     => ⊥
| φ 🡒 ψ => subst s φ 🡒 subst s ψ
| ◇φ    => ◇(subst s φ)
notation:95 φ "⟦" s "⟧" => Formula.subst s φ

variable {s : Substitution α β} {φ ψ : Formula α}

@[simp, grind =] lemma subst_atom {a : α} : (#a)⟦s⟧ = s a := rfl
@[simp, grind =] lemma subst_bot : (⊥ : Formula α)⟦s⟧ = ⊥ := rfl
@[simp, grind =] lemma subst_imp : (φ 🡒 ψ)⟦s⟧ = φ⟦s⟧ 🡒 ψ⟦s⟧ := rfl
@[simp, grind =] lemma subst_dia : (◇φ)⟦s⟧ = ◇(φ⟦s⟧) := rfl

@[simp, grind =] lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl
@[simp, grind =] lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl
@[simp, grind =] lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl
@[simp, grind =] lemma subst_iff : (φ 🡘 ψ)⟦s⟧ = φ⟦s⟧ 🡘 ψ⟦s⟧ := rfl
@[simp, grind =] lemma subst_top : (⊤ : Formula α)⟦s⟧ = ⊤ := rfl
@[simp, grind =] lemma subst_box : (□φ)⟦s⟧ = □(φ⟦s⟧) := rfl

@[grind =]
lemma subst_subst {t : Substitution α β} {s : Substitution β γ} :
  (φ⟦t⟧)⟦s⟧ = φ⟦fun a => (t a)⟦s⟧⟧ := by
  induction φ <;> grind;
@[simp, grind =]
lemma subst_id : φ⟦(#·)⟧ = φ := by induction φ <;> grind;

end

/-!
# Modal depth and variables
-/

section

variable {α : Type*} {a : α} {φ ψ : Formula α}

/-- The modal depth of a formula. -/
@[grind]
def depth : Formula α → ℕ
  | .atom _ => 0
  | .falsum => 0
  | .imp φ ψ => max φ.depth ψ.depth
  | .dia φ => φ.depth + 1

@[simp] lemma depth_atom : (#a).depth = 0 := rfl
@[simp] lemma depth_bot : (⊥ : Formula α).depth = 0 := rfl
@[simp] lemma depth_imp : (φ 🡒 ψ).depth = max φ.depth ψ.depth := rfl
@[simp] lemma depth_dia : (◇φ).depth = φ.depth + 1 := rfl

variable [DecidableEq α]

def atoms : Formula α → Finset α
  | .atom a => {a}
  | .falsum => ∅
  | .imp φ ψ => φ.atoms ∪ ψ.atoms
  | .dia φ => φ.atoms

@[simp] lemma atoms_atom : (#a).atoms = {a} := rfl
@[simp] lemma atoms_bot : (⊥ : Formula α).atoms = ∅ := rfl
@[simp] lemma atoms_imp : (φ 🡒 ψ).atoms = φ.atoms ∪ ψ.atoms := rfl
@[simp] lemma atoms_dia : (◇φ).atoms = φ.atoms := rfl
@[simp] lemma atoms_box : (□φ).atoms = φ.atoms := by simp [box_eq]

end

/-!
# Finite conjunctions and disjunctions
-/

section

variable {α β : Type*} {φ : Formula α} {l l₁ l₂ : List (Formula α)}

def conj : List (Formula α) → Formula α
  | [] => ⊤
  | φ :: l => φ ⋏ conj l
prefix:75 "⋀" => Formula.conj

def disj : List (Formula α) → Formula α
  | [] => ⊥
  | φ :: l => φ ⋎ disj l
prefix:75 "⋁" => Formula.disj

@[simp, grind =] lemma conj_nil : ⋀([] : List (Formula α)) = ⊤ := rfl
@[simp, grind =] lemma conj_cons : ⋀(φ :: l) = φ ⋏ ⋀l := rfl
@[simp, grind =] lemma disj_nil : ⋁([] : List (Formula α)) = ⊥ := rfl
@[simp, grind =] lemma disj_cons : ⋁(φ :: l) = φ ⋎ ⋁l := rfl

@[simp, grind =]
lemma subst_conj {s : Substitution α β} : (⋀l)⟦s⟧ = ⋀(l.map (·⟦s⟧)) := by
  induction l <;> simp_all

@[simp, grind =]
lemma subst_disj {s : Substitution α β} : (⋁l)⟦s⟧ = ⋁(l.map (·⟦s⟧)) := by
  induction l <;> simp_all

end

section

variable {α β : Type*} {A B : Formula α} {l : List (Formula α)}

@[simp] lemma depth_neg : (∼A).depth = A.depth := by simp
@[simp] lemma depth_and : (A ⋏ B).depth = max A.depth B.depth := by simp
@[simp] lemma depth_or : (A ⋎ B).depth = max A.depth B.depth := by simp

lemma depth_conj_eq_zero (h : ∀ A ∈ l, A.depth = 0) : (⋀l).depth = 0 := by
  induction l with
  | nil => simp [depth, Formula.verum_eq];
  | cons A l ih =>
    simp only [conj_cons, depth_and, h A List.mem_cons_self, ih fun B hB => h B <| .tail _ hB];
    simp;

lemma depth_disj_eq_zero (h : ∀ A ∈ l, A.depth = 0) : (⋁l).depth = 0 := by
  induction l with
  | nil => simp;
  | cons A l ih =>
    simp only [disj_cons, depth_or, h A List.mem_cons_self, ih fun B hB => h B <| .tail _ hB];
    simp;

lemma subst_congr_of_atoms [DecidableEq α] {s₁ s₂ : Substitution α β}
    (h : ∀ a ∈ A.atoms, s₁ a = s₂ a) : A⟦s₁⟧ = A⟦s₂⟧ := by
  induction A with
  | atom a => exact h a <| by simp;
  | falsum => rfl;
  | imp A B ihA ihB =>
    simp only [subst_imp];
    rw [ihA fun a ha => h a <| by simp [ha], ihB fun a ha => h a <| by simp [ha]];
  | dia A ih => simp only [subst_dia]; rw [ih h];

end

/-!
# Renaming of variables
-/

section

variable {α β γ : Type*} {f : α → β} {g : β → γ} {φ ψ : Formula α} {a : α} {n : ℕ}
  {l : List (Formula α)}

/-- `φ.map f` is `φ` with every variable `a` replaced by `f a`. -/
def map (f : α → β) (φ : Formula α) : Formula β := φ⟦fun a => #(f a)⟧

@[simp, grind =] lemma map_atom : (#a).map f = #(f a) := rfl
@[simp, grind =] lemma map_bot : (⊥ : Formula α).map f = ⊥ := rfl
@[simp, grind =] lemma map_imp : (φ 🡒 ψ).map f = φ.map f 🡒 ψ.map f := rfl
@[simp, grind =] lemma map_dia : (◇φ).map f = ◇(φ.map f) := rfl
@[simp, grind =] lemma map_neg : (∼φ).map f = ∼(φ.map f) := rfl
@[simp, grind =] lemma map_top : (⊤ : Formula α).map f = ⊤ := rfl
@[simp, grind =] lemma map_and : (φ ⋏ ψ).map f = φ.map f ⋏ ψ.map f := rfl
@[simp, grind =] lemma map_or : (φ ⋎ ψ).map f = φ.map f ⋎ ψ.map f := rfl
@[simp, grind =] lemma map_iff : (φ 🡘 ψ).map f = φ.map f 🡘 ψ.map f := rfl
@[simp, grind =] lemma map_box : (□φ).map f = □(φ.map f) := rfl

@[simp, grind =]
lemma map_multidia : (◇^[n]φ).map f = ◇^[n](φ.map f) := by
  induction n <;> simp_all

@[simp, grind =]
lemma map_multibox : (□^[n]φ).map f = □^[n](φ.map f) := by
  induction n <;> simp_all

@[simp, grind =]
lemma map_conj : (⋀l).map f = ⋀(l.map (·.map f)) := by
  induction l <;> simp_all

@[simp, grind =]
lemma map_disj : (⋁l).map f = ⋁(l.map (·.map f)) := by
  induction l <;> simp_all

@[simp]
lemma map_id : φ.map id = φ := subst_id

lemma map_map : (φ.map f).map g = φ.map (g ∘ f) := subst_subst

lemma map_subst {s : Substitution α β} : (φ⟦s⟧).map g = φ⟦fun a => (s a).map g⟧ := subst_subst

lemma subst_map {s : Substitution β γ} : (φ.map f)⟦s⟧ = φ⟦fun a => s (f a)⟧ := subst_subst

lemma map_injective (hf : Function.Injective f) : Function.Injective (map f : Formula α → _) := by
  intro φ ψ h;
  induction φ generalizing ψ with
  | falsum => cases ψ <;> simp_all [map, subst, falsum_eq];
  | atom a => cases ψ <;> simp_all [map, subst, hf.eq_iff];
  | imp φ₁ φ₂ ih₁ ih₂ =>
    cases ψ with
    | imp => grind;
    | _ => simp_all [map, subst];
  | dia φ ih =>
    cases ψ with
    | dia => grind;
    | _ => simp_all [map, subst];

end

/-!
# Subformulas and finitely many variables
-/

section

variable {α : Type*} [DecidableEq α] {φ ψ χ : Formula α}

@[grind]
def subformulas : Formula α → Finset (Formula α)
  | #a => {#a}
  | ⊥ => {⊥}
  | φ 🡒 ψ => insert (φ 🡒 ψ) (φ.subformulas ∪ ψ.subformulas)
  | ◇φ => insert (◇φ) φ.subformulas

@[simp, grind .]
lemma mem_subformulas_self : φ ∈ φ.subformulas := by
  cases φ <;> grind;

@[grind <=]
lemma mem_subformulas_imp_left (h : χ ∈ φ.subformulas) : χ ∈ (φ 🡒 ψ).subformulas := by grind;

@[grind <=]
lemma mem_subformulas_imp_right (h : χ ∈ ψ.subformulas) : χ ∈ (φ 🡒 ψ).subformulas := by grind;

@[grind <=]
lemma mem_subformulas_dia (h : ψ ∈ φ.subformulas) : ψ ∈ (◇φ).subformulas := by grind;

lemma subformulas_subset_of_mem (h : χ ∈ φ.subformulas) : χ.subformulas ⊆ φ.subformulas := by
  induction φ with
  | atom a => grind;
  | falsum =>
    simp only [subformulas, Finset.mem_singleton] at h;
    subst h;
    exact Finset.Subset.refl _
  | imp φ₁ φ₂ ih₁ ih₂ => grind;
  | dia φ ih => grind;

lemma mem_subformulas_of_imp_left (h : (φ 🡒 ψ) ∈ χ.subformulas) : φ ∈ χ.subformulas :=
  subformulas_subset_of_mem h <| mem_subformulas_imp_left mem_subformulas_self

lemma mem_subformulas_of_imp_right (h : (φ 🡒 ψ) ∈ χ.subformulas) : ψ ∈ χ.subformulas :=
  subformulas_subset_of_mem h <| mem_subformulas_imp_right mem_subformulas_self

lemma mem_subformulas_of_dia (h : ◇φ ∈ χ.subformulas) : φ ∈ χ.subformulas :=
  subformulas_subset_of_mem h <| mem_subformulas_dia mem_subformulas_self

/-- For every `φ : Formula ℕ` there is `m` such that, for all `m' ≥ m`, `φ` is the renaming along
`Fin.val` of a formula over `Fin m'`. -/
lemma exists_forall_ge_map_finVal (φ : Formula ℕ) :
    ∃ m, ∀ m' ≥ m, ∃ φ' : Formula (Fin m'), φ'.map Fin.val = φ := by
  induction φ with
  | falsum => exact ⟨0, fun _ _ => ⟨⊥, rfl⟩⟩;
  | atom a => exact ⟨a + 1, fun m' hm' => ⟨#⟨a, by omega⟩, rfl⟩⟩;
  | imp φ ψ ihφ ihψ =>
    obtain ⟨m₁, h₁⟩ := ihφ;
    obtain ⟨m₂, h₂⟩ := ihψ;
    use max m₁ m₂;
    intro m' hm';
    obtain ⟨φ', rfl⟩ := h₁ m' (le_of_max_le_left hm');
    obtain ⟨ψ', rfl⟩ := h₂ m' (le_of_max_le_right hm');
    exact ⟨φ' 🡒 ψ', rfl⟩;
  | dia φ ih =>
    obtain ⟨m, h⟩ := ih;
    use m;
    intro m' hm';
    obtain ⟨φ', rfl⟩ := h m' hm';
    exact ⟨◇φ', rfl⟩;

/-- Every `φ : Formula ℕ` is the renaming along `Fin.val` of a formula over some `Fin m`. -/
lemma exists_map_finVal (φ : Formula ℕ) : ∃ m, ∃ φ' : Formula (Fin m), φ'.map Fin.val = φ := by
  obtain ⟨m, h⟩ := φ.exists_forall_ge_map_finVal;
  exact ⟨m, h m le_rfl⟩;

end

section

variable {α : Type*} {n : ℕ} {φ : Formula α}

/-- `φ ⋏ □φ ⋏ ⋯ ⋏ □^[n]φ`. -/
def boxLe : ℕ → Formula α → Formula α
  | 0, φ => φ
  | n + 1, φ => φ ⋏ □(boxLe n φ)

notation:76 "□^≤[" n "]" φ:80 => Formula.boxLe n φ

/-- `φ ⋎ ◇φ ⋎ ⋯ ⋎ ◇^[n]φ`. -/
def diaLe : ℕ → Formula α → Formula α
  | 0, φ => φ
  | n + 1, φ => φ ⋎ ◇(diaLe n φ)

notation:76 "◇^≤[" n "]" φ:80 => Formula.diaLe n φ

@[simp]
lemma atoms_boxLe [DecidableEq α] : (□^≤[n] φ).atoms = φ.atoms := by
  induction n <;> simp_all [boxLe]

end

end Formula

end
