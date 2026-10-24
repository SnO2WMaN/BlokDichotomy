module

public import BlokDichotomy.Algebraic.Basic
public import BlokDichotomy.Logic.Basic

/-!
# Validity in modal algebras

The value of a formula in a modal algebra under a valuation, validity of formulas in modal
algebras, and the normal logic of a modal algebra.

## References

- [CZ98, §7.1, §7.5, Theorem 7.44, Theorem 7.51]
-/

@[expose] public section

universe u v

namespace Formula

variable {α : Type v} {β : Type*} {A : Type u} [ModalAlgebra A] {v : α → A} {φ ψ : Formula α}

/--
The value of a formula in `A` under the valuation `v`.
- [CZ98, §7.1]
-/
def eval (v : α → A) : Formula α → A
  | #a => v a
  | ⊥ => ⊥
  | φ 🡒 ψ => eval v φ ⇨ eval v ψ
  | ◇φ => ◇eval v φ

@[simp, grind =] lemma eval_atom {a : α} : (#a).eval v = v a := rfl
@[simp, grind =] lemma eval_bot : (⊥ : Formula α).eval v = ⊥ := rfl
@[simp, grind =] lemma eval_imp : (φ 🡒 ψ).eval v = φ.eval v ⇨ ψ.eval v := rfl
@[simp, grind =] lemma eval_dia : (◇φ).eval v = ◇φ.eval v := rfl
@[simp, grind =] lemma eval_neg : (∼φ).eval v = (φ.eval v)ᶜ := himp_bot _
@[simp, grind =] lemma eval_top : (⊤ : Formula α).eval v = ⊤ := himp_self
@[simp, grind =] lemma eval_or : (φ ⋎ ψ).eval v = φ.eval v ⊔ ψ.eval v := by
  simp [himp_eq, sup_comm];
@[simp, grind =] lemma eval_and : (φ ⋏ ψ).eval v = φ.eval v ⊓ ψ.eval v := by
  simp [himp_eq, compl_sup, inf_comm];
@[simp, grind =] lemma eval_box : (□φ).eval v = □φ.eval v := by
  rw [box_eq, eval_neg, eval_dia, eval_neg, ModalAlgebra.box_def];
@[simp, grind =] lemma eval_iff : (φ 🡘 ψ).eval v = (φ.eval v ⇨ ψ.eval v) ⊓ (ψ.eval v ⇨ φ.eval v) :=
  eval_and

lemma eval_subst {s : Substitution α β} {v : β → A} :
    (φ⟦s⟧).eval v = φ.eval (fun a => (s a).eval v) := by
  induction φ <;> simp_all;

lemma eval_map {f : α → β} {v : β → A} : (φ.map f).eval v = φ.eval (v ∘ f) := eval_subst

@[simp]
lemma hom_eval {B : Type*} [ModalAlgebra B] (f : ModalAlgebraHom A B) :
    f (φ.eval v) = φ.eval (f ∘ v) := by
  induction φ <;> simp_all;

end Formula

namespace ModalAlgebra

variable {α : Type v} {A : Type u} [ModalAlgebra A] {φ ψ : Formula α}

/--
`A ⊧ φ`: `φ` takes the value `⊤` under every valuation in `A`.
- [CZ98, §7.1]
-/
def Validates (A : Type u) [ModalAlgebra A] (φ : Formula α) : Prop := ∀ v : α → A, φ.eval v = ⊤
infix:50 " ⊧ " => ModalAlgebra.Validates

abbrev NotValidates (A : Type u) [ModalAlgebra A] (φ : Formula α) : Prop := ¬(A ⊧ φ)
infix:50 " ⊭ " => ModalAlgebra.NotValidates

/-- `A` validates every formula of `L`, i.e. `A` is an `L`-algebra. -/
def ValidatesLogic (A : Type u) [ModalAlgebra A] (L : NormalLogic α) : Prop := ∀ φ ∈ L, A ⊧ φ
infix:50 " ⊧ " => ModalAlgebra.ValidatesLogic

abbrev NotValidatesLogic (A : Type u) [ModalAlgebra A] (L : NormalLogic α) : Prop := ¬(A ⊧ L)
infix:50 " ⊭ " => ModalAlgebra.NotValidatesLogic

lemma not_validates_iff : A ⊭ φ ↔ ∃ v : α → A, φ.eval v ≠ ⊤ := by
  simp [NotValidates, Validates];

lemma validates_imp_iff : A ⊧ φ 🡒 ψ ↔ ∀ v : α → A, φ.eval v ≤ ψ.eval v := by
  simp [Validates];

lemma validates_iff_iff : A ⊧ φ 🡘 ψ ↔ ∀ v : α → A, φ.eval v = ψ.eval v := by
  simp only [Validates, Formula.eval_iff, inf_eq_top_iff, himp_eq_top_iff, ← le_antisymm_iff];

lemma mdp (hA : A ⊧ φ) (hAB : A ⊧ φ 🡒 ψ) : A ⊧ ψ := fun v => by
  simpa [hA v] using hAB v

lemma nec (h : A ⊧ φ) : A ⊧ □φ := fun v => by simp [h v]

lemma subst {s : Formula.Substitution α α} (h : A ⊧ φ) : A ⊧ φ⟦s⟧ := fun _ => by
  simpa [Formula.eval_subst] using h _

/--
The normal logic `{φ | A ⊧ φ}`.
- [CZ98, Theorem 7.51]
-/
def logic (A : Type u) [ModalAlgebra A] : NormalLogic α where
  carrier := {φ | A ⊧ φ}
  mdp := mdp
  nec := nec
  subst := subst

@[simp, grind =] lemma mem_logic : φ ∈ logic A ↔ A ⊧ φ := Iff.rfl

lemma validatesLogic_logic : A ⊧ (logic A : NormalLogic α) := fun _ hA => hA

lemma ValidatesLogic.le_logic {L : NormalLogic α} (h : A ⊧ L) : L ≤ logic A := h

lemma validates_axiomsK (h : φ ∈ (FormulaSet.axiomsK : FormulaSet α)) : A ⊧ φ := by
  intro v;
  cases h with
  | imply₁ => simp [le_himp_iff];
  | imply₂ =>
    simp only [Formula.eval_imp, himp_eq_top_iff, le_himp_iff];
    exact le_trans
      (le_inf (le_trans (inf_le_inf_right _ inf_le_left) himp_inf_le)
        (le_trans (inf_le_inf_right _ inf_le_right) himp_inf_le))
      himp_inf_le;
  | dne => simp;
  | distribute => simpa using box_himp_le (A := A);
  | diaDual => simp;

/--
Every modal algebra validates `𝐊`.
- [CZ98, Theorem 7.44]
-/
theorem validates_logicK : A ⊧ (𝐊 : NormalLogic α) :=
  NormalLogic.ofSet_le (L := logic A) fun _ => validates_axiomsK

instance : (logic A : NormalLogic α).IsNExt 𝐊 := ⟨fun _ => validates_logicK _⟩

lemma ValidatesLogic.validates_add {L : NormalLogic α} {X : FormulaSet α} (hL : A ⊧ L)
    (hX : ∀ φ ∈ X, A ⊧ φ) : A ⊧ (L + X) :=
  NormalLogic.add_le (L₂ := logic A) hL hX

end ModalAlgebra

end
