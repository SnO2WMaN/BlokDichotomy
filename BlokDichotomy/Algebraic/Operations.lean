module

public import BlokDichotomy.Algebraic.Validity
public import Mathlib.Order.BooleanSubalgebra

/-!
# Validity under operations on modal algebras

Modal subalgebras. Validity is reflected along injective homomorphisms (subalgebras),
preserved along surjective homomorphisms (homomorphic images), and a direct product validates
exactly the formulas valid in every factor.

## References

- [CZ98, §7.7, Proposition 7.59]
-/

@[expose] public section

universe u v w

/--
A Boolean subalgebra closed under `◇`.
- [CZ98, §7.7]
-/
structure ModalSubalgebra (A : Type u) [ModalAlgebra A] extends BooleanSubalgebra A where
  dia_mem' {a} : a ∈ carrier → ◇a ∈ carrier

namespace ModalSubalgebra

variable {A : Type u} [ModalAlgebra A] (S : ModalSubalgebra A) {a : A}

instance : SetLike (ModalSubalgebra A) A where
  coe S := S.carrier
  coe_injective S T h := by
    obtain ⟨S, _⟩ := S;
    obtain ⟨T, _⟩ := T;
    congr;
    exact SetLike.coe_injective h;

lemma dia_mem (h : a ∈ S) : ◇a ∈ S := S.dia_mem' h

instance : ModalAlgebra S where
  __ := S.toBooleanSubalgebra.instBooleanAlgebraCoe
  dia a := ⟨◇a.1, S.dia_mem a.2⟩
  dia_bot := Subtype.ext ModalAlgebra.dia_bot
  dia_sup _ _ := Subtype.ext <| ModalAlgebra.dia_sup _ _

@[simp, norm_cast] lemma val_dia (a : S) : ((◇a : S) : A) = ◇(a : A) := rfl

/-- The inclusion of a modal subalgebra. -/
def subtype : ModalAlgebraHom S A where
  toBoundedLatticeHom := S.toBooleanSubalgebra.subtype
  map_dia' _ := rfl

@[simp] lemma coe_subtype : ⇑S.subtype = ((↑) : S → A) := rfl

lemma subtype_injective : Function.Injective S.subtype := Subtype.coe_injective

end ModalSubalgebra

namespace ModalAlgebra

variable {α : Type w} {A : Type u} {B : Type v} [ModalAlgebra A] [ModalAlgebra B]
  {φ : Formula α}

/--
A formula valid in `B` is valid in every algebra embedded in `B`.
- [CZ98, Proposition 7.59]
-/
theorem Validates.of_injective {f : ModalAlgebraHom A B} (hf : Function.Injective f)
    (h : B ⊧ φ) : A ⊧ φ := by
  intro v;
  apply hf;
  rw [Formula.eval_hom, h, map_top];

/--
A formula valid in `A` is valid in every homomorphic image of `A`.
- [CZ98, §7.7]
-/
theorem Validates.of_surjective {f : ModalAlgebraHom A B} (hf : Function.Surjective f)
    (h : A ⊧ φ) : B ⊧ φ := by
  intro v;
  choose w hw using fun a => hf (v a);
  have : f ∘ w = v := funext hw;
  rw [← this, ← Formula.eval_hom, h, map_top];

lemma logic_le_of_injective {f : ModalAlgebraHom A B} (hf : Function.Injective f) :
    (logic B : NormalLogic α) ≤ logic A := fun _ => Validates.of_injective hf

lemma logic_le_of_surjective {f : ModalAlgebraHom A B} (hf : Function.Surjective f) :
    (logic A : NormalLogic α) ≤ logic B := fun _ => Validates.of_surjective hf

/--
A formula valid in `A` is valid in every subalgebra of `A`.
- [CZ98, Proposition 7.59]
-/
lemma Validates.subalgebra (S : ModalSubalgebra A) (h : A ⊧ φ) : S ⊧ φ :=
  h.of_injective S.subtype_injective

section Pi

variable {ι : Type u} {A : ι → Type v} [∀ i, ModalAlgebra (A i)]

lemma eval_pi_apply (v : α → ∀ i, A i) (i : ι) : φ.eval v i = φ.eval (fun a => v a i) :=
  Formula.eval_hom (proj i)

/--
A direct product validates exactly the formulas valid in every factor.
- [CZ98, §7.7]
-/
theorem pi_validates_iff : (∀ i, A i) ⊧ φ ↔ ∀ i, A i ⊧ φ := by
  classical
  constructor;
  · intro h i v;
    simpa [eval_pi_apply] using congrFun (h fun a => Function.update (fun _ => ⊤) i (v a)) i;
  · intro h v;
    funext i;
    simpa [eval_pi_apply] using h i (fun a => v a i);

end Pi

end ModalAlgebra

end
