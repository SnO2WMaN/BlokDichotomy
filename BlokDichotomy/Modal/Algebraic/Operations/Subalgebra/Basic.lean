module

public import BlokDichotomy.Modal.Algebraic.Validity
public import Mathlib.Order.BooleanSubalgebra

/-!
# Subalgebras of modal algebras

This file defines modal subalgebras and shows that validity is reflected along injective
homomorphisms.

## References

- [CZ98, §7.7, Proposition 7.59]
-/

@[expose] public section

namespace Modal

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
    (h : B ⊧ φ) : A ⊧ φ := fun v => hf <| by simp [h _]

/--
A formula valid in `A` is valid in every subalgebra of `A`.
- [CZ98, Proposition 7.59]
-/
lemma Validates.subalgebra (S : ModalSubalgebra A) (h : A ⊧ φ) : S ⊧ φ :=
  h.of_injective S.subtype_injective

lemma logic_le_of_injective {f : ModalAlgebraHom A B} (hf : Function.Injective f) :
    logic (α := α) B ≤ logic A := fun _ => Validates.of_injective hf

end ModalAlgebra

end Modal

end
