module

public import BlokDichotomy.Algebraic.Operations.Subalgebra.Basic

/-!
# Homomorphic images of modal algebras

This file defines the image of a modal algebra homomorphism as a subalgebra and shows that validity
is preserved along surjective homomorphisms.

## References

- [CZ98, §7.7, Proposition 7.62]
-/

@[expose] public section

universe u v w

namespace ModalAlgebraHom

variable {A : Type u} {B : Type v} [ModalAlgebra A] [ModalAlgebra B] (f : ModalAlgebraHom A B)

/--
The homomorphic image `f(A)`, as a subalgebra of `B`.
- [CZ98, §7.7]
-/
def range : ModalSubalgebra B where
  carrier := Set.range f
  supClosed' := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a ⊔ b, map_sup f a b⟩
  infClosed' := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a ⊓ b, map_inf f a b⟩
  compl_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨aᶜ, f.map_compl a⟩
  bot_mem' := ⟨⊥, map_bot f⟩
  dia_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨◇a, f.map_dia a⟩

@[simp] lemma mem_range {b : B} : b ∈ f.range ↔ ∃ a, f a = b := Iff.rfl

/-- `f`, regarded as a homomorphism onto its image. -/
def rangeRestrict : ModalAlgebraHom A f.range where
  toFun a := ⟨f a, a, rfl⟩
  map_sup' a b := Subtype.ext <| map_sup f a b
  map_inf' a b := Subtype.ext <| map_inf f a b
  map_top' := Subtype.ext <| map_top f
  map_bot' := Subtype.ext <| map_bot f
  map_dia' a := Subtype.ext <| f.map_dia a

@[simp] lemma coe_rangeRestrict (a : A) : (f.rangeRestrict a : B) = f a := rfl

lemma rangeRestrict_surjective : Function.Surjective f.rangeRestrict := by
  rintro ⟨_, a, rfl⟩;
  exact ⟨a, rfl⟩;

end ModalAlgebraHom

namespace ModalAlgebra

variable {α : Type w} {A : Type u} {B : Type v} [ModalAlgebra A] [ModalAlgebra B]
  {φ : Formula α}

/--
A formula valid in `A` is valid in every surjective homomorphic image of `A`.
- [CZ98, Proposition 7.62]
-/
theorem Validates.of_surjective {f : ModalAlgebraHom A B} (hf : Function.Surjective f)
    (h : A ⊧ φ) : B ⊧ φ := by
  intro v;
  choose w hw using fun a => hf (v a);
  simpa [show f ∘ w = v from funext hw, h _] using (Formula.hom_eval f (v := w) (φ := φ)).symm;

/--
A formula valid in `A` is valid in every homomorphic image of `A`.
- [CZ98, Proposition 7.62]
-/
lemma Validates.range (f : ModalAlgebraHom A B) (h : A ⊧ φ) : f.range ⊧ φ :=
  h.of_surjective f.rangeRestrict_surjective

lemma logic_le_of_surjective {f : ModalAlgebraHom A B} (hf : Function.Surjective f) :
    (logic A : NormalLogic α) ≤ logic B := fun _ => Validates.of_surjective hf

end ModalAlgebra

end
