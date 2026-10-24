module

public import BlokDichotomy.Algebraic.Validity

/-!
# Direct products of modal algebras

This file defines direct products of arbitrary families of modal algebras and shows that a product
validates exactly the formulas valid in every factor.

## References

- [CZ98, §7.7, Proposition 7.61]
-/

@[expose] public section

universe u v w

variable {α : Type w} {ι : Type u} {A : ι → Type v} [∀ i, ModalAlgebra (A i)]

namespace Pi

/--
The direct product of a family of modal algebras, with operations defined componentwise.
- [CZ98, §7.7]
-/
instance instModalAlgebra : ModalAlgebra (∀ i, A i) where
  dia f i := ◇f i
  dia_bot := funext fun _ => ModalAlgebra.dia_bot
  dia_sup _ _ := funext fun _ => ModalAlgebra.dia_sup _ _

@[simp] lemma dia_apply (f : ∀ i, A i) (i : ι) : (◇f) i = ◇f i := rfl

@[simp] lemma box_apply (f : ∀ i, A i) (i : ι) : (□f) i = □f i := rfl

/-- The projection of a direct product onto a factor. -/
def evalModalAlgebraHom (i : ι) : ModalAlgebraHom (∀ i, A i) (A i) where
  toFun f := f i
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl
  map_dia' _ := rfl

@[simp] lemma evalModalAlgebraHom_apply (i : ι) (f : ∀ i, A i) :
    evalModalAlgebraHom i f = f i := rfl

end Pi

namespace Formula

@[simp] lemma eval_pi_apply {φ : _root_.Formula α} (v : α → ∀ i, A i) (i : ι) :
    φ.eval v i = φ.eval (fun a => v a i) :=
  Formula.hom_eval (Pi.evalModalAlgebraHom i)

end Formula

namespace ModalAlgebra

variable {φ : Formula α}

/--
A direct product validates exactly the formulas valid in every factor.
- [CZ98, Proposition 7.61]
-/
theorem pi_validates_iff : (∀ i, A i) ⊧ φ ↔ ∀ i, A i ⊧ φ := by
  classical
  constructor;
  · intro h i v;
    simpa using congrFun (h fun a => Function.update (fun _ => ⊤) i (v a)) i;
  · intro h v;
    funext i;
    simpa using h i _;

end ModalAlgebra

end
