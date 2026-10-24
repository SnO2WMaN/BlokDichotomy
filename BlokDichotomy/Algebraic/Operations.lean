module

public import BlokDichotomy.Algebraic.Validity
public import Mathlib.Order.BooleanSubalgebra

/-!
# Operations on modal algebras

Subalgebras, direct products and homomorphic images of modal algebras. Validity is reflected along
injective homomorphisms, preserved along surjective homomorphisms, and a direct product validates
exactly the formulas valid in every factor.

## References

- [CZ98, §7.7, Proposition 7.59, Proposition 7.61, Proposition 7.62]
-/

@[expose] public section

universe u v w

/-! ### Subalgebras -/

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

/-! ### Direct products -/

namespace ModalAlgebra

section Pi

variable {ι : Type u} {A : ι → Type v} [∀ i, ModalAlgebra (A i)]

/--
The direct product of a family of modal algebras, with operations defined componentwise.
- [CZ98, §7.7]
-/
instance instPi : ModalAlgebra (∀ i, A i) where
  dia f i := ◇f i
  dia_bot := funext fun _ => dia_bot
  dia_sup _ _ := funext fun _ => dia_sup _ _

@[simp] lemma pi_dia_apply (f : ∀ i, A i) (i : ι) : (◇f) i = ◇f i := rfl

@[simp] lemma pi_box_apply (f : ∀ i, A i) (i : ι) : (□f) i = □f i := rfl

/-- The projection of a direct product onto a factor. -/
def proj (i : ι) : ModalAlgebraHom (∀ i, A i) (A i) where
  toFun f := f i
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
  map_top' := rfl
  map_bot' := rfl
  map_dia' _ := rfl

@[simp] lemma proj_apply (i : ι) (f : ∀ i, A i) : proj i f = f i := rfl

end Pi

end ModalAlgebra

/-! ### Homomorphic images -/

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

/-! ### Validity -/

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

/--
A formula valid in `A` is valid in every surjective homomorphic image of `A`.
- [CZ98, Proposition 7.62]
-/
theorem Validates.of_surjective {f : ModalAlgebraHom A B} (hf : Function.Surjective f)
    (h : A ⊧ φ) : B ⊧ φ := by
  intro v;
  choose w hw using fun a => hf (v a);
  simpa [show f ∘ w = v from funext hw, h _] using (Formula.eval_hom f (v := w) (φ := φ)).symm;

/--
A formula valid in `A` is valid in every homomorphic image of `A`.
- [CZ98, Proposition 7.62]
-/
lemma Validates.range (f : ModalAlgebraHom A B) (h : A ⊧ φ) : f.range ⊧ φ :=
  h.of_surjective f.rangeRestrict_surjective

lemma logic_le_of_injective {f : ModalAlgebraHom A B} (hf : Function.Injective f) :
    (logic B : NormalLogic α) ≤ logic A := fun _ => Validates.of_injective hf

lemma logic_le_of_surjective {f : ModalAlgebraHom A B} (hf : Function.Surjective f) :
    (logic A : NormalLogic α) ≤ logic B := fun _ => Validates.of_surjective hf

section Pi

variable {ι : Type u} {A : ι → Type v} [∀ i, ModalAlgebra (A i)]

@[simp] lemma eval_pi_apply (v : α → ∀ i, A i) (i : ι) :
    φ.eval v i = φ.eval (fun a => v a i) :=
  Formula.eval_hom (proj i)

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

end Pi

end ModalAlgebra

end
