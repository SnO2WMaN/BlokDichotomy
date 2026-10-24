module

public import BlokDichotomy.ToMathlib.Order.Notation
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Modal algebras

Modal algebras, taken as Boolean algebras with a normal additive operator `◇`, the dual operator
`□`, and homomorphisms of modal algebras.

## References

- [CZ98, §7.5, §7.7]
-/

@[expose] public section

namespace Modal

universe u v w

/--
A Boolean algebra with an operator `◇` preserving `⊥` and binary joins.
- [CZ98, §7.5, Theorem 7.44]
-/
class ModalAlgebra (A : Type u) extends BooleanAlgebra A, Dia A where
  dia_bot : ◇(⊥ : A) = ⊥
  dia_sup (a b : A) : ◇(a ⊔ b) = ◇a ⊔ ◇b

namespace ModalAlgebra

variable {A : Type u} [ModalAlgebra A] {a b : A}

/-- The dual operator `□a = (◇aᶜ)ᶜ`. -/
instance (priority := 100) toBox : Box A := ⟨fun a => (◇aᶜ)ᶜ⟩

lemma box_def : □a = (◇aᶜ)ᶜ := rfl

attribute [simp, grind =] dia_bot dia_sup

@[simp, grind =] lemma compl_box : (□a)ᶜ = ◇aᶜ := compl_compl _

@[simp, grind =] lemma compl_dia : (◇a)ᶜ = □aᶜ := by rw [box_def, compl_compl]

@[simp, grind =] lemma box_top : □(⊤ : A) = ⊤ := by rw [box_def, compl_top, dia_bot, compl_bot]

@[simp, grind =] lemma box_inf : □(a ⊓ b) = □a ⊓ □b := by
  simp only [box_def, compl_inf, dia_sup, compl_sup];

@[gcongr, grind ←]
lemma dia_mono (h : a ≤ b) : ◇a ≤ ◇b := by
  simpa [← dia_sup, sup_eq_right.mpr h] using le_sup_left (a := ◇a) (b := ◇b);

@[gcongr, grind ←]
lemma box_mono (h : a ≤ b) : □a ≤ □b := by
  exact compl_le_compl <| dia_mono <| compl_le_compl h;

lemma dia_monotone : Monotone (Dia.dia : A → A) := fun _ _ => dia_mono

lemma box_monotone : Monotone (Box.box : A → A) := fun _ _ => box_mono

lemma dia_inf_le : ◇(a ⊓ b) ≤ ◇a ⊓ ◇b := by grind [le_inf_iff, inf_le_left, inf_le_right]

lemma box_sup_le : □a ⊔ □b ≤ □(a ⊔ b) := by grind [sup_le_iff, le_sup_left, le_sup_right]

lemma box_himp_le : □(a ⇨ b) ≤ □a ⇨ □b := by
  simpa [le_himp_iff, ← box_inf] using box_mono (himp_inf_le (a := a) (b := b));

lemma box_inf_dia_le : □a ⊓ ◇b ≤ ◇(a ⊓ b) := by
  have h : b ≤ (a ⊓ b) ⊔ aᶜ := by simp [sup_inf_right];
  rw [inf_comm, ← le_himp_iff, himp_eq];
  simpa using dia_mono h;

end ModalAlgebra

/--
A homomorphism of modal algebras: a bounded lattice homomorphism commuting with `◇`.
- [CZ98, §7.1, §7.7]
-/
structure ModalAlgebraHom (A : Type u) (B : Type v) [ModalAlgebra A] [ModalAlgebra B] extends
    BoundedLatticeHom A B where
  map_dia' (a : A) : toFun (◇a) = ◇toFun a

namespace ModalAlgebraHom

variable {A : Type u} {B : Type v} {C : Type w} [ModalAlgebra A] [ModalAlgebra B]
  [ModalAlgebra C]

instance : FunLike (ModalAlgebraHom A B) A B where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩ := f;
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩ := g;
    congr;

instance : BoundedLatticeHomClass (ModalAlgebraHom A B) A B where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

variable (f : ModalAlgebraHom A B)

@[simp] lemma toFun_eq_coe : f.toFun = f := rfl

@[ext] lemma ext {g : ModalAlgebraHom A B} (h : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ h

@[simp, grind =] lemma map_dia (a : A) : f (◇a) = ◇f a := f.map_dia' a

@[simp, grind =] lemma map_compl (a : A) : f aᶜ = (f a)ᶜ := map_compl' f a

@[simp, grind =] lemma map_himp (a b : A) : f (a ⇨ b) = f a ⇨ f b := by simp [himp_eq]

@[simp, grind =] lemma map_box (a : A) : f (□a) = □f a := by
  simp only [ModalAlgebra.box_def, map_compl, map_dia];

/-- The identity homomorphism. -/
protected def id (A : Type u) [ModalAlgebra A] : ModalAlgebraHom A A where
  toBoundedLatticeHom := BoundedLatticeHom.id A
  map_dia' _ := rfl

@[simp] lemma coe_id : ⇑(ModalAlgebraHom.id A) = id := rfl

/-- The composition of homomorphisms. -/
def comp (g : ModalAlgebraHom B C) (f : ModalAlgebraHom A B) : ModalAlgebraHom A C where
  toBoundedLatticeHom := g.toBoundedLatticeHom.comp f.toBoundedLatticeHom
  map_dia' a := (congrArg g (f.map_dia a)).trans (g.map_dia _)

@[simp] lemma coe_comp (g : ModalAlgebraHom B C) : ⇑(g.comp f) = g ∘ f := rfl

end ModalAlgebraHom

end Modal

end
