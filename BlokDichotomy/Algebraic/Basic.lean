module

public import BlokDichotomy.Formula
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Modal algebras

Modal algebras, taken as Boolean algebras with a normal additive operator `◇`, the dual operator
`□`, homomorphisms of modal algebras, and direct products.

## References

- [CZ98, §7.5, §7.7]
-/

@[expose] public section

universe u v w

/--
A Boolean algebra with an operator `◇` preserving `⊥` and binary joins.
- [CZ98, §7.5, Theorem 7.44]
-/
class ModalAlgebra (A : Type u) extends BooleanAlgebra A where
  dia : A → A
  dia_bot : dia ⊥ = ⊥
  dia_sup (a b : A) : dia (a ⊔ b) = dia a ⊔ dia b

namespace ModalAlgebra

prefix:95 "◇" => ModalAlgebra.dia

variable {A : Type u} [ModalAlgebra A] {a b : A}

/-- The dual operator `□a = (◇aᶜ)ᶜ`. -/
def box (a : A) : A := (◇aᶜ)ᶜ
prefix:95 "□" => ModalAlgebra.box

attribute [simp] dia_bot dia_sup

lemma box_def : □a = (◇aᶜ)ᶜ := rfl

@[simp] lemma compl_box : (□a)ᶜ = ◇aᶜ := compl_compl _

lemma compl_dia : (◇a)ᶜ = □aᶜ := by rw [box, compl_compl]

@[simp] lemma box_top : □(⊤ : A) = ⊤ := by rw [box, compl_top, dia_bot, compl_bot]

@[simp] lemma box_inf : □(a ⊓ b) = □a ⊓ □b := by simp [box, compl_inf]

@[gcongr]
lemma dia_mono (h : a ≤ b) : ◇a ≤ ◇b := by
  rw [← sup_eq_right.mpr h, dia_sup];
  exact le_sup_left;

lemma dia_monotone : Monotone (dia : A → A) := fun _ _ => dia_mono

@[gcongr]
lemma box_mono (h : a ≤ b) : □a ≤ □b := by
  simpa [box] using dia_mono <| compl_le_compl h;

lemma box_monotone : Monotone (box : A → A) := fun _ _ => box_mono

lemma dia_inf_le : ◇(a ⊓ b) ≤ ◇a ⊓ ◇b :=
  le_inf (dia_mono inf_le_left) (dia_mono inf_le_right)

lemma box_sup_le : □a ⊔ □b ≤ □(a ⊔ b) :=
  sup_le (box_mono le_sup_left) (box_mono le_sup_right)

lemma box_inf_dia_le : □a ⊓ ◇b ≤ ◇(a ⊓ b) := by
  have h : ◇b ≤ ◇(a ⊓ b) ⊔ (□a)ᶜ := by
    rw [compl_box, ← dia_sup];
    apply dia_mono;
    rw [sup_comm, sup_inf_left, compl_sup_eq_top, top_inf_eq];
    exact le_sup_right;
  rw [inf_comm, ← le_himp_iff, himp_eq];
  exact h;

lemma box_himp_le : □(a ⇨ b) ≤ □a ⇨ □b := by
  rw [le_himp_iff, ← box_inf];
  exact box_mono <| by simp;

end ModalAlgebra

/--
A homomorphism of modal algebras: a bounded lattice homomorphism commuting with `◇`.
- [CZ98, §7.7]
-/
structure ModalAlgebraHom (A : Type u) (B : Type v) [ModalAlgebra A] [ModalAlgebra B] extends
    BoundedLatticeHom A B where
  map_dia' (a : A) : toFun (◇a) = ◇toFun a

namespace ModalAlgebraHom

variable {A : Type u} {B : Type v} {C : Type w} [ModalAlgebra A] [ModalAlgebra B]
  [ModalAlgebra C] {a : A}

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

@[simp] lemma map_dia (a : A) : f (◇a) = ◇f a := f.map_dia' a

@[simp] lemma map_compl : f aᶜ = (f a)ᶜ := map_compl' f a

@[simp] lemma map_himp {b : A} : f (a ⇨ b) = f a ⇨ f b := by simp [himp_eq]

@[simp] lemma map_box : f (□a) = □f a := by simp [ModalAlgebra.box]

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

namespace ModalAlgebra

variable {ι : Type u} {A : ι → Type v} [∀ i, ModalAlgebra (A i)]

/--
The direct product of modal algebras, with operations defined componentwise.
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

@[simp] lemma coe_proj (i : ι) : ⇑(proj (A := A) i) = fun f => f i := rfl

end ModalAlgebra

end
