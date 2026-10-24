module

public import BlokDichotomy.Algebraic.Operations
public import BlokDichotomy.GeneralFrame.Basic

/-!
# Dual algebras of frames

The dual algebra of a Kripke frame, the powerset algebra with `◇` given by `Frame.diaSet`, and
the dual algebra of a general frame, its subalgebra of admissible sets. A frame and its dual
algebra validate the same formulas.

## References

- [CZ98, Theorem 7.46, Proposition 8.1]
-/

@[expose] public section

universe u v

variable {κ : Type u} {α : Type v}

namespace Frame

variable {F : Frame κ} {X Y : Set F.World}

@[simp] lemma diaSet_empty : F.diaSet ∅ = ∅ := by simp [diaSet]

lemma diaSet_union : F.diaSet (X ∪ Y) = F.diaSet X ∪ F.diaSet Y := by
  ext w;
  simp only [diaSet, Set.mem_union, Set.mem_ofPred_eq];
  grind;

/--
The dual algebra `F⁺` of a Kripke frame: the subsets of its worlds, with `◇X` the set of worlds
seeing a point of `X`.
- [CZ98, Theorem 7.46]
-/
def DualAlgebra (F : Frame κ) : Type u := Set F.World

instance : ModalAlgebra F.DualAlgebra where
  toBooleanAlgebra := inferInstanceAs (BooleanAlgebra (Set F.World))
  dia := F.diaSet
  dia_bot := diaSet_empty
  dia_sup _ _ := diaSet_union

namespace DualAlgebra

/-- The underlying set of an element of the dual algebra. -/
def toSet : F.DualAlgebra → Set F.World := id

/-- A set of worlds, regarded as an element of the dual algebra. -/
def ofSet : Set F.World → F.DualAlgebra := id

@[simp] lemma toSet_ofSet : toSet (ofSet X) = X := rfl

@[simp] lemma toSet_bot : toSet (⊥ : F.DualAlgebra) = ∅ := rfl
@[simp] lemma toSet_himp (a b : F.DualAlgebra) : toSet (a ⇨ b) = toSet b ∪ (toSet a)ᶜ := himp_eq
@[simp] lemma toSet_dia (a : F.DualAlgebra) : toSet (◇a) = F.diaSet (toSet a) := rfl
@[simp] lemma toSet_top : toSet (⊤ : F.DualAlgebra) = Set.univ := rfl

lemma ext {a b : F.DualAlgebra} (h : toSet a = toSet b) : a = b := h

end DualAlgebra

open Model.World DualAlgebra

/--
The value of a formula in the dual algebra under a valuation is its truth set.
- [CZ98, Theorem 7.46]
-/
theorem eval_dualAlgebra (V : F.World → α → Prop) (φ : Formula α) :
    toSet (φ.eval fun a => ofSet {w | V w a}) = {w | w ⊩[⟨F, V⟩] φ} := by
  induction φ with
  | atom a => rfl;
  | falsum => simp;
  | imp φ ψ ihφ ihψ =>
    ext w;
    simp [ihφ, ihψ, forces_imp, or_comm];
  | dia φ ih =>
    ext w;
    simp [ih, diaSet, forces_dia];

/--
A frame and its dual algebra validate the same formulas.
- [CZ98, Theorem 7.46]
-/
theorem dualAlgebra_validates_iff {φ : Formula α} : F.DualAlgebra ⊧ φ ↔ F ⊧ φ := by
  constructor;
  · intro h V x;
    have h₁ := congrArg toSet <| h fun a => ofSet {w | V w a};
    rw [eval_dualAlgebra, toSet_top] at h₁;
    exact Set.eq_univ_iff_forall.mp h₁ x;
  · intro h v;
    apply DualAlgebra.ext;
    have := eval_dualAlgebra (fun w a => w ∈ toSet (v a)) φ;
    simp only [Set.ofPred_mem_eq] at this;
    rw [show (fun a => ofSet (toSet (v a))) = v from rfl] at this;
    rw [this, toSet_top, Set.eq_univ_iff_forall];
    exact h _;

lemma logic_dualAlgebra : (ModalAlgebra.logic F.DualAlgebra : NormalLogic α) = F.logic :=
  SetLike.ext fun _ => dualAlgebra_validates_iff

end Frame

namespace GeneralFrame

open Frame.DualAlgebra

variable {G : GeneralFrame κ}

/-- The admissible sets of a general frame, as a subalgebra of the dual algebra of its frame. -/
def admSubalgebra (G : GeneralFrame κ) : ModalSubalgebra G.toFrame.DualAlgebra where
  carrier := G.Adm
  supClosed' _ hX _ hY := G.union_mem hX hY
  infClosed' _ hX _ hY := G.inter_mem hX hY
  compl_mem' := G.compl_mem
  bot_mem' := G.empty_mem
  dia_mem' := G.diaSet_mem

/--
The dual algebra `G⁺` of a general frame: its admissible sets.
- [CZ98, Proposition 8.1]
-/
abbrev DualAlgebra (G : GeneralFrame κ) : Type u := G.admSubalgebra

open Model.World

/--
A general frame and its dual algebra validate the same formulas.
- [CZ98, §8.1]
-/
theorem dualAlgebra_validates_iff {φ : Formula α} : G.DualAlgebra ⊧ φ ↔ G ⊧ φ := by
  constructor;
  · intro h V hV x;
    have h₁ := congrArg (fun a => toSet (G.admSubalgebra.subtype a)) <|
      h fun a => ⟨ofSet {w | V w a}, hV a⟩;
    simp only [Formula.eval_hom, map_top] at h₁;
    rw [show (G.admSubalgebra.subtype ∘ fun a => (⟨ofSet {w | V w a}, hV a⟩ : G.DualAlgebra)) =
      fun a => ofSet {w | V w a} from rfl, Frame.eval_dualAlgebra, toSet_top] at h₁;
    exact Set.eq_univ_iff_forall.mp h₁ x;
  · intro h v;
    apply G.admSubalgebra.subtype_injective;
    rw [Formula.eval_hom, map_top];
    apply Frame.DualAlgebra.ext;
    have := Frame.eval_dualAlgebra (F := G.toFrame) (fun w a => w ∈ toSet (v a).1) φ;
    simp only [Set.ofPred_mem_eq] at this;
    rw [show (G.admSubalgebra.subtype ∘ v) = fun a => ofSet (toSet (v a).1) from rfl, this,
      toSet_top, Set.eq_univ_iff_forall];
    exact h _ (fun a => (v a).2);

lemma logic_dualAlgebra : (ModalAlgebra.logic G.DualAlgebra : NormalLogic α) = G.logic :=
  SetLike.ext fun _ => dualAlgebra_validates_iff

end GeneralFrame

end
