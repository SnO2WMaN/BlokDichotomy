module

public import BlokDichotomy.Algebraic.Frame
public import BlokDichotomy.Kripke.Completeness

/-!
# The Lindenbaum algebra

The Lindenbaum algebra of a normal extension `L` of `𝐊`: formulas modulo `L`-provable equivalence.
It embeds into the dual algebra of the canonical frame of `L`, it validates exactly the formulas
of `L`, every valuation in an `L`-algebra lifts to a homomorphism from it, and so every normal
extension of `𝐊` is complete with respect to modal algebras.

## References

- [CZ98, Theorem 7.1, Theorem 7.2, Theorem 7.43, §7.7, Theorem 8.3]
-/

@[expose] public section

universe u v

namespace NormalLogic

open Formula Frame.DualAlgebra Model.World

variable {α : Type v} {L : NormalLogic α} [L.IsNExt 𝐊] {φ ψ : Formula α}

/-- `φ` and `ψ` are equivalent when `φ 🡘 ψ ∈ L`. -/
def equivSetoid (L : NormalLogic α) [L.IsNExt 𝐊] : Setoid (Formula α) where
  r φ ψ := φ 🡘 ψ ∈ L
  iseqv := ⟨fun _ => iff_refl, iff_symm, iff_trans⟩

/--
The Lindenbaum algebra of `L`: formulas modulo `L`-provable equivalence.
- [CZ98, §7.2, Theorem 7.2]
-/
def LindenbaumAlgebra (L : NormalLogic α) [L.IsNExt 𝐊] : Type v := Quotient (equivSetoid L)

/-- The valuation in the dual algebra of the canonical frame given by the canonical model. -/
def canonicalValuation (L : NormalLogic α) : α → L.canonicalModel.toFrame.DualAlgebra :=
  fun a => Frame.DualAlgebra.ofSet {x | L.canonicalModel.Val' x a}

omit [L.IsNExt 𝐊] in
lemma toSet_eval_canonicalValuation :
    toSet (φ.eval L.canonicalValuation) = {x | x ⊩[L.canonicalModel] φ} :=
  Frame.eval_dualAlgebra L.canonicalModel.Val' φ

lemma eval_canonicalValuation_eq_iff :
    φ.eval L.canonicalValuation = ψ.eval L.canonicalValuation ↔ φ 🡘 ψ ∈ L := by
  rw [mem_iff_canonicalModel_validates];
  constructor;
  · intro h x;
    have := congrArg toSet h;
    rw [toSet_eval_canonicalValuation, toSet_eval_canonicalValuation, Set.ext_iff] at this;
    simpa [forces_iff] using this x;
  · intro h;
    apply Frame.DualAlgebra.ext;
    rw [toSet_eval_canonicalValuation, toSet_eval_canonicalValuation];
    ext x;
    simpa [forces_iff] using h x;

namespace LindenbaumAlgebra

/-- The class of `φ` in the Lindenbaum algebra. -/
def mk (φ : Formula α) : L.LindenbaumAlgebra := Quotient.mk (equivSetoid L) φ

lemma mk_eq_mk : (mk φ : L.LindenbaumAlgebra) = mk ψ ↔ φ 🡘 ψ ∈ L := Quotient.eq

@[elab_as_elim, induction_eliminator]
lemma ind {motive : L.LindenbaumAlgebra → Prop} (h : ∀ φ, motive (mk φ)) (a) : motive a :=
  Quotient.ind h a

instance : HImp L.LindenbaumAlgebra :=
  ⟨Quotient.map₂ (· 🡒 ·) fun _ _ h₁ _ _ h₂ => imp_iff_congr h₁ h₂⟩
instance : Bot L.LindenbaumAlgebra := ⟨mk ⊥⟩
instance : Top L.LindenbaumAlgebra := ⟨mk ⊤⟩
instance : Compl L.LindenbaumAlgebra := ⟨fun a => a ⇨ ⊥⟩
instance : Max L.LindenbaumAlgebra := ⟨fun a b => aᶜ ⇨ b⟩
instance : Min L.LindenbaumAlgebra := ⟨fun a b => (a ⇨ bᶜ)ᶜ⟩
instance : SDiff L.LindenbaumAlgebra := ⟨fun a b => a ⊓ bᶜ⟩
instance : Dia L.LindenbaumAlgebra := ⟨Quotient.map (◇·) fun _ _ h => dia_congr h⟩

@[simp] lemma mk_imp : (mk (φ 🡒 ψ) : L.LindenbaumAlgebra) = mk φ ⇨ mk ψ := rfl
@[simp] lemma mk_bot : (mk ⊥ : L.LindenbaumAlgebra) = ⊥ := rfl
@[simp] lemma mk_top : (mk ⊤ : L.LindenbaumAlgebra) = ⊤ := rfl
@[simp] lemma mk_dia : (mk (◇φ) : L.LindenbaumAlgebra) = ◇mk φ := rfl

/-- The map sending the class of `φ` to its truth set in the canonical model. -/
def toDual : L.LindenbaumAlgebra → L.canonicalModel.toFrame.DualAlgebra :=
  Quotient.lift (·.eval L.canonicalValuation) fun _ _ h => eval_canonicalValuation_eq_iff.mpr h

@[simp] lemma toDual_mk : toDual (mk φ : L.LindenbaumAlgebra) = φ.eval L.canonicalValuation := rfl

lemma toDual_injective : Function.Injective (toDual : L.LindenbaumAlgebra → _) := by
  intro a b;
  induction a;
  induction b;
  simpa [mk_eq_mk] using eval_canonicalValuation_eq_iff.mp;

instance : LE L.LindenbaumAlgebra := ⟨fun a b => toDual a ≤ toDual b⟩
instance : LT L.LindenbaumAlgebra := ⟨fun a b => toDual a < toDual b⟩

lemma toDual_himp (a b : L.LindenbaumAlgebra) : toDual (a ⇨ b) = toDual a ⇨ toDual b := by
  induction a;
  induction b;
  rfl;

lemma toDual_bot : toDual (⊥ : L.LindenbaumAlgebra) = ⊥ := rfl

lemma toDual_top : toDual (⊤ : L.LindenbaumAlgebra) = ⊤ := eval_top

lemma toDual_compl (a : L.LindenbaumAlgebra) : toDual aᶜ = (toDual a)ᶜ :=
  (toDual_himp a ⊥).trans (himp_bot _)

lemma toDual_sup (a b : L.LindenbaumAlgebra) : toDual (a ⊔ b) = toDual a ⊔ toDual b := by
  change toDual (aᶜ ⇨ b) = _;
  rw [toDual_himp, toDual_compl, himp_eq, compl_compl, sup_comm];

lemma toDual_inf (a b : L.LindenbaumAlgebra) : toDual (a ⊓ b) = toDual a ⊓ toDual b := by
  change toDual (a ⇨ bᶜ)ᶜ = _;
  rw [toDual_compl, toDual_himp, toDual_compl, himp_eq, compl_sup, compl_compl, compl_compl,
    inf_comm];

lemma toDual_sdiff (a b : L.LindenbaumAlgebra) : toDual (a \ b) = toDual a \ toDual b := by
  change toDual (a ⊓ bᶜ) = _;
  rw [toDual_inf, toDual_compl, sdiff_eq];

lemma toDual_dia (a : L.LindenbaumAlgebra) : toDual (◇a) = ◇toDual a := by
  induction a;
  rfl;

instance : BooleanAlgebra L.LindenbaumAlgebra :=
  toDual_injective.booleanAlgebra _ Iff.rfl Iff.rfl toDual_sup toDual_inf toDual_top toDual_bot
    toDual_compl toDual_sdiff toDual_himp

/--
The Lindenbaum algebra is a modal algebra.
- [CZ98, Theorem 7.2]
-/
instance : ModalAlgebra L.LindenbaumAlgebra where
  dia_bot := toDual_injective <| by simp [toDual_dia, toDual_bot]
  dia_sup a b := toDual_injective <| by simp [toDual_dia, toDual_sup]

/--
The embedding of the Lindenbaum algebra into the dual algebra of the canonical frame.
- [CZ98, Theorem 8.3]
-/
def toDualHom : ModalAlgebraHom L.LindenbaumAlgebra L.canonicalModel.toFrame.DualAlgebra where
  toFun := toDual
  map_sup' := toDual_sup
  map_inf' := toDual_inf
  map_top' := toDual_top
  map_bot' := toDual_bot
  map_dia' := toDual_dia

lemma toDualHom_injective :
    Function.Injective (toDualHom : ModalAlgebraHom L.LindenbaumAlgebra _) :=
  toDual_injective

@[simp] lemma mk_neg : (mk (∼φ) : L.LindenbaumAlgebra) = (mk φ)ᶜ := rfl
@[simp] lemma mk_or : (mk (φ ⋎ ψ) : L.LindenbaumAlgebra) = mk φ ⊔ mk ψ := rfl
@[simp] lemma mk_and : (mk (φ ⋏ ψ) : L.LindenbaumAlgebra) = mk φ ⊓ mk ψ := rfl
@[simp] lemma mk_box : (mk (□φ) : L.LindenbaumAlgebra) = □mk φ := rfl

@[simp]
lemma mk_eq_top_iff : (mk φ : L.LindenbaumAlgebra) = ⊤ ↔ φ ∈ L := by
  rw [← mk_top, mk_eq_mk];
  exact ⟨fun h => mem_mdp verum_mem <| iff_mpr h,
    fun h => iff_of_imp (imp_of_mem verum_mem) (imp_of_mem h)⟩;

/-- The value of `φ` under the valuation `a ↦ [#a]` is the class of `φ`. -/
@[simp]
lemma eval_mk : φ.eval (fun a => (mk (#a) : L.LindenbaumAlgebra)) = mk φ := by
  induction φ <;> simp_all;

lemma eval_eq_mk_subst (v : α → L.LindenbaumAlgebra) :
    φ.eval v = mk (φ⟦fun a => (v a).out⟧) := by
  rw [← eval_mk, eval_subst];
  simp only [eval_mk];
  exact congrArg (φ.eval ·) <| funext fun a => (Quotient.out_eq (v a)).symm;

/--
The Lindenbaum algebra of `L` validates exactly the formulas of `L`.
- [CZ98, Theorem 7.1, Theorem 7.2]
-/
theorem validates_iff : L.LindenbaumAlgebra ⊧ φ ↔ φ ∈ L :=
  ⟨fun h => by simpa using h fun a => mk (#a),
    fun h v => by simpa [eval_eq_mk_subst] using mem_subst h⟩

lemma validatesLogic : L.LindenbaumAlgebra ⊧ L := fun _ => validates_iff.mpr

section Lift

variable {A : Type u} [ModalAlgebra A] (hA : A ⊧ L) (v : α → A)

/--
A valuation `v` in an `L`-algebra `A` lifts to the homomorphism `[φ] ↦ φ.eval v`.
- [CZ98, §7.7]
-/
def lift : ModalAlgebraHom L.LindenbaumAlgebra A where
  toFun := Quotient.lift (·.eval v) fun _ _ h => ModalAlgebra.validates_iff_iff.mp (hA _ h) v
  map_sup' a b := by induction a; induction b; exact eval_or
  map_inf' a b := by induction a; induction b; exact eval_and
  map_top' := eval_top
  map_bot' := rfl
  map_dia' a := by induction a; rfl

@[simp] lemma lift_mk : lift hA v (mk φ) = φ.eval v := rfl

lemma lift_mk_atom (a : α) : lift hA v (mk (#a)) = v a := rfl

end Lift

end LindenbaumAlgebra

lemma logic_lindenbaumAlgebra : (ModalAlgebra.logic L.LindenbaumAlgebra : NormalLogic α) = L :=
  SetLike.ext fun _ => LindenbaumAlgebra.validates_iff

/--
A formula belongs to `L` iff it is valid in every modal algebra for `L`.
- [CZ98, Theorem 7.43]
-/
theorem mem_iff_forall_modalAlgebra :
    φ ∈ L ↔ ∀ (A : Type v) [ModalAlgebra A], A ⊧ L → A ⊧ φ :=
  ⟨fun h _ _ hA => hA φ h,
    fun h => LindenbaumAlgebra.validates_iff.mp <| h _ LindenbaumAlgebra.validatesLogic⟩

end NormalLogic

end
