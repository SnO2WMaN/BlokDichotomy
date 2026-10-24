module

public import BlokDichotomy.Kripke.Correspondence
public import BlokDichotomy.Propositional.Kripke.Completeness

/-!
# The Gödel translation and modal companions

The Gödel translation of intuitionistic formulas into modal ones, modal companions of
superintuitionistic logics, and the theorem that `𝐒𝟒` is a modal companion of `𝐈𝐧𝐭`.

## References

- [CZ98, §3.9, §9.6]
-/

@[expose] public section

universe u v

namespace Propositional

variable {κ : Type u} {α : Type v} {F : Frame κ} {A B : Formula α}

namespace Formula

/-- The Gödel translation.
- [CZ98, §3.9] -/
@[grind]
def gödelTranslate : Formula α → _root_.Formula α
  | #a    => □(#a)
  | ⊥     => ⊥
  | A ⋏ B => A.gödelTranslate ⋏ B.gödelTranslate
  | A ⋎ B => A.gödelTranslate ⋎ B.gödelTranslate
  | A 🡒 B => □(A.gödelTranslate 🡒 B.gödelTranslate)
scoped[Propositional] postfix:max "ᵍ" => Formula.gödelTranslate

@[simp, grind =] lemma gödelTranslate_atom {a : α} : (#a)ᵍ = □(#a) := rfl
@[simp, grind =] lemma gödelTranslate_bot : (⊥ : Formula α)ᵍ = ⊥ := rfl
@[simp, grind =] lemma gödelTranslate_and : (A ⋏ B)ᵍ = Aᵍ ⋏ Bᵍ := rfl
@[simp, grind =] lemma gödelTranslate_or : (A ⋎ B)ᵍ = Aᵍ ⋎ Bᵍ := rfl
@[simp, grind =] lemma gödelTranslate_imp : (A 🡒 B)ᵍ = □(Aᵍ 🡒 Bᵍ) := rfl

end Formula

/-- `M` is a modal companion of `L` if the Gödel translation embeds `L` into `M`.
- [CZ98, §9.6] -/
def _root_.NormalLogic.IsModalCompanion (M : NormalLogic α) (L : Logic α) : Prop :=
  ∀ A : Formula α, A ∈ L ↔ Aᵍ ∈ M

namespace Model

variable {M : _root_.Model κ α} {x : M.World}

/-- The intuitionistic model on the frame of a transitive modal model `M`, where `#a` is true at
`x` iff `□#a` is true at `x` in `M`. -/
def ofModal (M : _root_.Model κ α) [IsTrans κ M.Rel] : Propositional.Model κ α where
  toFrame := M.toFrame
  Val x a := x ⊩[M] □(#a)
  hereditary := by
    grind [_root_.Model.World.forces_box_of_rel];

/-- If the truth sets of `W` are those of `□#a` in `⟨F, V⟩`, then a formula is forced in the
intuitionistic model `⟨F, W⟩` iff its Gödel translation is forced in `⟨F, V⟩`. -/
lemma forces_gödelTranslate_iff_of_val [Std.Refl F.Rel] {V W : κ → α → Prop}
    {hW : ∀ {x y : κ}, F.Rel x y → ∀ {a}, W x a → W y a}
    (h : ∀ (x : κ) (a : α), W x a ↔ x ⊩[(⟨F, V⟩ : _root_.Model κ α)] □(#a))
    {x : κ} :
    x ⊩[(⟨F, W, hW⟩ : Propositional.Model κ α)] A ↔ x ⊩[(⟨F, V⟩ : _root_.Model κ α)] Aᵍ := by
  induction A generalizing x <;> grind;

/-- - [CZ98, Lemma 3.81] -/
theorem forces_ofModal_iff [IsPreorder κ M.Rel] : x ⊩[ofModal M] A ↔ x ⊩[M] Aᵍ := by
  exact forces_gödelTranslate_iff_of_val (F := M.toFrame) (V := M.Val')
    (hW := (ofModal M).hereditary) (fun _ _ => Iff.rfl);

end Model

/-- A reflexive transitive frame validates `Aᵍ` iff it validates `A`.
- [CZ98, Corollary 3.82] -/
theorem Frame.validates_gödelTranslate_iff [IsPreorder κ F.Rel] : F ⊧ Aᵍ ↔ F ⊧ A := by
  constructor;
  · intro h V hV x;
    have hV' : ∀ (x : κ) (a : α), V x a ↔ x ⊩[(⟨F, V⟩ : _root_.Model κ α)] □(#a) := by
      intro x a;
      rw [_root_.Model.World.forces_box];
      constructor;
      · exact fun hx y Rxy => hV Rxy hx;
      · exact fun hx => hx x (Std.Refl.refl x);
    exact (Propositional.Model.forces_gödelTranslate_iff_of_val (hW := hV) hV').mpr (h V x);
  · intro h V x;
    let M : _root_.Model κ α := ⟨F, V⟩;
    exact Propositional.Model.forces_ofModal_iff.mp
      (h _ (Propositional.Model.ofModal M).hereditary x);

/-- The Gödel translation embeds `𝐈𝐧𝐭` into `𝐒𝟒`.
- [CZ98, Theorem 3.83] -/
theorem gödelTranslate_mem_logicS4_iff : A ∈ 𝐈𝐧𝐭 ↔ Aᵍ ∈ 𝐒𝟒 := by
  rw [NormalLogic.mem_logicS4_iff, mem_logicInt_iff];
  constructor;
  · intro h κ' F _;
    exact Frame.validates_gödelTranslate_iff.mpr (h κ' F);
  · intro h κ' F _;
    exact Frame.validates_gödelTranslate_iff.mp (h F);

/-- `𝐒𝟒` is a modal companion of `𝐈𝐧𝐭`.
- [CZ98, Theorem 3.83, §9.6] -/
theorem logicS4_isModalCompanion_logicInt : (𝐒𝟒 : NormalLogic α).IsModalCompanion 𝐈𝐧𝐭 :=
  fun _ => gödelTranslate_mem_logicS4_iff

end Propositional

end
