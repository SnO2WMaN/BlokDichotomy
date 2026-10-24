module

public import BlokDichotomy.Propositional.BlokEsakia.Quotient

/-!
# The main lemma

Let `G` be a general frame on a preorder validating `𝐆𝐫𝐳`. A formula refuted in `G` is refuted in
`σ ρ G`, the general frame with the same points whose admissible sets are the Boolean combinations
of the admissible upsets of `G`. Hence `σ ρ G` and `G` have the same logic.

## References

- [BC22, Lemma 4.1]
-/

@[expose] public section

universe u v

variable {κ : Type u} {α : Type v}

namespace GeneralFrame

open Formula

section

variable [DecidableEq α] {G : GeneralFrame κ} {V : G.World → α → Prop} {A : Formula α}
  {B C : Formula α} {x y : G.World}

/-- The valuation making `p` true exactly at the points whose `definableType` contains `#p`.
- [BC22, Lemma 4.1] -/
def definableValuation (G : GeneralFrame κ) (V : G.World → α → Prop) (A : Formula α)
    (x : G.World) (p : α) : Prop :=
  #p ∈ G.definableType V A x

private lemma not_bot_mem_definableType : ⊥ ∉ G.definableType V A x := by
  obtain ⟨y, hy⟩ := exists_typeOf_eq_definableType (G := G) (V := V) (A := A) (x := x);
  rw [← hy, mem_typeOf_iff];
  exact fun h => Model.World.not_forces_bot h.2

private lemma imp_mem_definableType_iff (h : (B 🡒 C) ∈ A.subformulas) :
    (B 🡒 C) ∈ G.definableType V A x ↔ (B ∈ G.definableType V A x → C ∈ G.definableType V A x) := by
  obtain ⟨y, hy⟩ := exists_typeOf_eq_definableType (G := G) (V := V) (A := A) (x := x);
  rw [← hy, mem_typeOf_iff, mem_typeOf_iff, mem_typeOf_iff, Model.World.forces_imp];
  have hB := mem_subformulas_of_imp_left h;
  have hC := mem_subformulas_of_imp_right h;
  grind

variable [IsPreorder κ G.Rel]

/-- The valuation `definableValuation` is admissible in `σ ρ G`. -/
lemma isAdmissible_definableValuation (hV : G.IsAdmissible V) :
    G.toIntuitionistic.toModal.IsAdmissible (G.definableValuation V A) := by
  intro p;
  have h₁ := BooleanSubalgebra.setOf_exists_mem
    (BooleanSubalgebra.closure G.toIntuitionistic.Adm)
    (A.subformulas.powerset.filter fun a => #p ∈ a)
    (P := fun a => {x | G.definableType V A x = a})
    fun a _ => preimage_definableType_mem hV a;
  have h₂ : {x | G.definableValuation V A x p} = {x | ∃ a ∈ A.subformulas.powerset.filter
      (fun a => #p ∈ a), x ∈ {x | G.definableType V A x = a}} := by
    ext x;
    simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_powerset];
    constructor;
    · intro h;
      exact ⟨G.definableType V A x, ⟨definableType_subset, h⟩, rfl⟩;
    · rintro ⟨a, ⟨_, ha⟩, rfl⟩;
      exact ha;
  rw [h₂];
  exact h₁

/-- If `x ≺ y` and `B` belongs to the type assigned to `y`, then `◇B` belongs to the type assigned
to `x`. -/
private lemma dia_mem_definableType_of_rel {B : Formula α} (h : ◇B ∈ A.subformulas)
    (Rxy : x ≺ y) (hy : B ∈ G.definableType V A y) : ◇B ∈ G.definableType V A x := by
  obtain ⟨y', hy'⟩ := exists_typeOf_eq_definableType (G := G) (V := V) (A := A) (x := y);
  have h₁ : A.TypeLE (G.definableType V A x) (G.typeOf V A y') := by
    rw [hy'];
    exact (definableType_typeEquiv (x := x)).1.trans <|
      (typeLE_typeOf_of_rel Rxy).trans (definableType_typeEquiv (x := y)).2;
  exact dia_mem_of_typeLE h₁ h (hy' ▸ hy)

/-- The truth lemma: a subformula of `A` is true at `x` under `definableValuation` iff it belongs to
the type assigned to `x`. -/
lemma forces_definableValuation_iff [Nonempty α] (hV : G.IsAdmissible V)
    (hGrz : G ⊧ (𝐆𝐫𝐳 : NormalLogic α)) {B : Formula α} (hB : B ∈ A.subformulas) (x : G.World) :
    x ⊩[G.model (G.definableValuation V A)] B ↔ B ∈ G.definableType V A x := by
  induction B generalizing x with
  | atom p => exact Iff.rfl;
  | falsum =>
    exact ⟨fun h => absurd h Model.World.not_forces_bot,
      fun h => absurd h not_bot_mem_definableType⟩;
  | imp B C ihB ihC =>
    have h₁ := ihB (mem_subformulas_of_imp_left hB);
    have h₂ := ihC (mem_subformulas_of_imp_right hB);
    rw [imp_mem_definableType_iff hB, Model.World.forces_imp];
    simp only [Model.World.NotForces, h₁, h₂];
    tauto
  | dia B ih =>
    have hB' : B ∈ A.subformulas := mem_subformulas_of_dia hB;
    rw [Model.World.forces_dia];
    constructor;
    · rintro ⟨y, Rxy, hy⟩;
      exact dia_mem_definableType_of_rel hB Rxy <| (ih hB' y).mp hy;
    · intro h;
      have h₁ : ◇B ∈ G.typeOf V A x := (definableType_typeEquiv (x := x)).2 B hB h;
      obtain ⟨y, Rxy, hy⟩ := Model.World.forces_dia.mp (mem_typeOf_iff.mp h₁).2;
      have hU : {z | G.typeOf V A z = G.typeOf V A y} ∈ G.Adm := preimage_typeOf_mem_adm hV _;
      obtain ⟨y', Ryy', hy'⟩ := exists_passive_of_grz
        (a := Classical.arbitrary α) (hGrz _ NormalLogic.axiomGrz) hU (rfl : y ∈ _);
      have h₂ : y' ∈ {z | G.typeOf V A z = G.typeOf V A y} := Frame.passive_subset hy';
      have h₃ : G.typeOf V A y' = G.typeOf V A y := h₂;
      have h₄ : y' ∈ G.toFrame.passive {z | G.typeOf V A z = G.typeOf V A y'} := by
        rw [h₃];
        exact hy';
      have h₅ : B ∈ G.definableType V A y' := by
        rw [definableType_eq_of_passive h₄, h₃];
        exact mem_typeOf_iff.mpr ⟨hB', hy⟩;
      exact ⟨y', Frame.rel_trans Rxy Ryy', (ih hB' y').mpr h₅⟩

omit [DecidableEq α] in
/-- A formula refuted in a general frame on a preorder validating `𝐆𝐫𝐳` is refuted in `σ ρ G`.
- [BC22, Lemma 4.1] -/
theorem not_validates_toIntuitionistic_toModal_of_not_validates [Nonempty α]
    (hGrz : G ⊧ (𝐆𝐫𝐳 : NormalLogic α)) (h : G ⊭ A) : G.toIntuitionistic.toModal ⊭ A := by
  classical
  by_contra hσ;
  apply h;
  intro V hV x;
  by_contra hx;
  obtain ⟨w, _, hw⟩ := exists_passive_of_grz (a := Classical.arbitrary α)
    (hGrz _ NormalLogic.axiomGrz) (preimage_typeOf_mem_adm (A := A) hV (G.typeOf V A x))
    (rfl : x ∈ _);
  have h₁ : w ∈ {z | G.typeOf V A z = G.typeOf V A x} := Frame.passive_subset hw;
  have h₂ : G.typeOf V A w = G.typeOf V A x := h₁;
  have h₃ : w ∈ G.toFrame.passive {z | G.typeOf V A z = G.typeOf V A w} := by
    rw [h₂];
    exact hw;
  have h₄ : A ∉ G.definableType V A w := by
    rw [definableType_eq_of_passive h₃, h₂, mem_typeOf_iff];
    exact fun h => hx h.2;
  exact h₄ <| (forces_definableValuation_iff hV hGrz Formula.mem_subformulas_self w).mp <|
    hσ _ (isAdmissible_definableValuation hV) w

omit [DecidableEq α] in
/-- The logic of `σ ρ G` is the logic of `G`.
- [BC22, Lemma 4.1] -/
theorem logic_toIntuitionistic_toModal_eq [Nonempty α] (hGrz : G ⊧ (𝐆𝐫𝐳 : NormalLogic α)) :
    (G.toIntuitionistic.toModal.logic : NormalLogic α) = G.logic := by
  apply le_antisymm _ G.logic_le_toIntuitionistic_toModal;
  intro A hA;
  by_contra h;
  exact not_validates_toIntuitionistic_toModal_of_not_validates hGrz h hA

end

end GeneralFrame

end
