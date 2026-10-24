module

public import BlokDichotomy.Propositional.GeneralFrame.Companion
public import BlokDichotomy.ToMathlib.Order.BooleanSubalgebra

/-!
# The main lemma

Let `G` be a general frame on a preorder validating `𝐆𝐫𝐳`. A formula refuted in `G` is refuted in
`σ ρ G`, the general frame with the same points whose admissible sets are the Boolean combinations
of the admissible upward closed sets of `G`. Hence `σ ρ G` and `G` have the same logic.

The file defines the points of an admissible set `U` that are passive in `U` (one cannot leave `U`
from them and come back), the type of a point under a valuation (the subformulas of a formula `A`
true at it) with its preorder, and the definable type of a point.

## References

- [BC22, §1.5]
- [BC22, Lemma 4.1]
-/

@[expose] public section

namespace Modal

universe u v

variable {κ : Type u} {α : Type v}

/-- The points of `U` from which one cannot leave `U` and come back.
- [BC22, §1.5] -/
def Frame.passive (F : Frame κ) (U : Set F.World) : Set F.World :=
  F.diaSet U ∩ F.boxSet (U ∪ F.boxSet Uᶜ)

namespace Frame

variable {F : Frame κ} {U : Set F.World} {y : F.World}

section

variable [IsPreorder _ F.Rel]

lemma mem_passive_iff :
    y ∈ F.passive U ↔ y ∈ U ∧ ∀ u v : F.World, y ≺ u → u ≺ v → u ∉ U → v ∉ U := by
  constructor;
  · rintro ⟨⟨v, Ryv, hv⟩, hbox⟩;
    have hyU : y ∈ U := by
      rcases hbox y (rel_refl y) with hy | hy;
      · exact hy;
      · exact absurd hv (hy v Ryv);
    and_intros;
    · exact hyU;
    · intro u w Ryu Ruw hu;
      rcases hbox u Ryu with hu' | hu';
      · exact absurd hu' hu;
      · exact hu' w Ruw;
  · rintro ⟨hyU, h⟩;
    and_intros;
    · exact ⟨y, rel_refl y, hyU⟩;
    · intro u Ryu;
      by_cases hu : u ∈ U;
      · exact Or.inl hu;
      · exact Or.inr fun v Ruv => h u v Ryu Ruv hu;

lemma passive_subset : F.passive U ⊆ U := fun _ hy => (mem_passive_iff.mp hy).1

end

end Frame

namespace GeneralFrame

variable {G : GeneralFrame κ} [IsPreorder _ G.Rel] {U : Set G.World}

/-- The passive points of an admissible set are admissible in `σ ρ G`. -/
lemma passive_mem_toIntuitionistic_toModal (hU : U ∈ G.Adm) :
    G.toFrame.passive U ∈ G.toIntuitionistic.toModal.Adm := by
  have h₁ : G.toFrame.boxSet Uᶜ ∈ G.toIntuitionistic.toModal.Adm :=
    Propositional.GeneralFrame.subset_toModal_adm (G.boxSet_mem_upAdm (G.compl_mem hU));
  have h₂ : G.toFrame.boxSet (U ∪ G.toFrame.boxSet Uᶜ) ∈ G.toIntuitionistic.toModal.Adm :=
    Propositional.GeneralFrame.subset_toModal_adm
      (G.boxSet_mem_upAdm (G.union_mem hU (G.boxSet_mem (G.compl_mem hU))));
  have h₃ : G.toFrame.diaSet U ∈ G.toIntuitionistic.toModal.Adm := by
    rw [Frame.diaSet_eq];
    exact G.toIntuitionistic.toModal.compl_mem h₁;
  exact G.toIntuitionistic.toModal.inter_mem h₃ h₂

/-- Under the Grzegorczyk axiom, every point of an admissible set `U` has a passive point of `U`
above it.
- [BC22, Theorem 1.12] -/
lemma exists_passive_of_grz {a : α} (hGrz : G ⊧ □(□(#a 🡒 □#a) 🡒 #a) 🡒 #a) (hU : U ∈ G.Adm)
    {x : G.World} (hx : x ∈ U) : ∃ y : G.World, x ≺ y ∧ y ∈ G.toFrame.passive U := by
  have hV : G.IsAdmissible fun w (_ : α) => w ∉ U := fun _ => G.compl_mem hU;
  have h₁ := hGrz _ hV x;
  rw [Model.World.forces_imp] at h₁;
  rcases h₁ with h₁ | h₁;
  · rw [Model.World.not_forces_box] at h₁;
    obtain ⟨y, Rxy, hy⟩ := h₁;
    rw [Model.World.not_forces_imp, Model.World.forces_box] at hy;
    have h₂ : y ∈ U := by
      by_contra hyU;
      exact hy.2 hyU;
    have h₃ : ∀ u v : G.World, y ≺ u → u ≺ v → u ∉ U → v ∉ U := by
      intro u v Ryu Ruv hu;
      rcases (Model.World.forces_imp.mp (hy.1 u Ryu)) with h | h;
      · exact absurd (not_not.mp h) hu;
      · exact (Model.World.forces_box.mp h) v Ruv;
    exact ⟨y, Rxy, Frame.mem_passive_iff.mpr ⟨h₂, h₃⟩⟩;
  · exact absurd hx h₁

end GeneralFrame

section

variable [DecidableEq α]

namespace Formula

/-- `a ⊑ b`: every `◇`-subformula of `A` in `b` is in `a`. -/
def TypeLE (A : Formula α) (a b : Finset (Formula α)) : Prop :=
  ∀ B, ◇B ∈ A.subformulas → ◇B ∈ b → ◇B ∈ a

/-- `a ≡ b`: `a ⊑ b` and `b ⊑ a`. -/
def TypeEquiv (A : Formula α) (a b : Finset (Formula α)) : Prop :=
  A.TypeLE a b ∧ A.TypeLE b a

variable {A : Formula α} {a b c : Finset (Formula α)}

lemma TypeLE.refl (A : Formula α) (a : Finset (Formula α)) : A.TypeLE a a := fun _ _ h => h

lemma TypeLE.trans (h₁ : A.TypeLE a b) (h₂ : A.TypeLE b c) : A.TypeLE a c :=
  fun B hB hc => h₁ B hB <| h₂ B hB hc

lemma TypeEquiv.refl (A : Formula α) (a : Finset (Formula α)) : A.TypeEquiv a a :=
  ⟨TypeLE.refl A a, TypeLE.refl A a⟩

lemma TypeEquiv.symm (h : A.TypeEquiv a b) : A.TypeEquiv b a := ⟨h.2, h.1⟩

lemma TypeEquiv.trans (h₁ : A.TypeEquiv a b) (h₂ : A.TypeEquiv b c) : A.TypeEquiv a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

end Formula

namespace GeneralFrame

open Formula

/-- The type of `x`: the subformulas of `A` true at `x`.
- [BC22, Lemma 4.1] -/
noncomputable def typeOf (G : GeneralFrame κ) (V : G.World → α → Prop) (A : Formula α)
    (x : G.World) : Finset (Formula α) :=
  open Classical in A.subformulas.filter fun B => x ⊩[G.model V] B

variable {G : GeneralFrame κ} {V : G.World → α → Prop} {A : Formula α} {B : Formula α}
  {a b : Finset (Formula α)} {x y : G.World}

lemma mem_typeOf_iff : B ∈ G.typeOf V A x ↔ B ∈ A.subformulas ∧ x ⊩[G.model V] B := by
  simp [typeOf]

lemma typeOf_subset : G.typeOf V A x ⊆ A.subformulas := fun _ h => (mem_typeOf_iff.mp h).1

section

variable [IsPreorder _ G.Rel]

/-- If `x ≺ y` then `t(x) ⊑ t(y)`. -/
lemma typeLE_typeOf_of_rel (Rxy : x ≺ y) : A.TypeLE (G.typeOf V A x) (G.typeOf V A y) := by
  intro B hB hy;
  rw [mem_typeOf_iff] at hy ⊢;
  exact ⟨hB, Model.World.forces_dia_of_rel hy.2 Rxy⟩

/-- If `a ⊑ t(y)`, `◇B ∈ Sub A` and `B ∈ t(y)` then `◇B ∈ a`. -/
lemma dia_mem_of_typeLE (h : A.TypeLE a (G.typeOf V A y)) (hB : ◇B ∈ A.subformulas)
    (hy : B ∈ G.typeOf V A y) : ◇B ∈ a := by
  apply h B hB;
  rw [mem_typeOf_iff] at hy ⊢;
  exact ⟨hB, Model.World.forces_dia.mpr ⟨y, Frame.rel_refl y, hy.2⟩⟩

end

lemma typeOf_eq_iff (ha : a ⊆ A.subformulas) :
    G.typeOf V A x = a ↔ ∀ B ∈ A.subformulas, (x ⊩[G.model V] B ↔ B ∈ a) := by
  constructor;
  · intro h B hB;
    rw [← h, mem_typeOf_iff];
    constructor;
    · intro hx;
      exact ⟨hB, hx⟩;
    · intro hx;
      exact hx.2;
  · intro h;
    ext B;
    rw [mem_typeOf_iff];
    constructor;
    · rintro ⟨hB, hx⟩;
      exact (h B hB).mp hx;
    · intro hB;
      exact ⟨ha hB, (h B (ha hB)).mpr hB⟩

/-- The set of points of a given type is admissible. -/
lemma preimage_typeOf_mem_adm (hV : G.IsAdmissible V) (a : Finset (Formula α)) :
    {x | G.typeOf V A x = a} ∈ G.Adm := by
  by_cases ha : a ⊆ A.subformulas;
  · have h₁ : ∀ B ∈ A.subformulas,
        (if B ∈ a then {x | x ⊩[G.model V] B} else {x | x ⊩[G.model V] B}ᶜ) ∈
          G.admBooleanSubalgebra := by
      intro B _;
      split_ifs;
      · exact truthSet_mem hV B;
      · exact G.compl_mem <| truthSet_mem hV B;
    have h₂ := BooleanSubalgebra.setOf_forall_mem G.admBooleanSubalgebra A.subformulas h₁;
    have h₃ : {x | G.typeOf V A x = a} =
        {x | ∀ B ∈ A.subformulas,
          x ∈ if B ∈ a then {x | x ⊩[G.model V] B} else {x | x ⊩[G.model V] B}ᶜ} := by
      ext x;
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, typeOf_eq_iff ha];
      apply forall₂_congr;
      intro B _;
      by_cases hB : B ∈ a <;> simp [hB];
    rw [h₃];
    exact h₂
  · have h₁ : {x | G.typeOf V A x = a} = ∅ := by
      ext x;
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false];
      by_contra h;
      subst h;
      exact ha typeOf_subset;
    rw [h₁];
    exact G.empty_mem

section

variable [IsPreorder _ G.Rel]

omit [DecidableEq α] in
/-- The set of points not satisfying `◇B` is an admissible upward closed set of `G`. -/
private lemma notForces_dia_mem (hV : G.IsAdmissible V) (B : Formula α) :
    {x | x ⊮[G.model V] ◇B} ∈ G.toIntuitionistic.toModal.Adm := by
  have h₁ : {x | x ⊮[G.model V] ◇B} = G.toFrame.boxSet {x | x ⊩[G.model V] B}ᶜ := by
    ext x;
    simp [Frame.boxSet, Model.World.not_forces_dia];
  rw [h₁];
  exact Propositional.GeneralFrame.subset_toModal_adm
    (boxSet_mem_upAdm (G.compl_mem (truthSet_mem hV B)))

/-- The set of points whose type is above `a` is admissible in `σ ρ G`. -/
lemma typeLE_left_mem (hV : G.IsAdmissible V) (a : Finset (Formula α)) :
    {x | A.TypeLE a (G.typeOf V A x)} ∈ G.toIntuitionistic.toModal.Adm := by
  have h₁ := BooleanSubalgebra.setOf_forall_mem
    (BooleanSubalgebra.closure G.toIntuitionistic.Adm)
    (A.subformulas.filter fun B => ◇B ∈ A.subformulas ∧ ◇B ∉ a)
    (P := fun B => {x | x ⊮[G.model V] ◇B}) fun B _ => notForces_dia_mem hV B;
  have h₂ : {x | A.TypeLE a (G.typeOf V A x)} = {x | ∀ B ∈ A.subformulas.filter
      (fun B => ◇B ∈ A.subformulas ∧ ◇B ∉ a), x ∈ {x | x ⊮[G.model V] ◇B}} := by
    ext x;
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq];
    constructor;
    · intro h B hB hx;
      rw [Finset.mem_filter] at hB;
      exact hB.2.2 <| h B hB.2.1 <| mem_typeOf_iff.mpr ⟨hB.2.1, hx⟩;
    · intro h B hB hb;
      by_contra hnot;
      exact h B (Finset.mem_filter.mpr ⟨mem_subformulas_of_dia hB, hB, hnot⟩)
        (mem_typeOf_iff.mp hb).2;
  rw [h₂];
  exact h₁

/-- The set of points whose type is below `a` is admissible in `σ ρ G`. -/
lemma typeLE_right_mem (hV : G.IsAdmissible V) (a : Finset (Formula α)) :
    {x | A.TypeLE (G.typeOf V A x) a} ∈ G.toIntuitionistic.toModal.Adm := by
  have h₁ := BooleanSubalgebra.setOf_forall_mem
    (BooleanSubalgebra.closure G.toIntuitionistic.Adm)
    (A.subformulas.filter fun B => ◇B ∈ A.subformulas ∧ ◇B ∈ a)
    (P := fun B => {x | x ⊮[G.model V] ◇B}ᶜ) fun B _ =>
      (BooleanSubalgebra.closure G.toIntuitionistic.Adm).compl_mem (notForces_dia_mem hV B);
  have h₂ : {x | A.TypeLE (G.typeOf V A x) a} = {x | ∀ B ∈ A.subformulas.filter
      (fun B => ◇B ∈ A.subformulas ∧ ◇B ∈ a), x ∈ {x | x ⊮[G.model V] ◇B}ᶜ} := by
    ext x;
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq];
    constructor;
    · intro h B hB;
      rw [Finset.mem_filter] at hB;
      exact not_not.mpr (mem_typeOf_iff.mp (h B hB.2.1 hB.2.2)).2;
    · intro h B hB hb;
      exact mem_typeOf_iff.mpr ⟨hB, not_not.mp
        (h B (Finset.mem_filter.mpr ⟨mem_subformulas_of_dia hB, hB, hb⟩))⟩;
  rw [h₂];
  exact h₁

/-- The preimage of a cluster of types is a Boolean combination of admissible upward closed sets. -/
lemma typeEquiv_mem (hV : G.IsAdmissible V) (a : Finset (Formula α)) :
    {x | A.TypeEquiv (G.typeOf V A x) a} ∈ G.toIntuitionistic.toModal.Adm :=
  G.toIntuitionistic.toModal.inter_mem (typeLE_right_mem hV a) (typeLE_left_mem hV a)

end

/-- A representative of the cluster of `a` that is the type of some point. -/
noncomputable def rep (G : GeneralFrame κ) (V : G.World → α → Prop) (A : Formula α)
    (a : Finset (Formula α)) : Finset (Formula α) :=
  Classical.epsilon fun b => A.TypeEquiv b a ∧ ∃ y : G.World, G.typeOf V A y = b

lemma rep_spec (h : ∃ y : G.World, A.TypeEquiv (G.typeOf V A y) a) :
    A.TypeEquiv (G.rep V A a) a ∧ ∃ y : G.World, G.typeOf V A y = G.rep V A a := by
  obtain ⟨y, hy⟩ := h;
  exact Classical.epsilon_spec (p := fun b => A.TypeEquiv b a ∧ ∃ y : G.World, G.typeOf V A y = b)
    ⟨G.typeOf V A y, hy, y, rfl⟩

lemma rep_congr (h : A.TypeEquiv a b) : G.rep V A a = G.rep V A b := by
  unfold rep;
  congr 1;
  funext c;
  apply propext;
  constructor;
  · rintro ⟨h₁, h₂⟩;
    exact ⟨h₁.trans h, h₂⟩;
  · rintro ⟨h₁, h₂⟩;
    exact ⟨h₁.trans h.symm, h₂⟩

/-- The type of `x` if `x` is passive in the set of points of its type, and the representative of
its cluster otherwise.
- [BC22, Lemma 4.1] -/
noncomputable def definableType (G : GeneralFrame κ) (V : G.World → α → Prop) (A : Formula α)
    (x : G.World) : Finset (Formula α) :=
  open Classical in
  if x ∈ G.toFrame.passive {y | G.typeOf V A y = G.typeOf V A x} then G.typeOf V A x
  else G.rep V A (G.typeOf V A x)

lemma definableType_eq_of_passive
    (h : x ∈ G.toFrame.passive {y | G.typeOf V A y = G.typeOf V A x}) :
    G.definableType V A x = G.typeOf V A x := by
  simp [definableType, h]

lemma definableType_eq_rep_of_not_passive
    (h : x ∉ G.toFrame.passive {y | G.typeOf V A y = G.typeOf V A x}) :
    G.definableType V A x = G.rep V A (G.typeOf V A x) := by
  simp [definableType, h]

lemma definableType_typeEquiv : A.TypeEquiv (G.definableType V A x) (G.typeOf V A x) := by
  by_cases h : x ∈ G.toFrame.passive {y | G.typeOf V A y = G.typeOf V A x};
  · rw [definableType_eq_of_passive h];
    exact TypeEquiv.refl A _;
  · rw [definableType_eq_rep_of_not_passive h];
    exact (rep_spec ⟨x, TypeEquiv.refl A _⟩).1

lemma exists_typeOf_eq_definableType : ∃ y : G.World, G.typeOf V A y = G.definableType V A x := by
  by_cases h : x ∈ G.toFrame.passive {y | G.typeOf V A y = G.typeOf V A x};
  · exact ⟨x, (definableType_eq_of_passive h).symm⟩;
  · rw [definableType_eq_rep_of_not_passive h];
    exact (rep_spec ⟨x, TypeEquiv.refl A _⟩).2

lemma definableType_subset : G.definableType V A x ⊆ A.subformulas := by
  obtain ⟨y, hy⟩ := exists_typeOf_eq_definableType (G := G) (V := V) (A := A) (x := x);
  rw [← hy];
  exact typeOf_subset

section

variable [IsPreorder _ G.Rel]

private lemma definableType_eq_iff :
    G.definableType V A x = a ↔
      x ∈ G.toFrame.passive {y | G.typeOf V A y = a} ∨
      (A.TypeEquiv (G.typeOf V A x) a ∧ G.rep V A a = a ∧
        ∀ b ∈ A.subformulas.powerset, x ∉ G.toFrame.passive {y | G.typeOf V A y = b}) := by
  constructor;
  · intro h;
    by_cases hx : x ∈ G.toFrame.passive {y | G.typeOf V A y = G.typeOf V A x};
    · rw [definableType_eq_of_passive hx] at h;
      rw [← h];
      exact Or.inl hx;
    · have h₁ := definableType_eq_rep_of_not_passive hx;
      have h₂ : A.TypeEquiv (G.typeOf V A x) a := by
        have := (rep_spec (G := G) (V := V) (a := G.typeOf V A x) ⟨x, TypeEquiv.refl A _⟩).1;
        rw [← h₁, h] at this;
        exact this.symm;
      have h₃ : G.rep V A a = a := (rep_congr h₂.symm).trans (h₁.symm.trans h);
      have h₄ : ∀ b ∈ A.subformulas.powerset,
          x ∉ G.toFrame.passive {y | G.typeOf V A y = b} := by
        intro b _ hb;
        have h₅ : x ∈ {y | G.typeOf V A y = b} := Frame.passive_subset hb;
        have : G.typeOf V A x = b := h₅;
        subst this;
        exact hx hb;
      exact Or.inr ⟨h₂, h₃, h₄⟩
  · rintro (h | ⟨h₁, h₂, h₃⟩);
    · have h₁ : x ∈ {y | G.typeOf V A y = a} := Frame.passive_subset h;
      have : G.typeOf V A x = a := h₁;
      subst this;
      exact definableType_eq_of_passive h;
    · have h₄ : x ∉ G.toFrame.passive {y | G.typeOf V A y = G.typeOf V A x} :=
        h₃ _ (Finset.mem_powerset.mpr typeOf_subset);
      rw [definableType_eq_rep_of_not_passive h₄, rep_congr h₁, h₂]

/-- The set of points sent to a given type is a Boolean combination of admissible upward closed
sets. -/
lemma preimage_definableType_mem (hV : G.IsAdmissible V) (a : Finset (Formula α)) :
    {x | G.definableType V A x = a} ∈ G.toIntuitionistic.toModal.Adm := by
  have h₁ : ∀ b, G.toFrame.passive {y | G.typeOf V A y = b} ∈
      BooleanSubalgebra.closure G.toIntuitionistic.Adm :=
    fun b => passive_mem_toIntuitionistic_toModal (preimage_typeOf_mem_adm hV b);
  have h₂ := BooleanSubalgebra.setOf_exists_mem (BooleanSubalgebra.closure G.toIntuitionistic.Adm)
    A.subformulas.powerset (P := fun b => G.toFrame.passive {y | G.typeOf V A y = b})
    fun b _ => h₁ b;
  have h₃ : {x | G.rep V A a = a} ∈ BooleanSubalgebra.closure G.toIntuitionistic.Adm := by
    by_cases h : G.rep V A a = a;
    · simp only [h, Set.ofPred_true];
      exact (BooleanSubalgebra.closure G.toIntuitionistic.Adm).top_mem;
    · simp only [h, Set.ofPred_false];
      exact (BooleanSubalgebra.closure G.toIntuitionistic.Adm).bot_mem;
  have h₄ : {x | G.definableType V A x = a} =
      G.toFrame.passive {y | G.typeOf V A y = a} ∪ ({x | A.TypeEquiv (G.typeOf V A x) a} ∩
        ({x | G.rep V A a = a} ∩ {x | ∃ b ∈ A.subformulas.powerset,
          x ∈ G.toFrame.passive {y | G.typeOf V A y = b}}ᶜ)) := by
    ext x;
    rw [Set.mem_ofPred_eq, definableType_eq_iff];
    simp;
  rw [h₄];
  exact G.toIntuitionistic.toModal.union_mem (h₁ a) <| G.toIntuitionistic.toModal.inter_mem
    (typeEquiv_mem hV a) <| G.toIntuitionistic.toModal.inter_mem h₃
    (G.toIntuitionistic.toModal.compl_mem h₂)

end

end GeneralFrame

end

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
  by_contra h;
  exact Model.World.not_forces_bot h.2

private lemma imp_mem_definableType_iff (h : (B 🡒 C) ∈ A.subformulas) :
    (B 🡒 C) ∈ G.definableType V A x ↔ (B ∈ G.definableType V A x → C ∈ G.definableType V A x) := by
  obtain ⟨y, hy⟩ := exists_typeOf_eq_definableType (G := G) (V := V) (A := A) (x := x);
  rw [← hy, mem_typeOf_iff, mem_typeOf_iff, mem_typeOf_iff, Model.World.forces_imp];
  have hB := mem_subformulas_of_imp_left h;
  have hC := mem_subformulas_of_imp_right h;
  grind

variable [IsPreorder _ G.Rel]

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

/-- If `◇B` belongs to the type assigned to `x` and the truth lemma holds for `B`, then `x` sees
a point where `B` is true. -/
private lemma exists_rel_forces_of_dia_mem_definableType [Nonempty α] (hV : G.IsAdmissible V)
    (hGrz : G ⊧ logicGrz (α := α)) (hB : ◇B ∈ A.subformulas)
    (ih : ∀ y, y ⊩[G.model (G.definableValuation V A)] B ↔ B ∈ G.definableType V A y)
    (h : ◇B ∈ G.definableType V A x) : ∃ y, x ≺ y ∧ y ⊩[G.model (G.definableValuation V A)] B := by
  have hB' : B ∈ A.subformulas := mem_subformulas_of_dia hB;
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
  exact ⟨y', Frame.rel_trans Rxy Ryy', (ih y').mpr h₅⟩

/-- The truth lemma: a subformula of `A` is true at `x` under `definableValuation` iff it belongs to
the type assigned to `x`. -/
lemma forces_definableValuation_iff [Nonempty α] (hV : G.IsAdmissible V)
    (hGrz : G ⊧ logicGrz (α := α)) {B : Formula α} (hB : B ∈ A.subformulas) (x : G.World) :
    x ⊩[G.model (G.definableValuation V A)] B ↔ B ∈ G.definableType V A x := by
  induction B generalizing x with
  | atom p => exact Iff.rfl;
  | falsum =>
    constructor;
    · intro h;
      exact absurd h Model.World.not_forces_bot;
    · intro h;
      exact absurd h not_bot_mem_definableType;
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
    · exact exists_rel_forces_of_dia_mem_definableType hV hGrz hB (ih hB')

omit [DecidableEq α] in
/-- A formula refuted in a general frame on a preorder validating `𝐆𝐫𝐳` is refuted in `σ ρ G`.
- [BC22, Lemma 4.1] -/
theorem not_validates_toIntuitionistic_toModal_of_not_validates [Nonempty α]
    (hGrz : G ⊧ logicGrz (α := α)) (h : G ⊭ A) : G.toIntuitionistic.toModal ⊭ A := by
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
    by_contra h;
    exact hx h.2;
  exact h₄ <| (forces_definableValuation_iff hV hGrz Formula.mem_subformulas_self w).mp <|
    hσ _ (isAdmissible_definableValuation hV) w

omit [DecidableEq α] in
/-- The logic of `σ ρ G` is the logic of `G`.
- [BC22, Lemma 4.1] -/
theorem logic_toIntuitionistic_toModal_eq [Nonempty α] (hGrz : G ⊧ logicGrz (α := α)) :
    G.toIntuitionistic.toModal.logic (α := α) = G.logic := by
  apply le_antisymm _ G.logic_le_toIntuitionistic_toModal;
  intro A hA;
  by_contra h;
  exact not_validates_toIntuitionistic_toModal_of_not_validates hGrz h hA

end

end GeneralFrame

end Modal

end
