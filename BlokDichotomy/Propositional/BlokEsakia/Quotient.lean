module

public import BlokDichotomy.Propositional.BlokEsakia.Passive
public import BlokDichotomy.ToMathlib.Order.BooleanSubalgebra

/-!
# The finite quotient of a general frame by the types of subformulas

For a formula `A` and a valuation `V` on a general frame `G`, the type of a point is the set of
subformulas of `A` true at it. Types are preordered by the `◇`-subformulas they contain, and the
preimage of a cluster of types is a Boolean combination of admissible upsets. A point is moved to a
type of its cluster that is realized in the frame so that the preimages of the new types are Boolean
combinations of admissible upsets: a passive point keeps its type, and any other point is sent to a
fixed representative of its cluster.

## References

- [BC22, Lemma 4.1]
-/

@[expose] public section

universe u v

variable {κ : Type u} {α : Type v} [DecidableEq α]

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

variable [IsPreorder κ G.Rel]

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
        (if B ∈ a then {x | x ⊩[G.model V] B} else {x | x ⊩[G.model V] B}ᶜ) ∈ G.admSubalgebra := by
      intro B _;
      split_ifs;
      · exact truthSet_mem hV B;
      · exact G.compl_mem <| truthSet_mem hV B;
    have h₂ := BooleanSubalgebra.setOf_forall_mem G.admSubalgebra A.subformulas h₁;
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

variable [IsPreorder κ G.Rel]

omit [DecidableEq α] in
/-- The set of points not satisfying `◇B` is an admissible upset of `G`. -/
private lemma notForces_dia_mem (hV : G.IsAdmissible V) (B : Formula α) :
    {x | x ⊮[G.model V] ◇B} ∈ G.toIntuitionistic.toModal.Adm := by
  have h₁ : {x | x ⊮[G.model V] ◇B} = G.toFrame.boxSet {x | x ⊩[G.model V] B}ᶜ := by
    ext x;
    simp [Frame.boxSet, Model.World.not_forces_dia];
  rw [h₁];
  exact Propositional.GeneralFrame.subset_toModal_adm
    (boxSet_mem_upAdm (G.compl_mem (truthSet_mem hV B)))

/-- The points whose type is above `a`: `{x | a ⊑ t(x)}` is a finite intersection of the sets
`⟦□∼B⟧`. -/
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

/-- The points whose type is below `a`: `{x | t(x) ⊑ a}` is a finite intersection of the sets
`⟦◇B⟧`. -/
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

/-- The preimage of a cluster of types is a Boolean combination of admissible upsets. -/
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

variable [IsPreorder κ G.Rel]

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

/-- The set of points sent to a given type is a Boolean combination of admissible upsets. -/
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
