module

public import BlokDichotomy.Kripke.Generated
public import BlokDichotomy.Logic.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import BlokDichotomy.Kripke.Makinson
public import BlokDichotomy.Kripke.Splitting

/-!
# Frame companions and the degree of Kripke incompleteness

Frame equivalence of normal logics, frame companions, and the degree of Kripke incompleteness.

## References

- [CZ98, §10.5, Theorem 10.51, Theorem 10.54, Theorem 8.67]
-/

@[expose] public section

universe u v

variable {α : Type v}
variable {L L₁ L₂ L₃ : NormalLogic α} {φ : Formula α}
variable {P : {κ : Type u} → Frame κ → Prop}

namespace NormalLogic

/-- `L₁` and `L₂` are validated by the same frames satisfying `P`.
- [CZ98, §10.5] -/
def FrameEquiv (P : {κ : Type u} → Frame κ → Prop) (L₁ L₂ : NormalLogic α) : Prop :=
  ∀ κ (F : Frame κ), P F → (F ⊧ L₁ ↔ F ⊧ L₂)

@[inherit_doc] notation:50 L₁:51 " ≊[" P "] " L₂:51 => FrameEquiv P L₁ L₂

namespace FrameEquiv

@[refl] lemma refl : L ≊[P] L := fun _ _ _ => Iff.rfl

@[symm] lemma symm (h : L₁ ≊[P] L₂) : L₂ ≊[P] L₁ := fun κ F hF => (h κ F hF).symm

@[trans] lemma trans (h₁ : L₁ ≊[P] L₂) (h₂ : L₂ ≊[P] L₃) : L₁ ≊[P] L₃ :=
  fun κ F hF => (h₁ κ F hF).trans (h₂ κ F hF)

end FrameEquiv

variable (P) in
/-- The logic of the frames satisfying `P` and validating `L`.
- [CZ98, §10.5] -/
def frameLogic (L : NormalLogic α) : NormalLogic α where
  carrier := {φ | ∀ κ : Type u, ∀ F : Frame κ, P F → F ⊧ L → F ⊧ φ}
  mdp hA hAB κ F hP hF := Frame.mdp (hA κ F hP hF) (hAB κ F hP hF)
  nec hA κ F hP hF := Frame.nec (hA κ F hP hF)
  subst hA κ F hP hF := Frame.subst (hA κ F hP hF)

@[simp, grind =]
lemma mem_frameLogic : φ ∈ frameLogic P L ↔ ∀ κ (F : Frame κ), P F → F ⊧ L → F ⊧ φ := Iff.rfl

instance : (frameLogic P L).IsNExt 𝐊 := ⟨fun _ hA _ _ _ _ => Frame.validates_logicK _ hA⟩

lemma le_frameLogic : L ≤ frameLogic P L := fun _ hA _ _ _ hF => hF _ hA

lemma frameEquiv_frameLogic : L ≊[P] frameLogic P L :=
  fun κ F hP => ⟨fun hF _ hA => hA κ F hP hF, fun hF φ hA => hF φ <| le_frameLogic hA⟩

/-- If `L ≊[P] L₁`, then `L₁ ≤ frameLogic P L`.
- [CZ98, §10.5] -/
lemma FrameEquiv.le_frameLogic (h : L ≊[P] L₁) : L₁ ≤ frameLogic P L :=
  fun _ hA κ F hP hF => (h κ F hP).mp hF _ hA

lemma FrameEquiv.frameLogic_eq (h : L ≊[P] L₁) : frameLogic P L = frameLogic P L₁ :=
  SetLike.ext fun _ => forall₂_congr fun κ F => forall_congr' fun hP => imp_congr_left (h κ F hP)

@[simp, grind =]
lemma frameLogic_frameLogic : frameLogic P (frameLogic P L) = frameLogic P L :=
  frameEquiv_frameLogic.symm.frameLogic_eq

@[gcongr]
lemma frameLogic_mono (h : L₁ ≤ L₂) : frameLogic P L₁ ≤ frameLogic P L₂ :=
  fun _ hA κ F hP hF => hA κ F hP fun _ hB => hF _ (h hB)

lemma frameEquiv_iff_frameLogic_eq : L ≊[P] L₁ ↔ frameLogic P L = frameLogic P L₁ :=
  ⟨FrameEquiv.frameLogic_eq, fun h => frameEquiv_frameLogic.trans <|
    h ▸ frameEquiv_frameLogic.symm⟩

variable (P) in
/-- `frameLogic P L ≤ L`.
- [CZ98, §10.5] -/
def KripkeComplete (L : NormalLogic α) : Prop := frameLogic P L ≤ L

lemma kripkeComplete_iff_frameLogic_eq : KripkeComplete P L ↔ frameLogic P L = L :=
  ⟨fun h => le_antisymm h le_frameLogic, fun h => h.le⟩

lemma kripkeComplete_frameLogic : KripkeComplete P (frameLogic P L) :=
  frameLogic_frameLogic.le

lemma not_kripkeComplete_iff_incomplete : ¬KripkeComplete P L ↔ Logic.Incomplete P L := by
  unfold KripkeComplete Logic.Incomplete;
  rw [le_iff];
  push Not;
  exact ⟨fun ⟨φ, hA, hnA⟩ => ⟨φ, hA, hnA⟩, fun ⟨φ, hA, hnA⟩ => ⟨φ, hA, hnA⟩⟩;

/-- The normal extensions `L₁` of `K` with `L ≊[P] L₁`.
- [CZ98, §10.5] -/
def Companion (P : {κ : Type u} → Frame κ → Prop) (L : NormalLogic α) :=
  {L₁ : NormalLogic α // L₁.IsNExt 𝐊 ∧ L ≊[P] L₁}

def Companion.self (L : NormalLogic α) [L.IsNExt 𝐊] : Companion P L :=
  ⟨L, inferInstance, .refl⟩

def Companion.frameLogic (L : NormalLogic α) : Companion P L :=
  ⟨NormalLogic.frameLogic P L, inferInstance, frameEquiv_frameLogic⟩

variable (P) in
/-- The cardinality of `Companion P L`.
- [CZ98, §10.5] -/
noncomputable def degree (L : NormalLogic α) : Cardinal.{v} := Cardinal.mk (Companion P L)

lemma FrameEquiv.degree_eq (h : L₁ ≊[P] L₂) : degree P L₁ = degree P L₂ :=
  Cardinal.mk_congr <| Equiv.subtypeEquivRight fun _ =>
    and_congr_right' ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

lemma degree_ne_zero : degree P L ≠ 0 :=
  Cardinal.mk_ne_zero_iff.mpr ⟨Companion.frameLogic L⟩

lemma one_le_degree : 1 ≤ degree P L := Cardinal.one_le_iff_ne_zero.mpr degree_ne_zero

lemma degree_eq_one_iff :
    degree P L = 1 ↔ ∀ L₁ : NormalLogic α, L₁.IsNExt 𝐊 → L ≊[P] L₁ → L₁ = frameLogic P L := by
  rw [degree, Cardinal.eq_one_iff_unique];
  constructor;
  · rintro ⟨hs, -⟩ L₁ hL₁ h;
    exact congrArg Subtype.val <| hs.elim ⟨L₁, hL₁, h⟩ (Companion.frameLogic L);
  · intro h;
    and_intros;
    · constructor;
      rintro ⟨L₁, hL₁, h₁⟩ ⟨L₂, hL₂, h₂⟩;
      exact Subtype.ext <| (h L₁ hL₁ h₁).trans (h L₂ hL₂ h₂).symm;
    · exact ⟨Companion.frameLogic L⟩;

/-- If `degree P L = 1`, then `L = frameLogic P L`.
- [CZ98, §10.5] -/
lemma eq_frameLogic_of_degree_eq_one [L.IsNExt 𝐊] (h : degree P L = 1) : L = frameLogic P L :=
  degree_eq_one_iff.mp h L inferInstance .refl

lemma kripkeComplete_of_degree_eq_one [L.IsNExt 𝐊] (h : degree P L = 1) : KripkeComplete P L :=
  (eq_frameLogic_of_degree_eq_one h).symm.le

/-- If `L₁ ≠ L₂` are companions of `L`, then `2 ≤ degree P L`.
- [CZ98, §10.5] -/
lemma two_le_degree (hL₁ : L₁.IsNExt 𝐊) (hL₂ : L₂.IsNExt 𝐊)
  (h₁ : L ≊[P] L₁) (h₂ : L ≊[P] L₂) (hne : L₁ ≠ L₂) : 2 ≤ degree P L :=
  Cardinal.two_le_iff.mpr ⟨⟨L₁, hL₁, h₁⟩, ⟨L₂, hL₂, h₂⟩, fun h => hne <| congrArg Subtype.val h⟩

lemma two_le_degree_of_ne [L.IsNExt 𝐊] (hL₁ : L₁.IsNExt 𝐊) (h : L ≊[P] L₁)
    (hne : L₁ ≠ L) : 2 ≤ degree P L :=
  two_le_degree hL₁ inferInstance h .refl hne

/-- If `¬KripkeComplete P L`, then `2 ≤ degree P L`.
- [CZ98, §10.5] -/
lemma two_le_degree_of_not_kripkeComplete [L.IsNExt 𝐊] (h : ¬KripkeComplete P L) :
    2 ≤ degree P L :=
  two_le_degree_of_ne inferInstance frameEquiv_frameLogic fun he => h he.le

lemma degree_eq_one_or_two_le : degree P L = 1 ∨ 2 ≤ degree P L := by
  rcases (one_le_degree (P := P) (L := L)).eq_or_lt with h | h;
  · exact Or.inl h.symm;
  · exact Or.inr <| Cardinal.two_le_iff_one_lt.mpr h;

end NormalLogic


section Inter

open Model.World

variable {κ : Type u} {F : Frame κ} {L₁ L₂ : NormalLogic α}

private lemma forces_rename (e : α ⊕ α ↪ α) (V₁ V₂ : F.World → α → Prop) (i : Bool) {x : F.World}
    {φ : Formula α} :
    x ⊩[(⟨F, fun w c => (∃ a, e (.inl a) = c ∧ V₁ w a) ∨ (∃ b, e (.inr b) = c ∧ V₂ w b)⟩ :
        Model _ α)] φ⟦fun a => #(e (if i then .inl a else .inr a))⟧ ↔
      x ⊩[⟨F, if i then V₁ else V₂⟩] φ := by
  rw [forces_subst];
  have h : (fun w a => w ⊩[(⟨F, fun w c => (∃ a, e (.inl a) = c ∧ V₁ w a) ∨
      (∃ b, e (.inr b) = c ∧ V₂ w b)⟩ : Model _ α)] #(e (if i then .inl a else .inr a))) =
      if i then V₁ else V₂ := by
    funext w a;
    cases i <;> simp [Forces, Model.Val];
  rw [h];

/-- Given `e : α ⊕ α ↪ α`, a rooted frame validating `L₁ ∩ L₂` validates `L₁` or `L₂`.
- [CZ98, §10.5] -/
theorem Frame.validates_inter_of_isRooted [L₁.IsNExt 𝐊] [L₂.IsNExt 𝐊] (e : α ⊕ α ↪ α)
    (hF : F.IsRooted) (h : F ⊧ (L₁ ∩ L₂)) : F ⊧ L₁ ∨ F ⊧ L₂ := by
  by_contra! hc;
  obtain ⟨h₁, h₂⟩ := hc;
  obtain ⟨φ, hA, hφ⟩ := Frame.not_validateLogic_iff.mp h₁;
  obtain ⟨ψ, hB, hψ⟩ := Frame.not_validateLogic_iff.mp h₂;
  obtain ⟨V₁, x₁, hx₁⟩ := Frame.not_validates_iff'.mp hφ;
  obtain ⟨V₂, x₂, hx₂⟩ := Frame.not_validates_iff'.mp hψ;
  obtain ⟨r, hr⟩ := hF;
  obtain ⟨k₁, Rrx₁⟩ := hr x₁;
  obtain ⟨k₂, Rrx₂⟩ := hr x₂;
  let s₁ : Formula.Substitution α α := fun a => #(e (.inl a));
  let s₂ : Formula.Substitution α α := fun a => #(e (.inr a));
  have hC : □^[k₁]φ⟦s₁⟧ ⋎ □^[k₂]ψ⟦s₂⟧ ∈ L₁ ∩ L₂ := by
    constructor;
    · exact NormalLogic.mem_mdp
        (NormalLogic.multibox_mem <| NormalLogic.mem_subst hA) NormalLogic.or_left;
    · exact NormalLogic.mem_mdp
        (NormalLogic.multibox_mem <| NormalLogic.mem_subst hB) NormalLogic.or_right;
  rcases forces_or.mp <| h _ hC
    (fun w c => (∃ a, e (.inl a) = c ∧ V₁ w a) ∨ (∃ b, e (.inr b) = c ∧ V₂ w b)) r with h₁ | h₁;
  · exact hx₁ <| (forces_rename e V₁ V₂ true).mp <| forces_multidox.mp h₁ x₁ Rrx₁;
  · exact hx₂ <| (forces_rename e V₁ V₂ false).mp <| forces_multidox.mp h₁ x₂ Rrx₂;

lemma nonempty_sum_embedding_of_infinite [Infinite α] : Nonempty (α ⊕ α ↪ α) := by
  rw [← Cardinal.le_def, Cardinal.mk_sum, Cardinal.lift_id,
    Cardinal.add_eq_self <| Cardinal.infinite_iff.mp inferInstance];

theorem Frame.validates_inter_of_isRooted_of_infinite [Infinite α] [L₁.IsNExt 𝐊] [L₂.IsNExt 𝐊]
    (hF : F.IsRooted) (h : F ⊧ (L₁ ∩ L₂)) : F ⊧ L₁ ∨ F ⊧ L₂ :=
  validates_inter_of_isRooted (Classical.choice nonempty_sum_embedding_of_infinite) hF h

end Inter


namespace NormalLogic

open Frame

section UnionSplitting

variable {𝔉 : Set FinFrame} {L : NormalLogic ℕ}

/-- The union-splitting `K / 𝔉` is Kripke complete.
- [CZ98, Theorem 10.54]
-/
theorem unionSplitting_kripkeComplete (h𝔉 : ∀ F ∈ 𝔉, FinFrame.RootedCycleFree F)
  : KripkeComplete (fun _ => True) (unionSplitting 𝔉) := by
  intro φ hA;
  by_contra hnA;
  obtain ⟨m, G, hG, hGA⟩ := unionSplitting_fmp h𝔉 hnA;
  exact hGA <| validates_transport_iff.mp <|
    hA _ G.ulift trivial (validateLogic_transport_iff.mpr hG);

/-- Every union-splitting of `K` is Kripke complete.
- [CZ98, Theorem 10.54]
-/
theorem IsUnionSplitting.kripkeComplete (h : L.IsUnionSplitting)
  : KripkeComplete (fun _ => True) L := by
  obtain ⟨𝔉, h𝔉, rfl⟩ := h;
  exact unionSplitting_kripkeComplete h𝔉;

/-- A union-splitting of `K` has degree `1`.
- [CZ98, Theorem 10.51]
-/
theorem degree_eq_one_of_isUnionSplitting (h : L.IsUnionSplitting)
  : degree (fun _ => True) L = 1 := by
  obtain ⟨𝔉, h𝔉, rfl⟩ := h;
  have hc := unionSplitting_kripkeComplete h𝔉;
  apply degree_eq_one_iff.mpr;
  intro L₁ hL₁ hE;
  rw [kripkeComplete_iff_frameLogic_eq.mp hc];
  apply le_antisymm;
  · calc L₁ ≤ frameLogic _ L₁ := le_frameLogic
      _ = frameLogic _ (unionSplitting 𝔉) := hE.frameLogic_eq.symm
      _ ≤ unionSplitting 𝔉 := hc;
  · apply (unionSplitting_le_iff (L := L₁) h𝔉).mpr;
    intro F hF hFL₁;
    apply not_validates_unionSplitting h𝔉 hF;
    exact validateLogic_transport_iff.mp <|
      (hE _ F.2.ulift trivial).mpr <| validateLogic_transport_iff.mpr hFL₁;

end UnionSplitting


section Inconsistent

variable {α : Type v} {L : NormalLogic α}

/-- An inconsistent logic has degree `1`.
- [CZ98, Theorem 8.67]
-/
theorem degree_eq_one_of_not_consistent (h : ¬L.Consistent) : degree (fun _ => True) L = 1 := by
  have hL : ∀ φ, φ ∈ L := fun φ => by
    by_contra hA;
    exact h <| consistent_iff.mpr ⟨φ, hA⟩;
  apply degree_eq_one_iff.mpr;
  intro L₁ hL₁ hE;
  have hall : ∀ φ, φ ∈ L₁ := fun φ => by
    by_contra hA;
    obtain ⟨F, hF⟩ := Consistent.exists_frame_validates <| consistent_iff.mpr ⟨φ, hA⟩;
    exact h <| consistent_of_validates <| (hE _ F.ulift trivial).mpr <|
      validateLogic_transport_iff.mpr hF;
  exact SetLike.ext fun φ => iff_of_true (hall φ) (le_frameLogic <| hL φ);

end Inconsistent

end NormalLogic

end
