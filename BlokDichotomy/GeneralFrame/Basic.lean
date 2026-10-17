module

public import BlokDichotomy.Kripke.Generated

/-!
# General frames

General frames, admissible valuations, validity, and the logic of a general frame.

## References

- [CZ98, §8.1]
-/

@[expose] public section

universe u v

variable {κ : Type u} {α : Type v}

def Frame.diaSet (F : Frame κ) (X : Set F.World) : Set F.World := {w | ∃ v, w ≺ v ∧ v ∈ X}

/--
A Kripke frame with a set `Adm` of admissible sets closed under intersection, complement and
`Frame.diaSet`.
- [CZ98, §8.1]
-/
structure GeneralFrame (κ : Type u) extends Frame κ where
  Adm : Set (Set toFrame.World)
  univ_mem : Set.univ ∈ Adm
  inter_mem {X Y : Set toFrame.World} : X ∈ Adm → Y ∈ Adm → X ∩ Y ∈ Adm
  compl_mem {X : Set toFrame.World} : X ∈ Adm → Xᶜ ∈ Adm
  diaSet_mem {X : Set toFrame.World} : X ∈ Adm → toFrame.diaSet X ∈ Adm

/--
The general frame of a Kripke frame, in which every set is admissible.
- [CZ98, §8.1]
-/
def Frame.toGeneralFrame (F : Frame κ) : GeneralFrame κ where
  toFrame := F
  Adm := Set.univ
  univ_mem := trivial
  inter_mem _ _ := trivial
  compl_mem _ := trivial
  diaSet_mem _ := trivial

namespace GeneralFrame

variable {G : GeneralFrame κ} {X Y : Set G.World}

lemma empty_mem : ∅ ∈ G.Adm := by simpa using G.compl_mem G.univ_mem

lemma union_mem (hX : X ∈ G.Adm) (hY : Y ∈ G.Adm) : X ∪ Y ∈ G.Adm := by
  simpa [Set.compl_inter] using G.compl_mem <| G.inter_mem (G.compl_mem hX) (G.compl_mem hY)

lemma himp_mem (hX : X ∈ G.Adm) (hY : Y ∈ G.Adm) : Xᶜ ∪ Y ∈ G.Adm :=
  union_mem (G.compl_mem hX) hY

/--
`V` is admissible when `{w | V w a} ∈ G.Adm` for every `a`.
- [CZ98, §8.1]
-/
def IsAdmissible (G : GeneralFrame κ) (V : G.World → α → Prop) : Prop := ∀ a, {w | V w a} ∈ G.Adm

abbrev model (G : GeneralFrame κ) (V : G.World → α → Prop) : Model κ α := ⟨G.toFrame, V⟩

open Model.World

variable {V : G.World → α → Prop} {φ ψ : Formula α}

/--
- [CZ98, §8.1]
-/
lemma truthSet_mem (hV : G.IsAdmissible V) (φ : Formula α) :
    {w | w ⊩[G.model V] φ} ∈ G.Adm := by
  induction φ with
  | falsum => simpa using G.empty_mem;
  | atom a => exact hV a;
  | imp φ ψ ihφ ihψ =>
    convert himp_mem ihφ ihψ using 1;
    ext w;
    simp [forces_imp, NotForces];
  | dia φ ih =>
    convert G.diaSet_mem ih using 1;
    ext w;
    simp [Frame.diaSet, forces_dia];

lemma isAdmissible_subst (hV : G.IsAdmissible V) (s : Formula.Substitution α α) :
    G.IsAdmissible (fun w a => w ⊩[G.model V] s a) :=
  fun a => truthSet_mem hV (s a)

lemma isAdmissible_toGeneralFrame {F : Frame κ} (V : F.World → α → Prop) :
    F.toGeneralFrame.IsAdmissible V := fun _ => trivial

/--
`G ⊧ φ`: `φ` is true at every point under every admissible valuation.
- [CZ98, §8.1]
-/
def Validates (G : GeneralFrame κ) (φ : Formula α) : Prop :=
  ∀ V : G.World → α → Prop, G.IsAdmissible V → G.model V ⊧ φ
infix:50 " ⊧ " => GeneralFrame.Validates

abbrev NotValidates (G : GeneralFrame κ) (φ : Formula α) : Prop := ¬(G ⊧ φ)
infix:50 " ⊭ " => GeneralFrame.NotValidates

def ValidatesLogic (G : GeneralFrame κ) (L : NormalLogic α) : Prop := ∀ φ ∈ L, G ⊧ φ
infix:50 " ⊧ " => GeneralFrame.ValidatesLogic

abbrev NotValidateLogic (G : GeneralFrame κ) (L : NormalLogic α) : Prop := ¬(G ⊧ L)
infix:50 " ⊭ " => GeneralFrame.NotValidateLogic

lemma mdp (hA : G ⊧ φ) (hAB : G ⊧ φ 🡒 ψ) : G ⊧ ψ :=
  fun V hV x => hAB V hV x <| hA V hV x

lemma nec (h : G ⊧ φ) : G ⊧ □φ :=
  fun V hV _ => forces_box.mpr fun y _ => h V hV y

lemma subst {s : Formula.Substitution α α} (h : G ⊧ φ) : G ⊧ φ⟦s⟧ :=
  fun _ hV x => (forces_subst s).mpr <| h _ (isAdmissible_subst hV s) x

/--
The normal logic `{φ | G ⊧ φ}`.
- [CZ98, §8.1]
-/
def logic (G : GeneralFrame κ) : NormalLogic α where
  carrier := {φ | G ⊧ φ}
  mdp := mdp
  nec := nec
  subst := subst

@[simp, grind =] lemma mem_logic : φ ∈ G.logic ↔ G ⊧ φ := Iff.rfl

lemma validatesLogic_logic : G ⊧ (G.logic : NormalLogic α) := fun _ hA => hA

lemma validates_logicK : G ⊧ (𝐊 : NormalLogic α) := by
  intro φ hA V _;
  exact Frame.validates_logicK φ hA V;

instance : (G.logic : NormalLogic α).IsNExt 𝐊 := ⟨fun _ hA => validates_logicK _ hA⟩

lemma ValidatesLogic.le_logic {L : NormalLogic α} (h : G ⊧ L) : L ≤ G.logic := h

end GeneralFrame


namespace Frame

variable {F : Frame κ} {φ : Formula α} {L : NormalLogic α}

@[simp]
lemma toGeneralFrame_validates_iff : F.toGeneralFrame ⊧ φ ↔ F ⊧ φ :=
  ⟨fun h V => h V (GeneralFrame.isAdmissible_toGeneralFrame V), fun h V _ => h V⟩

@[simp]
lemma toGeneralFrame_validatesLogic_iff : F.toGeneralFrame ⊧ L ↔ F ⊧ L :=
  forall₂_congr fun _ _ => toGeneralFrame_validates_iff

/--
- [CZ98, §8.1]
-/
lemma logic_toGeneralFrame : (F.toGeneralFrame.logic : NormalLogic α) = F.logic :=
  SetLike.ext fun _ => toGeneralFrame_validates_iff

end Frame


namespace GeneralFrame

open Model.World

variable {G : GeneralFrame κ} {u : G.World} {V : G.World → α → Prop} {φ : Formula α}
  {L : NormalLogic α}

lemma forces_iff_pointGenerate :
    u ⊩[G.model V] φ ↔
      Frame.pointGenerate.root G.toFrame u ⊩[⟨G.toFrame⥜u, fun y a => V y.1 a⟩] φ :=
  forces_pointGenerate_root.symm

lemma forces_of_pointGenerate_validates (h : G.toFrame⥜u ⊧ φ) (V : G.World → α → Prop)
    {y : G.World} (hy : y ∈ G.toFrame.Reach u) : y ⊩[G.model V] φ :=
  forces_pointGenerate (M := G.model V) (y := ⟨y, hy⟩) |>.mp <| h _ _

lemma forces_of_pointGenerate_validatesLogic (h : G.toFrame⥜u ⊧ L) {φ : Formula α}
    (hA : φ ∈ L) (V : G.World → α → Prop) : u ⊩[G.model V] φ :=
  forces_of_pointGenerate_validates (h φ hA) V Frame.self_mem_reach

/-- Every `X ⊆ G.toFrame.Reach u` is `Y ∩ G.toFrame.Reach u` for some `Y ∈ G.Adm`. -/
def AdmissibleOnReach (G : GeneralFrame κ) (u : G.World) : Prop :=
  ∀ X ⊆ G.toFrame.Reach u, ∃ Y ∈ G.Adm, Y ∩ G.toFrame.Reach u = X

/-- If `G.AdmissibleOnReach u`, then `G.toFrame⥜u ⊧ φ` iff `φ` is true at every point of
`G.toFrame.Reach u` under every admissible valuation. -/
lemma pointGenerate_validates_iff (hG : G.AdmissibleOnReach u) :
    G.toFrame⥜u ⊧ φ ↔
      ∀ V, G.IsAdmissible V → ∀ y ∈ G.toFrame.Reach u, y ⊩[G.model V] φ := by
  constructor;
  · intro h V _ y hy;
    exact forces_of_pointGenerate_validates h V hy;
  · intro h W y;
    have hY : ∀ a, ∃ Y ∈ G.Adm, Y ∩ G.toFrame.Reach u = {w | ∃ hw, W ⟨w, hw⟩ a} := fun a =>
      hG _ fun w ⟨hw, _⟩ => hw;
    choose Y hYadm hYeq using hY;
    have hV : G.IsAdmissible (fun w a => w ∈ Y a) := hYadm;
    have hagree : (G.model fun w a => w ∈ Y a)⥜u = ⟨G.toFrame⥜u, W⟩ := by
      simp only [Model.pointGenerate, Model.mk.injEq, true_and];
      funext z a;
      apply propext;
      have := congrArg (z.1 ∈ ·) (hYeq a);
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Subtype.coe_eta, eq_iff_iff] at this;
      constructor;
      · intro hz;
        obtain ⟨_, h'⟩ := this.mp ⟨hz, z.2⟩;
        exact h';
      · intro hz;
        exact (this.mpr ⟨z.2, hz⟩).1;
    have := forces_pointGenerate (M := G.model fun w a => w ∈ Y a) (x := u) (φ := φ) (y := y);
    rw [hagree] at this;
    exact this.mpr <| h _ hV y.1 y.2;

lemma pointGenerate_validatesLogic_iff (hG : G.AdmissibleOnReach u) :
    G.toFrame⥜u ⊧ L ↔
      ∀ φ ∈ L, ∀ V, G.IsAdmissible V → ∀ y ∈ G.toFrame.Reach u, y ⊩[G.model V] φ :=
  forall₂_congr fun _ _ => pointGenerate_validates_iff hG

end GeneralFrame

end
