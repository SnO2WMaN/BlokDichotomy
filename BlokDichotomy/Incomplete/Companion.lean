module

public import BlokDichotomy.Incomplete.Löb
public import BlokDichotomy.Kripke.Degree
public import BlokDichotomy.GeneralFrame.Basic
public import BlokDichotomy.Kripke.Makinson
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# A continuum of frame companions

Frame companions `L.interLog H` of `L` from general frames `H` satisfying `HookInterface`, and the
resulting lower bound `𝔠 ≤ degree P L`.

## References

- [CZ98, p. 367, p. 368]
-/

@[expose] public section

universe u w

open Formula Model.World

namespace NormalLogic

variable {α : Type*} {κ : Type*}

/-- `L ∩ H.logic`.
- [CZ98, p. 367]
-/
def interLog (L : NormalLogic α) (H : GeneralFrame κ) : NormalLogic α := L ∩ H.logic

variable {L : NormalLogic α} {H : GeneralFrame κ} {φ : Formula α}

instance [L.IsNExt 𝐊] : (L.interLog H).IsNExt 𝐊 := by
  unfold interLog;
  infer_instance

lemma mem_interLog_iff : φ ∈ L.interLog H ↔ φ ∈ L ∧ H ⊧ φ := Iff.rfl

lemma interLog_le : L.interLog H ≤ L := fun _ h => h.1

end NormalLogic


namespace Naming

open NormalLogic

variable {κ : Type w} (L : NormalLogic ℕ) (N m l e : ℕ) (φ : Formula ℕ) (I : Set ℕ)

/-- The properties of a hooked general frame `H` with index set `I`.
- [CZ98, p. 367, p. 368]
-/
structure HookInterface (H : GeneralFrame κ) where
  /-- The points whose generated subframes validate `L`. -/
  safe : Set H.World
  forces_of_mem_safe {x : H.World} (hx : x ∈ safe) {ψ : Formula ℕ} (hA : ψ ∈ L)
    (V : H.World → ℕ → Prop) :
    x ⊩[H.model V] ψ
  /-- When the irreflexive point does not validate `L`, every point has a successor. -/
  serial (h : deadEnd ⊭ L) (x : H.World) : ∃ y, x ≺ y
  /-- The point named by `γ`. -/
  gammaPoint : H.World
  gammaPoint_forces (V : H.World → ℕ → Prop) (hV : H.IsAdmissible V) (h₁ : ∃ w, V w 0)
    (h₂ : ∃ w, ¬V w 0) : gammaPoint ⊩[H.model V] gamma N m
  reach_gammaPoint {x : H.World} (hx : x ∉ safe) : ∃ n ≤ l, H.toFrame.RelItr n x gammaPoint
  /-- When the reflexive point does not validate `L`, a dead end is reachable. -/
  reach_deadEnd (h : reflPoint ⊭ L) {x : H.World} (hx : x ∉ safe) :
    ∃ n ≤ l, ∃ y, H.toFrame.RelItr n x y ∧ ∀ z, ¬y ≺ z
  validates_gammaLöb : H ⊧ gammaLöb N m
  alpha_unique {i : ℕ} (hi : i ∉ I) (V : H.World → ℕ → Prop) (hV : H.IsAdmissible V)
    {x y : H.World}
    (hx : x ⊩[H.model V] alpha N m i) (hy : y ⊩[H.model V] alpha N m i) : x = y
  not_validates_xi {i : ℕ} (hi : i ∈ I) : H ⊭ xi N m e φ i

variable {L N m l e φ I} {H : GeneralFrame κ} [L.IsNExt 𝐊]
variable {P : {κ : Type u} → Frame κ → Prop}

namespace HookInterface

variable (hH : HookInterface L N m l e φ I H)
include hH

section Formulas

variable {ψ : Formula ℕ}

/-- If `deadEnd ⊭ L`, then `◇⊤ ∈ L.interLog H`.
- [CZ98, (10.12)]
-/
lemma diaTop_mem (h : deadEnd ⊭ L) : ◇⊤ ∈ L.interLog H := by
  constructor;
  · by_contra h';
    exact h <| deadEnd_validates_of_not_mem h';
  · intro V _ x;
    obtain ⟨y, hy⟩ := hH.serial h x;
    exact forces_dia.mpr ⟨y, hy, forces_top⟩;

/-- `∼ψ ⋏ ∼tau N 🡒 ◇^≤[l] gamma N m ∈ L.interLog H` for `ψ ∈ L`.
- [CZ98, (10.12)]
-/
lemma tau_mem (hψ : ψ ∈ L) : ∼ψ ⋏ ∼tau N 🡒 ◇^≤[l] gamma N m ∈ L.interLog H := by
  constructor;
  · apply mem_mdp hψ;
    apply mem_of_isTautology;
    intro v;
    grind;
  · intro V hV x;
    rw [forces_imp, NotForces, forces_and, forces_neg, forces_neg];
    by_cases hx : x ∈ hH.safe;
    · exact Or.inl fun h => h.1 <| hH.forces_of_mem_safe hx hψ V;
    · by_cases hq : (∀ w, V w 0) ∨ (∀ w, ¬V w 0);
      · exact Or.inl fun h => h.2 <| forces_tau_of_const hq;
      · push Not at hq;
        obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := hq;
        obtain ⟨n, hn, hxc⟩ := hH.reach_gammaPoint hx;
        exact Or.inr <| forces_diaLe.mpr
          ⟨n, hn, _, hxc, hH.gammaPoint_forces V hV ⟨w₂, hw₂⟩ ⟨w₁, hw₁⟩⟩;

/-- `∼ψ 🡒 □^≤[l] gammaLöb N m ∈ L.interLog H` for `ψ ∈ L`.
- [CZ98, (10.13)]
-/
lemma gammaLöb_mem (hψ : ψ ∈ L) : ∼ψ 🡒 □^≤[l] gammaLöb N m ∈ L.interLog H := by
  constructor;
  · apply mem_mdp hψ;
    apply mem_of_isTautology;
    intro v;
    grind;
  · intro V hV x;
    rw [forces_imp];
    exact Or.inr <| forces_boxLe.mpr fun _ _ y _ => hH.validates_gammaLöb V hV y;

/-- If `reflPoint ⊭ L`, then `ψ ⋎ ◇^≤[l] □⊥ ∈ L.interLog H` for `ψ ∈ L`.
- [CZ98, (10.12)]
-/
lemma deadEnd_mem (h : reflPoint ⊭ L) (hψ : ψ ∈ L) :
    ψ ⋎ ◇^≤[l] □⊥ ∈ L.interLog H := by
  constructor;
  · apply mem_mdp hψ;
    apply mem_of_isTautology;
    intro v;
    grind;
  · intro V _ x;
    rw [forces_or];
    by_cases hx : x ∈ hH.safe;
    · exact Or.inl <| hH.forces_of_mem_safe hx hψ V;
    · obtain ⟨n, hn, y, Rxy, hy⟩ := hH.reach_deadEnd h hx;
      exact Or.inr <| forces_diaLe.mpr ⟨n, hn, y, Rxy, forces_box.mpr fun z hz => hy z hz⟩;

end Formulas

end HookInterface


section FrameEquiv

variable {ι : Type*} {F : Frame ι} {V : F.World → ℕ → Prop} {u : F.World} {ψ : Formula ℕ}

lemma eq_of_relItr_of_forall_rel (hsucc : ∀ v, u ≺ v → v = u) {n : ℕ} {v : F.World}
    (h : F.RelItr n u v) : v = u := by
  induction n generalizing v with
  | zero => exact (Frame.iff_relItr_zero.mp h).symm;
  | succ n ih =>
    obtain ⟨z, hz, hzv⟩ := Frame.iff_relItr_succ'.mp h;
    rw [ih hz] at hzv;
    exact hsucc v hzv;

abbrev shift (ψ : Formula ℕ) : Formula ℕ := ψ⟦fun a => #(a + 2)⟧

lemma shift_mem {L : NormalLogic ℕ} (h : ψ ∈ L) : shift ψ ∈ L := L.subst h

lemma forces_shift {W : F.World → ℕ → Prop} (hW : ∀ w a, W w (a + 2) ↔ V w a) :
    u ⊩[(⟨F, W⟩ : Model _ ℕ)] shift ψ ↔ u ⊩[(⟨F, V⟩ : Model _ ℕ)] ψ := by
  rw [forces_subst];
  have h : (fun w a => W w (a + 2)) = V := funext fun w => funext fun a => propext (hW w a);
  change u ⊩[(⟨F, fun w a => W w (a + 2)⟩ : Model _ ℕ)] ψ ↔ _;
  rw [h]

namespace HookInterface

variable (hH : HookInterface L N m l e φ I H)
include hH

private lemma false_of_refutes_of_rel_ne (hN : 1 ≤ N) (hF : F ⊧ L.interLog H) (hA : ψ ∈ L)
    (hu : u ⊮[(⟨F, V⟩ : Model _ ℕ)] ψ) {v : F.World} (Ruv : u ≺ v) (hvu : v ≠ u) : False := by
  let V₁ : F.World → ℕ → Prop := fun w a => if a = 0 then w = u else V w (a - 2);
  have hV₁ : ∀ w a, V₁ w (a + 2) ↔ V w a := fun w a => by simp [V₁];
  have hψ : u ⊮[(⟨F, V₁⟩ : Model _ ℕ)] shift ψ := by rwa [NotForces, forces_shift hV₁];
  have hτ : u ⊮[(⟨F, V₁⟩ : Model _ ℕ)] tau N :=
    not_forces_tau (M := ⟨F, V₁⟩) hN (by simp [V₁, Model.Val]) Ruv (by simp [V₁, Model.Val, hvu]);
  have h₁ := hF _ (hH.tau_mem (l := l) (shift_mem hA)) V₁ u;
  rw [forces_imp, NotForces, forces_and, forces_neg, forces_neg] at h₁;
  obtain ⟨n, hn, x, hux, hx⟩ := forces_diaLe.mp <| h₁.resolve_left fun h => h ⟨hψ, hτ⟩;
  obtain ⟨y, Rxy, -⟩ := forces_dia.mp (forces_gamma.mp hx).1;
  let V₂ : F.World → ℕ → Prop := fun w a => if a = 1 then w ≠ y else V₁ w a;
  have hV₂ : ∀ w a, V₂ w (a + 2) ↔ V w a := fun w a => by simp [V₂, V₁];
  have h₂ := hF _ (hH.gammaLöb_mem (l := l) (shift_mem hA)) V₂ u;
  rw [forces_imp, NotForces, forces_neg, NotForces, forces_shift hV₂] at h₂;
  have h₃ := forces_boxLe.mp (h₂.resolve_left fun h => h hu) n hn x hux;
  have hx₂ : x ⊩[(⟨F, V₂⟩ : Model _ ℕ)] gamma N m :=
    (forces_congr_of_atoms_subset atoms_gamma fun w => by simp [V₂, Model.Val]).mp hx;
  exact not_forces_löb V₁ y <| forces_gammaLöb.mp h₃ hx₂ y Rxy;

/-- `L.interLog H` is a frame companion of `L`.
- [CZ98, p. 368]
-/
theorem frameEquiv (hN : 1 ≤ N) : L ≊[P] L.interLog H := by
  intro ι F _;
  constructor;
  · exact fun hF ψ hA => hF ψ hA.1;
  · intro hF;
    by_contra hFL;
    obtain ⟨ψ, hA, hψ⟩ := Frame.not_validateLogic_iff.mp hFL;
    obtain ⟨V, u, hu⟩ := Frame.not_validates_iff'.mp hψ;
    by_cases hv : ∃ v, u ≺ v ∧ v ≠ u;
    · obtain ⟨v, Ruv, hvu⟩ := hv;
      exact hH.false_of_refutes_of_rel_ne hN hF hA hu Ruv hvu;
    · push Not at hv;
      by_cases Ruu : u ≺ u;
      · have hr : reflPoint ⊭ L := fun h =>
          hu <| (forces_iff_reflPoint Ruu hv).mpr <| h ψ hA _ 0;
        have h := hF _ (hH.deadEnd_mem (l := l) hr hA) V u;
        rcases forces_or.mp h with h | h;
        · exact hu h;
        · obtain ⟨n, -, y, huy, hy⟩ := forces_diaLe.mp h;
          rw [eq_of_relItr_of_forall_rel hv huy] at hy;
          exact forces_box.mp hy u Ruu;
      · have hx : ∀ v, ¬u ≺ v := fun v Ruv => Ruu <| hv v Ruv ▸ Ruv;
        have hd : deadEnd ⊭ L := fun h => hu <|
          (forces_iff_of_no_succ (M := ⟨F, V⟩) (N := ⟨deadEnd, fun _ a => V u a⟩) (x := u)
            (y := 0) hx
            (fun _ h => h) fun _ => Iff.rfl).mpr <| h ψ hA _ 0;
        obtain ⟨y, hy, -⟩ := forces_dia.mp <| hF _ (hH.diaTop_mem hd) V u;
        exact hx y hy;

omit [L.IsNExt 𝐊] in
/-- `H ⊧ xi N m e φ i` for `i ∉ I`.
- [CZ98, p. 367]
-/
lemma validates_xi {i : ℕ} (hi : i ∉ I) : H ⊧ xi N m e φ i := by
  intro V hV x;
  rw [xi, forces_neg, NotForces, forces_and, forces_and, forces_dia, forces_dia];
  rintro ⟨⟨y, -, hy⟩, ⟨y', -, hy'⟩, -⟩;
  rw [forces_and] at hy hy';
  rw [forces_neg] at hy';
  rw [hH.alpha_unique hi V hV hy.1 hy'.1] at hy;
  exact hy'.2 hy.2;

end HookInterface

lemma xi_mem (hφ : φ ∈ L) (i : ℕ) : xi N m e φ i ∈ L := by
  have h : □^[e]φ ∈ L := multibox_mem hφ;
  apply mem_mdp h;
  unfold xi;
  apply mem_of_isTautology;
  intro v;
  simp;
  grind;

/-- If `I ≠ J`, then `L.interLog H ≠ L.interLog H'`.
- [CZ98, p. 367]
-/
theorem HookInterface.interLog_ne {J : Set ℕ} {κ' : Type*} {H' : GeneralFrame κ'} (hφ : φ ∈ L)
    (hI : HookInterface L N m l e φ I H) (hJ : HookInterface L N m l e φ J H') (hIJ : I ≠ J) :
    L.interLog H ≠ L.interLog H' := by
  obtain ⟨i, hi⟩ : ∃ i, ¬(i ∈ I ↔ i ∈ J) := by
    by_contra h;
    push Not at h;
    exact hIJ <| Set.ext h;
  intro he;
  by_cases hiI : i ∈ I;
  · have hiJ : i ∉ J := fun h => hi ⟨fun _ => h, fun _ => hiI⟩;
    have h : xi N m e φ i ∈ L.interLog H' := ⟨xi_mem hφ i, hJ.validates_xi hiJ⟩;
    rw [← he] at h;
    exact hI.not_validates_xi hiI h.2;
  · have hiJ : i ∈ J := by tauto;
    have h : xi N m e φ i ∈ L.interLog H := ⟨xi_mem hφ i, hI.validates_xi hiI⟩;
    rw [he] at h;
    exact hJ.not_validates_xi hiJ h.2;

/-- `Cardinal.continuum ≤ degree P L`.
- [CZ98, p. 367, p. 368]
-/
theorem HookInterface.continuum_le_degree {κ : Set ℕ → Type w} {H : ∀ I, GeneralFrame (κ I)}
    (hH : ∀ I, HookInterface L N m l e φ I (H I)) (hφ : φ ∈ L) (hN : 1 ≤ N) :
    Cardinal.continuum ≤ degree P L := by
  let f : Set ℕ → Companion P L := fun I =>
    ⟨L.interLog (H I), inferInstance, (hH I).frameEquiv hN⟩;
  have hf : Function.Injective f := fun I J h => by
    by_contra hIJ;
    exact interLog_ne hφ (hH I) (hH J) hIJ <| congrArg Subtype.val h;
  rw [← Cardinal.mk_set_nat];
  exact Cardinal.mk_le_of_injective hf;

end FrameEquiv

end Naming

end
