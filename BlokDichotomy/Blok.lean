module

public import BlokDichotomy.Formula
public import BlokDichotomy.GeneralFrame.Basic
public import BlokDichotomy.Kripke.Basic
public import BlokDichotomy.Kripke.Cycle
public import BlokDichotomy.Kripke.Degree
public import BlokDichotomy.Kripke.Makinson
public import BlokDichotomy.Kripke.Splitting
public import BlokDichotomy.Kripke.Transport
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Blok's dichotomy theorem

The degree of Kripke incompleteness of a normal logic extending `𝐊` is `1` or the continuum.

## References

- [CZ98, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/

@[expose] public section

universe u w

/-! ## Löb-type formulas -/

namespace Naming

open Formula Model.World

variable (N m : ℕ)

/-- `tau N = □^≤[N] #0 ⋎ □^≤[N] ∼#0`.
- [CZ98, Example 10.58]
-/
def tau : Formula ℕ := □^≤[N] (#0) ⋎ □^≤[N] (∼#0)

def deltaPair : ℕ → Formula ℕ × Formula ℕ
  | 0 => (◇tau N ⋏ ∼tau N, ◇tau N ⋏ ∼tau N)
  | j + 1 =>
    (◇(deltaPair j).1 ⋏ ∼(deltaPair j).2, (deltaPair j).2 ⋎ (◇(deltaPair j).1 ⋏ ∼(deltaPair j).2))

/-- `delta N 0 = ◇tau N ⋏ ∼tau N` and `delta N (j + 1) = ◇delta N j ⋏ ∼deltaUpTo N j`.
- [CZ98, Example 10.57]
-/
def delta (j : ℕ) : Formula ℕ := (deltaPair N j).1

/-- `delta N 0 ⋎ ⋯ ⋎ delta N j`. -/
def deltaUpTo (j : ℕ) : Formula ℕ := (deltaPair N j).2

/-- `pi N 0 = delta N 0` and `pi N (j + 1) = delta N (j + 1) ⋏ ◇pi N j`.
- [CZ98, Example 10.57]
-/
def pi : ℕ → Formula ℕ
  | 0 => delta N 0
  | j + 1 => delta N (j + 1) ⋏ ◇pi j

/-- `alpha N m 0 = ◇pi N m ⋏ ∼◇◇pi N m` and
`alpha N m (i + 1) = ◇alpha N m i ⋏ ∼◇◇alpha N m i`.
- [CZ98, Example 10.57]
-/
def alpha : ℕ → Formula ℕ
  | 0 => ◇pi N m ⋏ ∼◇◇pi N m
  | i + 1 => ◇alpha i ⋏ ∼◇◇alpha i

/-- `gamma N m = ◇◇alpha N m 0 ⋏ ∼◇alpha N m 0`.
- [CZ98, Example 10.57]
-/
def gamma : Formula ℕ := ◇◇alpha N m 0 ⋏ ∼◇alpha N m 0

/-- `theta N m = ◇alpha N m 0`.
- [CZ98, Example 10.57]
-/
def theta : Formula ℕ := ◇alpha N m 0

/-- `box₀ N m φ = □(theta N m 🡒 φ)`.
- [CZ98, p. 365]
-/
def box₀ (φ : Formula ℕ) : Formula ℕ := □(theta N m 🡒 φ)

/-- `löb N m = box₀ N m (box₀ N m #1 🡒 #1) 🡒 #1`.
- [CZ98, p. 365]
-/
def löb : Formula ℕ := box₀ N m (box₀ N m (#1) 🡒 #1) 🡒 #1

/-- `gammaLöb N m = gamma N m 🡒 □löb N m`.
- [CZ98, p. 365]
-/
def gammaLöb : Formula ℕ := gamma N m 🡒 □löb N m

/-- `xi N m e φ i = ∼(◇(alpha N m i ⋏ #0) ⋏ ◇(alpha N m i ⋏ ∼#0) ⋏ ∼□^[e]φ)`.
- [CZ98, p. 367]
-/
def xi (e : ℕ) (φ : Formula ℕ) (i : ℕ) : Formula ℕ :=
  ∼(◇(alpha N m i ⋏ #0) ⋏ ◇(alpha N m i ⋏ ∼#0) ⋏ ∼□^[e]φ)

variable {N m} {j i : ℕ}

@[simp] lemma delta_zero : delta N 0 = ◇tau N ⋏ ∼tau N := rfl
private lemma delta_succ : delta N (j + 1) = ◇delta N j ⋏ ∼deltaUpTo N j := rfl
@[simp] lemma deltaUpTo_zero : deltaUpTo N 0 = delta N 0 := rfl
private lemma deltaUpTo_succ : deltaUpTo N (j + 1) = deltaUpTo N j ⋎ delta N (j + 1) := rfl


section Atoms

private lemma atoms_tau : ∀ a ∈ (tau N).atoms, a = 0 := by
  intro a ha;
  simpa [tau] using ha;

private lemma atoms_deltaPair (j : ℕ) :
    (∀ a ∈ (deltaPair N j).1.atoms, a = 0) ∧ ∀ a ∈ (deltaPair N j).2.atoms, a = 0 := by
  induction j with
  | zero => simpa [deltaPair] using atoms_tau;
  | succ j ih =>
    constructor <;>
    · intro a ha;
      simp only [deltaPair, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
      grind;

private lemma atoms_pi : ∀ a ∈ (pi N j).atoms, a = 0 := by
  induction j with
  | zero => exact (atoms_deltaPair 0).1;
  | succ j ih =>
    intro a ha;
    simp only [pi, delta, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
    have := (atoms_deltaPair (N := N) (j + 1)).1 a;
    grind;

private lemma atoms_alpha : ∀ a ∈ (alpha N m i).atoms, a = 0 := by
  induction i with
  | zero =>
    intro a ha;
    simp only [alpha, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
    have := atoms_pi (N := N) (j := m) a;
    grind;
  | succ i ih =>
    intro a ha;
    simp only [alpha, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
    grind;

private lemma atoms_gamma : ∀ a ∈ (gamma N m).atoms, a = 0 := by
  intro a ha;
  simp only [gamma, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
  have := atoms_alpha (N := N) (m := m) (i := 0) a;
  grind;

end Atoms


section Semantics

variable {κ : Type*} {M : Model κ ℕ} {x : M.World}

private lemma forces_congr_of_atoms_subset {φ : Formula ℕ} (hA : ∀ a ∈ φ.atoms, a = 0)
    {V : M.World → ℕ → Prop}
    (hV : ∀ w, M.Val w 0 ↔ V w 0) : x ⊩[M] φ ↔ x ⊩[⟨M.toFrame, V⟩] φ :=
  forces_congr_of_atoms fun a ha w => by rw [hA a ha]; exact hV w

private lemma forces_tau :
    x ⊩ tau N ↔ (∀ i ≤ N, ∀ y, (x ≺^[i] y) → M.Val y 0) ∨
      (∀ i ≤ N, ∀ y, (x ≺^[i] y) → ¬M.Val y 0) := by
  simp only [tau, forces_or, forces_boxLe, forces_neg];
  rfl

/-- If `M.Val · 0` is constant, then `x ⊩ tau N`.
- [CZ98, Example 10.58]
-/
private lemma forces_tau_of_const (h : (∀ w, M.Val w 0) ∨ (∀ w, ¬M.Val w 0)) : x ⊩ tau N := by
  rw [forces_tau];
  rcases h with h | h;
  · exact Or.inl fun _ _ y _ => h y;
  · exact Or.inr fun _ _ y _ => h y;

private lemma not_forces_tau (hN : 1 ≤ N) {y : M.World} (hx : M.Val x 0) (Rxy : x ≺ y)
    (hy : ¬M.Val y 0) : x ⊮ tau N := by
  rw [NotForces, forces_tau];
  rintro (h | h);
  · exact hy <| h 1 hN y <| Frame.iff_relItr_one.mpr Rxy;
  · exact h 0 (Nat.zero_le _) x rfl hx;

/-- If every `y` satisfies `x ≺^[n] y` for some `n ≤ N` and `M.Val · 0` is not constant, then
`x ⊮ tau N`.
- [CZ98, Example 10.58]
-/
private lemma not_forces_tau_of_reach (hreach : ∀ y, ∃ n ≤ N, x ≺^[n] y) (h₁ : ∃ w, M.Val w 0)
    (h₂ : ∃ w, ¬M.Val w 0) : x ⊮ tau N := by
  obtain ⟨w₁, hw₁⟩ := h₁;
  obtain ⟨w₂, hw₂⟩ := h₂;
  rw [NotForces, forces_tau];
  rintro (h | h);
  · obtain ⟨n, hn, hx⟩ := hreach w₂;
    exact hw₂ <| h n hn w₂ hx;
  · obtain ⟨n, hn, hx⟩ := hreach w₁;
    exact h n hn w₁ hx hw₁;

private lemma forces_deltaUpTo : x ⊩ deltaUpTo N j ↔ ∃ i ≤ j, x ⊩ delta N i := by
  induction j with
  | zero => simp;
  | succ j ih =>
    rw [deltaUpTo_succ, forces_or, ih];
    grind

private lemma forces_delta_succ :
    x ⊩ delta N (j + 1) ↔ x ⊩ ◇delta N j ∧ ∀ i ≤ j, x ⊮ delta N i := by
  rw [delta_succ, forces_and, forces_neg, NotForces, forces_deltaUpTo];
  push Not;
  rfl

private lemma not_forces_delta_of_lt (hij : i < j) (h : x ⊩ delta N i) : x ⊮ delta N j := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hij;
  rw [show i + j + 1 = (i + j) + 1 by omega, NotForces, forces_delta_succ];
  exact fun h' => h'.2 i (by omega) h

private lemma forces_pi_succ : x ⊩ pi N (j + 1) ↔
    x ⊩ delta N (j + 1) ∧ ∃ y, x ≺ y ∧ y ⊩ pi N j := by
  simp only [pi, forces_and, forces_dia]

private lemma forces_delta_of_forces_pi (h : x ⊩ pi N j) : x ⊩ delta N j := by
  cases j with
  | zero => exact h;
  | succ j => exact (forces_pi_succ.mp h).1

private lemma forces_alpha_zero :
    x ⊩ alpha N m 0 ↔ x ⊩ ◇pi N m ∧ x ⊮ ◇◇pi N m := by
  rw [alpha, forces_and, forces_neg]

private lemma forces_alpha_succ :
    x ⊩ alpha N m (i + 1) ↔ x ⊩ ◇alpha N m i ∧ x ⊮ ◇◇alpha N m i := by
  rw [alpha, forces_and, forces_neg]

private lemma forces_gamma : x ⊩ gamma N m ↔ x ⊩ ◇◇alpha N m 0 ∧ x ⊮ ◇alpha N m 0 := by
  rw [gamma, forces_and, forces_neg]

private lemma forces_box₀ {φ : Formula ℕ} :
    x ⊩ box₀ N m φ ↔ ∀ y, x ≺ y → y ⊩ theta N m → y ⊩ φ := by
  rw [box₀, forces_box];
  exact forall₂_congr fun _ _ => forces_imp.trans imp_iff_not_or.symm

private lemma forces_löb :
    x ⊩ löb N m ↔ (x ⊩ box₀ N m (box₀ N m (#1) 🡒 #1) → M.Val x 1) := by
  rw [löb, forces_imp];
  exact imp_iff_not_or.symm

private lemma forces_gammaLöb :
    x ⊩ gammaLöb N m ↔ (x ⊩ gamma N m → ∀ y, x ≺ y → y ⊩ löb N m) := by
  rw [gammaLöb, forces_imp, forces_box];
  exact imp_iff_not_or.symm

section Const

variable (h : (∀ w, M.Val w 0) ∨ (∀ w, ¬M.Val w 0))
include h

private lemma not_forces_delta_of_const : x ⊮ delta N j := by
  induction j generalizing x with
  | zero =>
    rw [delta_zero, NotForces, forces_and, forces_neg];
    exact fun h' => h'.2 <| forces_tau_of_const h;
  | succ j ih =>
    rw [NotForces, forces_delta_succ, forces_dia];
    rintro ⟨⟨y, -, hy⟩, -⟩;
    exact ih hy;

private lemma not_forces_pi_of_const : x ⊮ pi N j :=
  fun h' => not_forces_delta_of_const h <| forces_delta_of_forces_pi h'

private lemma not_forces_alpha_of_const : x ⊮ alpha N m i := by
  induction i generalizing x with
  | zero =>
    rw [NotForces, forces_alpha_zero, forces_dia];
    rintro ⟨⟨y, -, hy⟩, -⟩;
    exact not_forces_pi_of_const h hy;
  | succ i ih =>
    rw [NotForces, forces_alpha_succ, forces_dia];
    rintro ⟨⟨y, -, hy⟩, -⟩;
    exact ih hy;

/-- If `M.Val · 0` is constant, then `x ⊮ gamma N m`.
- [CZ98, Example 10.58]
-/
private lemma not_forces_gamma_of_const : x ⊮ gamma N m := by
  rw [NotForces, forces_gamma, forces_dia];
  rintro ⟨⟨y, -, hy⟩, -⟩;
  obtain ⟨z, -, hz⟩ := forces_dia.mp hy;
  exact not_forces_alpha_of_const h hz;

end Const

/-- `y ⊮ löb N m` under the valuation sending `#1` to `{w | w ≠ y}`.
- [CZ98, Example 10.57]
-/
theorem not_forces_löb {F : Frame κ} (V : F.World → ℕ → Prop) (y : F.World) :
    y ⊮[(⟨F, fun w a => if a = 1 then w ≠ y else V w a⟩ : Model _ ℕ)] löb N m := by
  rw [NotForces, forces_löb];
  intro h;
  apply h _ rfl;
  rw [forces_box₀];
  intro z Ryz hz;
  rw [forces_imp, NotForces];
  by_cases hzy : z = y;
  · left;
    rw [hzy] at Ryz hz ⊢;
    rw [forces_box₀];
    intro h';
    exact h' y Ryz hz rfl;
  · right;
    exact hzy

end Semantics

end Naming

/-! ## Frame companions -/

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

private lemma mem_interLog_iff : φ ∈ L.interLog H ↔ φ ∈ L ∧ H ⊧ φ := Iff.rfl

private lemma interLog_le : L.interLog H ≤ L := fun _ h => h.1

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
private lemma diaTop_mem (h : deadEnd ⊭ L) : ◇⊤ ∈ L.interLog H := by
  constructor;
  · by_contra h';
    exact h <| deadEnd_validates_of_not_mem h';
  · intro V _ x;
    obtain ⟨y, hy⟩ := hH.serial h x;
    exact forces_dia.mpr ⟨y, hy, forces_top⟩;

/-- `∼ψ ⋏ ∼tau N 🡒 ◇^≤[l] gamma N m ∈ L.interLog H` for `ψ ∈ L`.
- [CZ98, (10.12)]
-/
private lemma tau_mem (hψ : ψ ∈ L) : ∼ψ ⋏ ∼tau N 🡒 ◇^≤[l] gamma N m ∈ L.interLog H := by
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
private lemma gammaLöb_mem (hψ : ψ ∈ L) : ∼ψ 🡒 □^≤[l] gammaLöb N m ∈ L.interLog H := by
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
private lemma deadEnd_mem (h : reflPoint ⊭ L) (hψ : ψ ∈ L) :
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

private lemma eq_of_relItr_of_forall_rel (hsucc : ∀ v, u ≺ v → v = u) {n : ℕ} {v : F.World}
    (h : F.RelItr n u v) : v = u := by
  induction n generalizing v with
  | zero => exact (Frame.iff_relItr_zero.mp h).symm;
  | succ n ih =>
    obtain ⟨z, hz, hzv⟩ := Frame.iff_relItr_succ'.mp h;
    rw [ih hz] at hzv;
    exact hsucc v hzv;

abbrev shift (ψ : Formula ℕ) : Formula ℕ := ψ⟦fun a => #(a + 2)⟧

private lemma shift_mem {L : NormalLogic ℕ} (h : ψ ∈ L) : shift ψ ∈ L := L.subst h

private lemma forces_shift {W : F.World → ℕ → Prop} (hW : ∀ w a, W w (a + 2) ↔ V w a) :
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
private lemma validates_xi {i : ℕ} (hi : i ∉ I) : H ⊧ xi N m e φ i := by
  intro V hV x;
  rw [xi, forces_neg, NotForces, forces_and, forces_and, forces_dia, forces_dia];
  rintro ⟨⟨y, -, hy⟩, ⟨y', -, hy'⟩, -⟩;
  rw [forces_and] at hy hy';
  rw [forces_neg] at hy';
  rw [hH.alpha_unique hi V hV hy.1 hy'.1] at hy;
  exact hy'.2 hy.2;

end HookInterface

private lemma xi_mem (hφ : φ ∈ L) (i : ℕ) : xi N m e φ i ∈ L := by
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

/-! ## Hooked frames -/

namespace Frame

section
variable {κ : Type u} {F : Frame κ} {x y : F.World}

private lemma exists_relItr_lt_card [Finite F.World] (h : y ∈ F.Reach x) :
    ∃ n < Nat.card F.World, x ≺^[n] y := by
  obtain ⟨n, hn⟩ := h;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hlt : n < Nat.card F.World;
    · exact ⟨n, hlt, hn⟩;
    obtain ⟨p, hp₀, hpn, hp⟩ := exists_path hn;
    have hni : ¬Function.Injective (fun i : Fin (Nat.card F.World + 1) => p i) := by
      intro hi;
      have := Nat.card_le_card_of_injective _ hi;
      simp at this;
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hni;
    have hne' : (i : ℕ) ≠ j := Fin.val_ne_of_ne hne;
    wlog hij' : (i : ℕ) < j generalizing i j;
    · exact this j i hij.symm hne.symm hne'.symm <| by omega;
    have h₁ := relItr_of_path hp (Nat.zero_le i) (by omega);
    have h₂ := relItr_of_path hp (i := j) (j := n) (by omega) le_rfl;
    rw [hp₀] at h₁;
    rw [hpn, ← hij] at h₂;
    exact ih _ (by omega) (relItr_trans h₁ h₂);


end

section
variable {κ : Type*} {F : Frame κ} {x y : F.World} {α : Type*} {L : NormalLogic α}

private lemma HasCycle.exists_path (h : F.HasCycle) : ∃ p : ℕ → F.World, ∀ t, p t ≺ p (t + 1) := by
  obtain ⟨x, k, hk, hx⟩ := h;
  obtain ⟨p, hp₀, hpk, hp⟩ := Frame.exists_path hx;
  use fun t => p (t % k);
  intro t;
  have hdm := Nat.div_add_mod t k;
  have hlt := Nat.mod_lt t hk;
  rcases Nat.lt_or_ge (t % k + 1) k with h | h;
  · have he : (t + 1) % k = t % k + 1 := by
      rw [show t + 1 = (t % k + 1) + k * (t / k) by omega, Nat.add_mul_mod_self_left];
      exact Nat.mod_eq_of_lt h;
    simpa only [he] using hp _ hlt;
  · have he : (t + 1) % k = 0 := by
      rw [show t + 1 = k * (t / k + 1) by rw [Nat.mul_succ]; omega, Nat.mul_mod_right];
    have h' := hp (k - 1) (by omega);
    rw [show k - 1 + 1 = k by omega, hpk, ← hp₀] at h';
    simpa only [he, show t % k = k - 1 by omega] using h';

private lemma eq_of_mem_reach_of_forall_not_rel (hx : ∀ z, x ⊀ z) (h : y ∈ F.Reach x) : y = x := by
  obtain ⟨n, hn⟩ := h;
  cases n with
  | zero => exact hn.symm;
  | succ n =>
    obtain ⟨z, hz, -⟩ := hn;
    exact absurd hz (hx z);

private lemma deadEnd_validates_of_forall_not_rel (hx : ∀ z, x ⊀ z) (h : F⥜x ⊧ L)
  : deadEnd ⊧ L := by
  let f : F⥜x →ₚ deadEnd :=
    { toFun := fun _ => 0
      forth := fun {y z} Ryz => by
        have Ryz' : y.1 ≺ z.1 := Ryz;
        rw [eq_of_mem_reach_of_forall_not_rel hx y.2] at Ryz';
        exact hx z.1 Ryz'
      back := fun h => h.elim };
  exact ValidateLogic.of_surjective_pMorphism f (fun i => ⟨(pointGenerate.root F x).1,
    Subsingleton.elim _ _⟩) h

private lemma not_isRootedBy_of_forall_not_rel (hc : F.HasCycle) (hx : ∀ z, x ⊀ z) :
    ¬F.IsRootedBy x := by
  intro hr;
  obtain ⟨y, k, hk, hy⟩ := hc;
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne';
  obtain ⟨z, hz, -⟩ := hy;
  exact hx z <| eq_of_mem_reach_of_forall_not_rel hx (hr y) ▸ hz;


end

end Frame



/-- The data of a hooked frame: a rooted frame `F`, an infinite path in `F`, the number `len + 1`
of copies, the length `m` of the `d`-chain, and whether `dBot` is reflexive.
- [CZ98, Fig. 10.4, Fig. 10.5]
- [Blok78, Definition 4.3]
-/
structure HookData (κ : Type u) where
  F : Frame κ
  root : F.Root
  path : ℕ → F.World
  path_rel : ∀ t, path t ≺ path (t + 1)
  /-- The copies are `copy 0, …, copy len`. -/
  len : ℕ
  /-- The `d`-chain is `d m ≺ ⋯ ≺ d 0`. -/
  m : ℕ
  card_add_len_lt : Nat.card F.World + len + 2 ≤ m
  /-- Whether `dBot` sees itself. -/
  refl : Prop


namespace HookData

section

variable {κ : Type u} (D : HookData κ) (I : Set ℕ)

inductive World : Type u
  | base (u : D.F.World)
  | copy (t : ℕ) (ht : t ≤ D.len)
  | c
  | b
  | a (i : ℕ) (twin : Bool) (h : twin = true → i ∈ I)
  | d (j : ℕ) (hj : j ≤ D.m)
  | dBot

/-- The accessibility relation of the hooked frame.
- [CZ98, Fig. 10.4, Fig. 10.5]
-/
def Rel : D.World I → D.World I → Prop
  | .base u, .base v => u ≺ v
  | .base u, .copy t _ => u = D.path 0 ∧ t = 0
  | .copy t _, .base v => D.path (t + 1) ≺ v
  | .copy t _, .copy t' _ => t' = t + 1
  | .copy t _, .d j _ => t = D.len ∧ j = 0
  | .d j _, .base v => j = 0 ∧ v = D.root
  | .d j _, .c => j = 0
  | .d j _, .d j' _ => j = j' + 1
  | .d j _, .dBot => j = 0
  | .dBot, .dBot => D.refl
  | .c, .b => True
  | .b, .a _ _ _ => True
  | .a i _ _, .a j _ _ => j < i
  | .a i _ _, .d j _ => i = 0 ∧ j = D.m
  | _, _ => False

def hookFrame : Frame (D.World I) := ⟨D.Rel I⟩

variable {D I}

namespace World

def IsA : D.World I → Prop
  | .a _ _ _ => True
  | _ => False

def index : D.World I → ℕ
  | .a i _ _ => i
  | _ => 0

def twin : D.World I → Bool
  | .a _ t _ => t
  | _ => false

def IsUnwound : D.World I → Prop
  | .base _ => True
  | .copy _ _ => True
  | _ => False

@[simp] lemma isA_a {i : ℕ} {t : Bool} {h : t = true → i ∈ I} : (World.a i t h : D.World I).IsA :=
  trivial

@[simp] lemma index_a {i : ℕ} {t : Bool} {h : t = true → i ∈ I} :
    (World.a i t h : D.World I).index = i := rfl

private lemma isA_iff {w : D.World I} : w.IsA ↔ ∃ i t h, w = .a i t h := by
  cases w <;> simp_all [IsA];

private lemma isUnwound_iff {w : D.World I} :
    w.IsUnwound ↔ (∃ u, w = .base u) ∨ ∃ t ht, w = .copy t ht := by
  cases w <;> simp_all [IsUnwound];

end World

@[simp] lemma hookFrame_rel {x y : (D.hookFrame I).World} : x ≺ y ↔ D.Rel I x y := Iff.rfl

open World

private lemma finite_isA_index_le (n : ℕ) : {w : D.World I | w.IsA ∧ w.index ≤ n}.Finite := by
  apply Set.Finite.of_finite_image (f := fun w => (w.index, w.twin));
  · apply ((Set.finite_le_nat n).prod Set.finite_univ).subset;
    rintro _ ⟨w, ⟨-, hw⟩, rfl⟩;
    exact ⟨hw, trivial⟩;
  · rintro (_ | _ | _ | _ | ⟨i, t, h⟩ | _ | _) ⟨⟨⟩, -⟩ (_ | _ | _ | _ | ⟨i', t', h'⟩ | _ | _)
      ⟨⟨⟩, -⟩ he;
    simp only [index, twin, Prod.mk.injEq] at he;
    obtain ⟨rfl, rfl⟩ := he;
    rfl;

/-- The admissible sets of the hooked frame: the sets `S` such that only finitely many `a`-points
disagree with `b` about membership in `S`.
- [CZ98, Fig. 10.5]
- [Blok78, Definition 4.3]
-/
def Adm (D : HookData κ) (I : Set ℕ) : Set (Set (D.World I)) :=
  {S | {w | w.IsA ∧ (w ∈ S ↔ World.b ∉ S)}.Finite}

private lemma mem_adm_iff {S : Set (D.World I)} :
    S ∈ D.Adm I ↔ (World.b ∈ S → {w | w.IsA ∧ w ∉ S}.Finite) ∧
      (World.b ∉ S → {w | w.IsA ∧ w ∈ S}.Finite) := by
  by_cases hb : World.b ∈ S <;> simp [Adm, hb];

private lemma mem_adm_of_not_mem_of_finite {S : Set (D.World I)} (hb : World.b ∉ S)
    (hS : {w | w.IsA ∧ w ∈ S}.Finite) : S ∈ D.Adm I :=
  mem_adm_iff.mpr ⟨fun h => absurd h hb, fun _ => hS⟩

private lemma mem_adm_of_forall {S : Set (D.World I)} (hS : ∀ w ∈ S, w ≠ .b ∧ ¬w.IsA) :
    S ∈ D.Adm I :=
  mem_adm_of_not_mem_of_finite (fun h => (hS _ h).1 rfl) <|
    Set.finite_empty.subset fun w ⟨hw, hwS⟩ => (hS w hwS).2 hw

lemma adm_compl {S : Set (D.World I)} (hS : S ∈ D.Adm I) : Sᶜ ∈ D.Adm I := by
  apply hS.subset;
  rintro w ⟨hw, h⟩;
  simp only [Set.mem_compl_iff] at h;
  exact ⟨hw, by tauto⟩;

lemma adm_inter {S T : Set (D.World I)} (hS : S ∈ D.Adm I) (hT : T ∈ D.Adm I) :
    S ∩ T ∈ D.Adm I := by
  apply (hS.union hT).subset;
  rintro w ⟨hw, h⟩;
  simp only [Set.mem_inter_iff, not_and] at h;
  simp only [Set.mem_union, Set.mem_ofPred_eq];
  tauto;

private lemma mem_diaSet_b {S : Set (D.World I)} :
    World.b ∈ (D.hookFrame I).diaSet S ↔ ∃ w ∈ S, w.IsA := by
  constructor;
  · rintro ⟨w, hw, hwS⟩;
    exact ⟨w, hwS, by cases w <;> simp_all [Rel, IsA]⟩;
  · rintro ⟨w, hwS, hw⟩;
    obtain ⟨i, t, h, rfl⟩ := isA_iff.mp hw;
    exact ⟨.a i t h, trivial, hwS⟩;

private lemma mem_diaSet_of_isA {S : Set (D.World I)} {w : D.World I} (hw : w.IsA) :
    w ∈ (D.hookFrame I).diaSet S ↔
      (∃ w' ∈ S, w'.IsA ∧ w'.index < w.index) ∨ (w.index = 0 ∧ World.d D.m le_rfl ∈ S) := by
  obtain ⟨i, t, h, rfl⟩ := isA_iff.mp hw;
  constructor;
  · rintro ⟨w', hw', hw'S⟩;
    cases w' with
    | a j t' h' => exact Or.inl ⟨_, hw'S, trivial, hw'⟩;
    | d j hj =>
      obtain ⟨rfl, rfl⟩ := hw';
      exact Or.inr ⟨rfl, hw'S⟩;
    | _ => simp_all [Rel];
  · rintro (⟨w', hw'S, hw', hlt⟩ | ⟨h₀, hd⟩);
    · obtain ⟨j, t', h', rfl⟩ := isA_iff.mp hw';
      exact ⟨.a j t' h', hlt, hw'S⟩;
    · exact ⟨.d D.m le_rfl, ⟨h₀, rfl⟩, hd⟩;

lemma adm_diaSet {S : Set (D.World I)} : (D.hookFrame I).diaSet S ∈ D.Adm I := by
  by_cases h : ∃ w ∈ S, w.IsA;
  · obtain ⟨z, hzS, hz⟩ := h;
    apply (finite_isA_index_le z.index).subset;
    rintro w ⟨hw, hwS⟩;
    use hw;
    by_contra! hlt;
    exact (hwS.mp <| (mem_diaSet_of_isA hw).mpr <| Or.inl ⟨z, hzS, hz, hlt⟩) <|
      mem_diaSet_b.mpr ⟨z, hzS, hz⟩;
  · apply (finite_isA_index_le 0).subset;
    rintro w ⟨hw, hwS⟩;
    use hw;
    rcases (mem_diaSet_of_isA hw).mp (hwS.mpr fun hb => h <| mem_diaSet_b.mp hb) with
      ⟨w', hw'S, hw', -⟩ | ⟨h₀, -⟩;
    · exact absurd ⟨w', hw'S, hw'⟩ h;
    · omega;

variable (D I) in
/-- The hooked general frame.
- [CZ98, Fig. 10.4, Fig. 10.5]
- [Blok78, Definition 4.3]
-/
def hooked : GeneralFrame (D.World I) where
  toFrame := D.hookFrame I
  Adm := D.Adm I
  univ_mem := Set.finite_empty.subset fun _ ⟨_, h⟩ => h.mp trivial trivial
  inter_mem := adm_inter
  compl_mem := adm_compl
  diaSet_mem _ := adm_diaSet

@[simp] lemma hooked_toFrame : (D.hooked I).toFrame = D.hookFrame I := rfl

@[simp] lemma hooked_adm : (D.hooked I).Adm = D.Adm I := rfl


section Rel

/-! ### Successors and predecessors -/

variable {x y : (D.hookFrame I).World}

private lemma rel_base_iff {u : D.F.World} :
    (.base u : (D.hookFrame I).World) ≺ y ↔
      (∃ v, y = .base v ∧ u ≺ v) ∨ (u = D.path 0 ∧ y = .copy 0 (Nat.zero_le _)) := by
  cases y <;> simp [Rel];

private lemma rel_copy_iff {t : ℕ} {ht : t ≤ D.len} :
    (.copy t ht : (D.hookFrame I).World) ≺ y ↔
      (∃ v, y = .base v ∧ D.path (t + 1) ≺ v) ∨ (∃ h, y = .copy (t + 1) h) ∨
        (t = D.len ∧ y = .d 0 (Nat.zero_le _)) := by
  cases y <;> simp [Rel, eq_comm];
  omega;

private lemma rel_c_iff : (.c : (D.hookFrame I).World) ≺ y ↔ y = .b := by
  cases y <;> simp [Rel];

private lemma rel_b_iff : (.b : (D.hookFrame I).World) ≺ y ↔ y.IsA := by
  cases y <;> simp [Rel, IsA];

private lemma rel_a_iff {i : ℕ} {t : Bool} {h : t = true → i ∈ I} :
    (.a i t h : (D.hookFrame I).World) ≺ y ↔
      (y.IsA ∧ y.index < i) ∨ (i = 0 ∧ y = .d D.m le_rfl) := by
  cases y <;> simp [Rel, IsA, index];

private lemma rel_a_zero_iff {t : Bool} {h : t = true → 0 ∈ I} :
    (.a 0 t h : (D.hookFrame I).World) ≺ y ↔ y = .d D.m le_rfl := by
  rw [rel_a_iff];
  simp;

private lemma rel_d_succ_iff {j : ℕ} {hj : j + 1 ≤ D.m} :
    (.d (j + 1) hj : (D.hookFrame I).World) ≺ y ↔ y = .d j (by omega) := by
  cases y <;> simp [Rel, eq_comm];

private lemma rel_d_zero_iff {hj : 0 ≤ D.m} :
    (.d 0 hj : (D.hookFrame I).World) ≺ y ↔ y = .dBot ∨ y = .c ∨ y = .base D.root := by
  cases y <;> simp [Rel, eq_comm];

private lemma rel_dBot_iff : (.dBot : (D.hookFrame I).World) ≺ y ↔ y = .dBot ∧ D.refl := by
  cases y <;> simp [Rel];

private lemma rel_to_base_iff {v : D.F.World} :
    x ≺ (.base v : (D.hookFrame I).World) ↔
      (∃ u, x = .base u ∧ u ≺ v) ∨
        (∃ t ht, x = .copy t ht ∧ D.path (t + 1) ≺ v) ∨
        (x = .d 0 (Nat.zero_le _) ∧ v = D.root) := by
  cases x <;> simp_all [Rel];

private lemma rel_to_copy_iff {t : ℕ} {ht : t ≤ D.len} :
    x ≺ (.copy t ht : (D.hookFrame I).World) ↔
      (t = 0 ∧ x = .base (D.path 0)) ∨ ∃ s hs, t = s + 1 ∧ x = .copy s hs := by
  cases x <;> simp [Rel, and_comm];
  omega;

private lemma rel_to_c_iff : x ≺ (.c : (D.hookFrame I).World) ↔ x = .d 0 (Nat.zero_le _) := by
  cases x <;> simp [Rel];

private lemma rel_to_b_iff : x ≺ (.b : (D.hookFrame I).World) ↔ x = .c := by
  cases x <;> simp [Rel];

private lemma rel_to_a_iff {i : ℕ} {t : Bool} {h : t = true → i ∈ I} :
    x ≺ (.a i t h : (D.hookFrame I).World) ↔ x = .b ∨ (x.IsA ∧ i < x.index) := by
  cases x <;> simp [Rel, IsA, index];

private lemma rel_to_d_iff {j : ℕ} {hj : j ≤ D.m} :
    x ≺ (.d j hj : (D.hookFrame I).World) ↔
      (∃ h, x = .d (j + 1) h) ∨ (j = 0 ∧ x = .copy D.len le_rfl) ∨
        (j = D.m ∧ x.IsA ∧ x.index = 0) := by
  cases x <;> simp [Rel, IsA, index, and_comm];
  omega;

private lemma rel_to_dBot_iff :
    x ≺ (.dBot : (D.hookFrame I).World) ↔ x = .d 0 (Nat.zero_le _) ∨ (x = .dBot ∧ D.refl) := by
  cases x <;> simp [Rel];

private lemma isUnwound_of_rel (hy : y.IsUnwound) (Rxy : x ≺ y) :
    x.IsUnwound ∨ x = .d 0 (Nat.zero_le _) := by
  cases x <;> cases y <;> simp_all [Rel, IsUnwound];

private lemma isUnwound_of_isUnwound_rel (hx : x.IsUnwound) (Rxy : x ≺ y) :
    y.IsUnwound ∨ y = .d 0 (Nat.zero_le _) := by
  cases x <;> cases y <;> simp_all [Rel, IsUnwound];

private lemma isA_of_rel (hy : y.IsA) (Rxy : x ≺ y) : x = .b ∨ x.IsA := by
  cases x <;> cases y <;> simp_all [Rel, IsA];

end Rel


section Reach

/-! ### Reachability -/

open Frame

variable {x y : (D.hookFrame I).World} {n : ℕ}

lemma relItr_base {u v : D.F.World} (Ruv : u ≺^[n] v) :
    RelItr (F := D.hookFrame I) n (.base u) (.base v) :=
  relItr_map (G := D.hookFrame I) World.base (fun h => h) Ruv

private lemma relItr_copy {t t' : ℕ} {ht : t ≤ D.len} {ht' : t' ≤ D.len} (h : t ≤ t') :
    RelItr (F := D.hookFrame I) (t' - t) (.copy t ht) (.copy t' ht') := by
  induction t' with
  | zero =>
    obtain rfl : t = 0 := by omega;
    simp;
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h;
    · simp;
    · rw [show t' + 1 - t = t' - t + 1 by omega];
      exact relItr_tail (ih (ht' := by omega) (by omega)) (by simp [Rel]);

private lemma relItr_d {j j' : ℕ} {hj : j ≤ D.m} {hj' : j' ≤ D.m} (h : j ≤ j') :
    RelItr (F := D.hookFrame I) (j' - j) (.d j' hj') (.d j hj) := by
  induction j' with
  | zero =>
    obtain rfl : j = 0 := by omega;
    simp;
  | succ j' ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h;
    · simp;
    · rw [show j' + 1 - j = (j' - j) + 1 by omega, iff_relItr_succ];
      exact ⟨.d j' (by omega), by simp [Rel], ih (hj' := by omega) (by omega)⟩;

/-- `.b ≺^[D.m + 3] .base D.root`.
- [CZ98, p. 367]
-/
private lemma b_relItr_root : RelItr (F := D.hookFrame I) (D.m + 3) .b (.base D.root) := by
  have h₁ : RelItr (F := D.hookFrame I) (D.m - 0) (.d D.m le_rfl) (.d 0 (Nat.zero_le _)) :=
    relItr_d (Nat.zero_le _);
  have h₂ := relItr_tail h₁ (z := .base D.root) (by simp [Rel]);
  have h₃ := relItr_head (x := .a 0 false (by simp)) (by simp [Rel]) h₂;
  have h₄ := relItr_head (x := .b) (by simp [Rel]) h₃;
  rwa [show D.m - 0 + 1 + 1 + 1 = D.m + 3 by omega] at h₄;

private lemma eq_dBot_of_dBot_relItr (RdBoty : (.dBot : (D.hookFrame I).World) ≺^[n] y) :
    y = .dBot := by
  induction n generalizing y with
  | zero => exact RdBoty.symm;
  | succ n ih =>
    obtain ⟨z, h₁, h₂⟩ := iff_relItr_succ'.mp RdBoty;
    obtain rfl := ih h₁;
    exact (rel_dBot_iff.mp h₂).1;

variable (D I) in
/-- The points `.dBot` and `.base u` with `D.path 0 ∉ D.F.Reach u`.
- [CZ98, p. 367]
-/
def detached : Set (D.hookFrame I).World :=
  {x | x = .dBot ∨ ∃ u, x = .base u ∧ D.path 0 ∉ D.F.Reach u}

@[simp] lemma dBot_mem_detached : (.dBot : (D.hookFrame I).World) ∈ D.detached I := Or.inl rfl

@[simp] lemma base_mem_detached_iff {u : D.F.World} :
    (.base u : (D.hookFrame I).World) ∈ D.detached I ↔ D.path 0 ∉ D.F.Reach u := by
  simp [detached];

private lemma eq_dBot_or_isUnwound_of_mem_detached (hx : x ∈ D.detached I) :
    x = .dBot ∨ x.IsUnwound := by
  rcases hx with rfl | ⟨u, rfl, -⟩;
  · exact Or.inl rfl;
  · exact Or.inr trivial;

private lemma mem_detached_of_rel (hx : x ∈ D.detached I) (Rxy : x ≺ y) : y ∈ D.detached I := by
  rcases hx with rfl | ⟨u, rfl, hu⟩;
  · rw [(rel_dBot_iff.mp Rxy).1];
    exact dBot_mem_detached;
  · rcases rel_base_iff.mp Rxy with ⟨v, rfl, Ruv⟩ | ⟨rfl, -⟩;
    · exact base_mem_detached_iff.mpr fun hv => hu <| reach_trans (mem_reach_of_rel Ruv) hv;
    · exact absurd self_mem_reach hu;

private lemma relItr_base_iff_of_not_mem_reach {u : D.F.World} (hu : D.path 0 ∉ D.F.Reach u) :
    ((.base u : (D.hookFrame I).World) ≺^[n] y) ↔
      ∃ v : D.F.World, (u ≺^[n] v) ∧ y = .base v := by
  induction n generalizing y with
  | zero => simp [eq_comm];
  | succ n ih =>
    constructor;
    · intro h;
      obtain ⟨z, h₁, h₂⟩ := iff_relItr_succ'.mp h;
      obtain ⟨w, hw, rfl⟩ := ih.mp h₁;
      rcases rel_base_iff.mp h₂ with ⟨v, rfl, hwv⟩ | ⟨rfl, -⟩;
      · exact ⟨v, relItr_tail hw hwv, rfl⟩;
      · exact absurd (mem_reach_of_relItr hw) hu;
    · rintro ⟨v, h, rfl⟩;
      exact relItr_base h;

def pointGenerateBase {u : D.F.World} (hu : D.path 0 ∉ D.F.Reach u) :
    D.F⥜u →ₚ (D.hookFrame I)⥜(.base u) where
  toFun v := ⟨.base v.1, v.2.elim fun _ h => mem_reach_of_relItr <| relItr_base h⟩
  forth h := h
  back {v z} h := by
    obtain ⟨z, n, hn⟩ := z;
    obtain ⟨w, -, rfl⟩ := (relItr_base_iff_of_not_mem_reach hu).mp hn;
    exact ⟨⟨w, reach_of_rel v.2 h⟩, h, rfl⟩;

private lemma pointGenerateBase_surjective {u : D.F.World} (hu : D.path 0 ∉ D.F.Reach u) :
    Function.Surjective (pointGenerateBase (I := I) hu) := by
  rintro ⟨z, n, hn⟩;
  obtain ⟨w, hw, rfl⟩ := (relItr_base_iff_of_not_mem_reach hu).mp hn;
  exact ⟨⟨w, n, hw⟩, rfl⟩;

private lemma pointGenerate_base_validates {α : Type*} {L : NormalLogic α} {u : D.F.World}
    (hu : D.path 0 ∉ D.F.Reach u) (h : D.F⥜u ⊧ L) :
    (D.hookFrame I)⥜(.base u) ⊧ L :=
  ValidateLogic.of_surjective_pMorphism (pointGenerateBase hu) (pointGenerateBase_surjective hu) h

private lemma surjective_to_pointGenerate_dBot {ι : Type*}
    (f : ι → ((D.hookFrame I)⥜.dBot).World) [Nonempty ι] :
    Function.Surjective f := by
  rintro ⟨z, n, hn⟩;
  obtain rfl := eq_dBot_of_dBot_relItr hn;
  obtain ⟨k, hk⟩ := (f (Classical.arbitrary ι)).2;
  exact ⟨Classical.arbitrary ι, Subtype.ext <| eq_dBot_of_dBot_relItr hk⟩;

private lemma pointGenerate_dBot_validates {α : Type*} {L : NormalLogic α}
    (h₁ : ¬D.refl → deadEnd ⊧ L) (h₂ : D.refl → reflPoint ⊧ L) :
    (D.hookFrame I)⥜.dBot ⊧ L := by
  by_cases hr : D.refl;
  · let f : reflPoint →ₚ (D.hookFrame I)⥜.dBot :=
      { toFun := fun _ => (pointGenerate.root _ _).1
        forth := fun _ => hr
        back := by
          rintro _ ⟨z, n, hn⟩ -;
          obtain rfl := eq_dBot_of_dBot_relItr hn;
          exact ⟨0, trivial, rfl⟩ };
    exact ValidateLogic.of_surjective_pMorphism f (surjective_to_pointGenerate_dBot f) (h₂ hr);
  · let f : deadEnd →ₚ (D.hookFrame I)⥜.dBot :=
      { toFun := fun _ => (pointGenerate.root _ _).1
        forth := fun h => h.elim
        back := fun h => absurd (rel_dBot_iff.mp h).2 hr };
    exact ValidateLogic.of_surjective_pMorphism f (surjective_to_pointGenerate_dBot f) (h₁ hr);

/-- If `x ∈ D.detached I` and `φ ∈ L`, then `x ⊩[(D.hooked I).model V] φ`, provided
`D.F⥜u ⊧ L` for every non-root `u`, `deadEnd ⊧ L` when `¬D.refl`, and `reflPoint ⊧ L` when
`D.refl`.
- [CZ98, p. 367]
-/
private lemma forces_of_mem_detached {α : Type*} {L : NormalLogic α}
    (hF : ∀ u : D.F.World, ¬D.F.IsRootedBy u → D.F⥜u ⊧ L)
    (h₁ : ¬D.refl → deadEnd ⊧ L) (h₂ : D.refl → reflPoint ⊧ L)
    (hx : x ∈ D.detached I) {φ : Formula α} (hA : φ ∈ L) (V : D.World I → α → Prop) :
    x ⊩[(D.hooked I).model V] φ := by
  rcases hx with rfl | ⟨u, rfl, hu⟩;
  · exact GeneralFrame.forces_of_pointGenerate_validatesLogic
      (G := D.hooked I) (pointGenerate_dBot_validates h₁ h₂) hA V;
  · apply GeneralFrame.forces_of_pointGenerate_validatesLogic (G := D.hooked I) _ hA V;
    apply pointGenerate_base_validates hu;
    exact hF u fun hr => hu <| hr _;

/-- If `D.refl` and every point of `D.F` has a successor, then every point of the hooked frame
has a successor.
- [CZ98, p. 367]
-/
lemma exists_rel (hr : D.refl) (hF : ∀ u : D.F.World, ∃ v, u ≺ v) (x : (D.hookFrame I).World) :
    ∃ y, x ≺ y := by
  cases x with
  | base u =>
    obtain ⟨v, hv⟩ := hF u;
    exact ⟨.base v, hv⟩;
  | copy t ht => exact ⟨.base (D.path (t + 2)), D.path_rel (t + 1)⟩;
  | c => exact ⟨.b, by simp [Rel]⟩;
  | b => exact ⟨.a 0 false (by simp), by simp [Rel]⟩;
  | a i t h =>
    rcases Nat.eq_zero_or_pos i with rfl | hi;
    · exact ⟨.d D.m le_rfl, by simp [Rel]⟩;
    · exact ⟨.a 0 false (by simp), by simpa [Rel] using hi⟩;
  | d j hj =>
    cases j with
    | zero => exact ⟨.dBot, by simp [Rel]⟩;
    | succ j => exact ⟨.d j (by omega), by simp [Rel]⟩;
  | dBot => exact ⟨.dBot, hr⟩;

variable [Finite D.F.World]

/-- If `x ∉ D.detached I`, then `x ≺^[n] .d 0 _` for some `n ≤ D.m + 3`.
- [CZ98, p. 367]
-/
private lemma exists_relItr_d_zero (hx : x ∉ D.detached I) :
    ∃ n ≤ D.m + 3, x ≺^[n] .d 0 (Nat.zero_le _) := by
  have hm := D.card_add_len_lt;
  have hcopy (t : ℕ) (ht : t ≤ D.len) :
      RelItr (F := D.hookFrame I) (D.len - t + 1) (.copy t ht) (.d 0 (Nat.zero_le _)) :=
    relItr_tail (relItr_copy (ht' := le_rfl) ht) (by simp [Rel]);
  have hdm : RelItr (F := D.hookFrame I) (D.m - 0) (.d D.m le_rfl) (.d 0 (Nat.zero_le _)) :=
    relItr_d (Nat.zero_le _);
  have ha₀ : RelItr (F := D.hookFrame I) (D.m - 0 + 1) (.a 0 false (by simp))
      (.d 0 (Nat.zero_le _)) :=
    relItr_head (by simp [Rel]) hdm;
  cases x with
  | base u =>
    have hu : D.path 0 ∈ D.F.Reach u := by simpa using hx;
    obtain ⟨k, hk, hku⟩ := exists_relItr_lt_card hu;
    exact ⟨_, by omega, relItr_trans (relItr_base hku) <|
      relItr_head (y := .copy 0 (Nat.zero_le _)) (by simp [Rel]) (hcopy 0 _)⟩;
  | copy t ht => exact ⟨_, by omega, hcopy t ht⟩;
  | c => exact ⟨_, by omega, relItr_head (y := .b) (by simp [Rel]) <|
      relItr_head (by simp [Rel]) ha₀⟩;
  | b => exact ⟨_, by omega, relItr_head (by simp [Rel]) ha₀⟩;
  | a i t h =>
    rcases Nat.eq_zero_or_pos i with rfl | hi;
    · exact ⟨_, by omega, relItr_head (by simp [Rel]) hdm⟩;
    · exact ⟨_, by omega, relItr_head (by simpa [Rel] using hi) ha₀⟩;
  | d j hj => exact ⟨_, by omega, relItr_d (Nat.zero_le j)⟩;
  | dBot => exact absurd dBot_mem_detached hx;

/-- `.d 0 _ ≺^[n] y` for some `n ≤ D.m + 4`.
- [CZ98, p. 367]
-/
private lemma d_zero_exists_relItr (y : (D.hookFrame I).World) :
    ∃ n ≤ D.m + 4, RelItr (F := D.hookFrame I) n (.d 0 (Nat.zero_le _)) y := by
  have hm := D.card_add_len_lt;
  have hb : RelItr (F := D.hookFrame I) (1 + 1) (.d 0 (Nat.zero_le _)) .b :=
    relItr_head (y := .c) (by simp [Rel]) <| relItr_head (by simp [Rel]) relItr_zero_self;
  have hroot (v : D.F.World) : ∃ k < Nat.card D.F.World,
      RelItr (F := D.hookFrame I) (1 + k) (.d 0 (Nat.zero_le _)) (.base v) := by
    obtain ⟨k, hk, hkv⟩ := exists_relItr_lt_card (D.root.2 v);
    exact ⟨k, hk, relItr_trans (n := 1) (by simp [Rel]) (relItr_base hkv)⟩;
  cases y with
  | base v =>
    obtain ⟨k, hk, h⟩ := hroot v;
    exact ⟨_, by omega, h⟩;
  | copy t ht =>
    obtain ⟨k, hk, h⟩ := hroot (D.path 0);
    exact ⟨_, by omega, relItr_trans h <| relItr_head (y := .copy 0 (Nat.zero_le _))
      (by simp [Rel]) (relItr_copy (ht' := ht) (Nat.zero_le t))⟩;
  | c => exact ⟨1, by omega, by simp [Rel]⟩;
  | b => exact ⟨_, by omega, hb⟩;
  | a i t h => exact ⟨_, by omega, relItr_tail hb (z := .a i t h) (by simp [Rel])⟩;
  | d j hj =>
    exact ⟨_, by omega, relItr_trans hb <| relItr_head (y := .a 0 false (by simp))
      (by simp [Rel]) <| relItr_head (by simp [Rel]) (relItr_d (hj' := le_rfl) hj)⟩;
  | dBot => exact ⟨1, by omega, by simp [Rel]⟩;

/-- If `x ∉ D.detached I`, then `x ≺^[n] y` for some `n ≤ 2 * D.m + 7`.
- [CZ98, p. 367]
-/
private lemma exists_relItr_of_not_mem_detached (hx : x ∉ D.detached I)
    (y : (D.hookFrame I).World) :
    ∃ n ≤ 2 * D.m + 7, x ≺^[n] y := by
  obtain ⟨k, hk, h⟩ := exists_relItr_d_zero hx;
  obtain ⟨k', hk', h'⟩ := d_zero_exists_relItr y;
  exact ⟨_, by omega, relItr_trans h h'⟩;

lemma exists_relItr_c (hx : x ∉ D.detached I) : ∃ n ≤ D.m + 4, x ≺^[n] .c := by
  obtain ⟨k, hk, h⟩ := exists_relItr_d_zero hx;
  exact ⟨_, by omega, relItr_tail h (by simp [Rel])⟩;

private lemma exists_relItr_dBot (hx : x ∉ D.detached I) : ∃ n ≤ D.m + 4, x ≺^[n] .dBot := by
  obtain ⟨k, hk, h⟩ := exists_relItr_d_zero hx;
  exact ⟨_, by omega, relItr_tail h (by simp [Rel])⟩;

end Reach


section Unwound

/-! ### The size of the unwound frame -/

variable (D I) in
def unwoundPoint : D.F.World ⊕ Fin (D.len + 1) → D.World I
  | .inl u => .base u
  | .inr t => .copy t (by omega)

private lemma range_unwoundPoint : Set.range (D.unwoundPoint I) = {w | w.IsUnwound} := by
  ext w;
  constructor;
  · rintro ⟨u | t, rfl⟩ <;> trivial;
  · intro hw;
    rcases isUnwound_iff.mp hw with ⟨u, rfl⟩ | ⟨t, ht, rfl⟩;
    · exact ⟨.inl u, rfl⟩;
    · exact ⟨.inr ⟨t, by omega⟩, rfl⟩;

variable [Finite D.F.World]

private lemma finite_isUnwound : {w : D.World I | w.IsUnwound}.Finite :=
  range_unwoundPoint ▸ Set.finite_range _

private lemma ncard_isUnwound_le :
    {w : D.World I | w.IsUnwound}.ncard ≤ Nat.card D.F.World + D.len + 1 := by
  rw [← range_unwoundPoint, ← Set.image_univ];
  calc (D.unwoundPoint I '' Set.univ).ncard
      ≤ (Set.univ : Set (D.F.World ⊕ Fin (D.len + 1))).ncard := Set.ncard_image_le Set.finite_univ
    _ = Nat.card D.F.World + D.len + 1 := by simp [Set.ncard_univ, Nat.card_sum]; omega;

private lemma ncard_isUnwound_lt : {w : D.World I | w.IsUnwound}.ncard < D.m := by
  have := D.card_add_len_lt;
  have := ncard_isUnwound_le (D := D) (I := I);
  omega;

end Unwound


end

/-! ## Transfer -/

section

open Formula Model.World

variable {κ : Type u} {D : HookData κ} {I : Set ℕ} {α : Type*}

section Unwind

variable (D) in
def unwindRel : D.F.World ⊕ Fin (D.len + 1) → D.F.World ⊕ Fin (D.len + 1) → Prop
  | .inl u, .inl v => u ≺ v
  | .inl u, .inr t => u = D.path 0 ∧ t.1 = 0
  | .inr t, .inl v => D.path (t.1 + 1) ≺ v
  | .inr t, .inr t' => t'.1 = t.1 + 1

variable (D) in
/-- The frame on `D.F.World ⊕ Fin (D.len + 1)` with relation `D.unwindRel`.
- [CZ98, Fig. 10.4]
-/
def unwind : Frame (D.F.World ⊕ Fin (D.len + 1)) := ⟨D.unwindRel⟩

variable (D) in
/-- The p-morphism `D.unwind →ₚ D.F`.
- [CZ98, Fig. 10.4]
-/
def unwindProj : D.unwind →ₚ D.F where
  toFun
    | .inl u => u
    | .inr t => D.path (t.1 + 1)
  forth {x y} h := by
    rcases x with u | t <;> rcases y with v | t';
    · exact h;
    · obtain ⟨rfl, ht'⟩ := h;
      simpa [ht'] using D.path_rel 0;
    · exact h;
    · have ht' : t'.1 = t.1 + 1 := h;
      simpa [ht'] using D.path_rel (t.1 + 1);
  back {x z} h := by
    rcases x with u | t <;> exact ⟨.inl z, h, rfl⟩

private lemma unwindProj_surjective : Function.Surjective (D.unwindProj) := fun u => ⟨.inl u, rfl⟩

private lemma validates_of_unwind_validates {L : NormalLogic α} (h : D.unwind ⊧ L) : D.F ⊧ L :=
  Frame.ValidateLogic.of_surjective_pMorphism D.unwindProj unwindProj_surjective h

end Unwind


variable (D I) in
def liftVal (V : D.F.World → α → Prop) : D.World I → α → Prop
  | .base u, a => V u a
  | .copy t _, a => V (D.path (t + 1)) a
  | _, _ => False

private lemma isAdmissible_liftVal (V : D.F.World → α → Prop) :
    (D.hooked I).IsAdmissible (D.liftVal I V) := by
  intro a;
  apply mem_adm_of_forall;
  intro w hw;
  cases w <;> simp_all [liftVal, World.IsA];

section Transfer

variable [DecidableEq α]

/-- If `V'` agrees with `V` on `.base u` and `.copy t _` for the atoms of `φ`, then
`.base u ⊩ φ ↔ u ⊩ φ` when `φ.depth ≤ D.len + 1`, and
`.copy t _ ⊩ φ ↔ D.path (t + 1) ⊩ φ` when `φ.depth + t ≤ D.len`.
- [Blok78, Theorem 4.6]
- [CZ98, Proposition 3.2]
-/
theorem forces_transfer {P : α → Prop} {V : D.F.World → α → Prop} {V' : D.World I → α → Prop}
    (hbase : ∀ u a, P a → (V' (.base u) a ↔ V u a))
    (hcopy : ∀ t ht a, P a → (V' (.copy t ht) a ↔ V (D.path (t + 1)) a))
    {φ : Formula α} (hA : ∀ a ∈ φ.atoms, P a) :
    (∀ u, φ.depth ≤ D.len + 1 →
      ((.base u : D.World I) ⊩[(D.hooked I).model V'] φ ↔ u ⊩[⟨D.F, V⟩] φ)) ∧
    (∀ t ht, φ.depth + t ≤ D.len →
      ((.copy t ht : D.World I) ⊩[(D.hooked I).model V'] φ ↔ D.path (t + 1) ⊩[⟨D.F, V⟩] φ)) := by
  induction φ with
  | atom a =>
    have ha : P a := hA a <| by simp;
    exact ⟨fun u _ => hbase u a ha, fun t ht _ => hcopy t ht a ha⟩;
  | falsum => exact ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩;
  | imp φ ψ ihφ ihψ =>
    obtain ⟨hA₁, hA₂⟩ := ihφ fun a ha => hA a <| by simp [ha];
    obtain ⟨hB₁, hB₂⟩ := ihψ fun a ha => hA a <| by simp [ha];
    constructor;
    · intro u hu;
      simp only [depth_imp, sup_le_iff] at hu;
      exact imp_congr (hA₁ u hu.1) (hB₁ u hu.2);
    · intro t ht h;
      simp only [depth_imp] at h;
      exact imp_congr (hA₂ t ht <| by omega) (hB₂ t ht <| by omega);
  | dia φ ih =>
    obtain ⟨h₁, h₂⟩ := ih hA;
    simp only [depth_dia];
    constructor;
    · intro u hu;
      constructor;
      · rintro ⟨y, hy, hyA⟩;
        rcases rel_base_iff.mp hy with ⟨v, rfl, Ruv⟩ | ⟨rfl, rfl⟩;
        · exact ⟨v, Ruv, (h₁ v <| by omega).mp hyA⟩;
        · exact ⟨D.path 1, D.path_rel 0, (h₂ 0 _ <| by omega).mp hyA⟩;
      · rintro ⟨v, Ruv, hv⟩;
        exact ⟨.base v, Ruv, (h₁ v <| by omega).mpr hv⟩;
    · intro t ht h;
      constructor;
      · rintro ⟨y, hy, hyA⟩;
        rcases rel_copy_iff.mp hy with ⟨v, rfl, hv⟩ | ⟨ht', rfl⟩ | ⟨rfl, -⟩;
        · exact ⟨v, hv, (h₁ v <| by omega).mp hyA⟩;
        · exact ⟨D.path (t + 1 + 1), D.path_rel (t + 1), (h₂ (t + 1) ht' <| by omega).mp hyA⟩;
        · omega;
      · rintro ⟨v, hv, hvA⟩;
        exact ⟨.base v, hv, (h₁ v <| by omega).mpr hvA⟩;

end Transfer

/-- If `φ.depth ≤ D.len + 1`, then `.base u ⊩ φ` under `D.liftVal I V` iff `u ⊩ φ` under `V`.
- [Blok78, Theorem 4.6]
- [CZ98, Proposition 3.2]
-/
theorem forces_liftVal_base_iff {V : D.F.World → α → Prop} {φ : Formula α}
    (hA : φ.depth ≤ D.len + 1) (u : D.F.World) :
    (.base u : D.World I) ⊩[(D.hooked I).model (D.liftVal I V)] φ ↔ u ⊩[⟨D.F, V⟩] φ := by
  classical
  exact (forces_transfer (P := fun _ => True) (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (fun _ _ => trivial)).1 u hA


end

/-! ## Naming -/

section

open World Naming Formula Model.World

variable {κ : Type u} {D : HookData κ} {I : Set ℕ} {N : ℕ} {V : D.World I → ℕ → Prop}

section Rel

variable {x y : (D.hookFrame I).World}

private lemma not_isUnwound_of_rel (hx : ¬x.IsUnwound) (hxd : x ≠ .d 0 (Nat.zero_le _))
    (Rxy : x ≺ y) :
    ¬y.IsUnwound := by
  cases x <;> cases y <;> simp_all [Rel, IsUnwound];

private lemma ne_dBot_of_rel (hx : x ≠ .dBot) (hxd : x ≠ .d 0 (Nat.zero_le _)) (Rxy : x ≺ y) :
    y ≠ .dBot := by
  rintro rfl;
  rcases rel_to_dBot_iff.mp Rxy with h | ⟨rfl, -⟩;
  · exact hxd h;
  · exact hx rfl;

private lemma two_le_m : 2 ≤ D.m := by
  have := D.card_add_len_lt;
  omega;

end Rel


section Naming

def Reaches (D : HookData κ) (I : Set ℕ) (N : ℕ) : Prop :=
  ∀ x : (D.hookFrame I).World, ¬x.IsUnwound → x ≠ .dBot → ∀ y, ∃ n ≤ N, x ≺^[n] y

variable (hreach : D.Reaches I N) (h₁ : ∃ w, V w 0) (h₂ : ∃ w, ¬V w 0)

local notation "𝓜" => GeneralFrame.model (HookData.hooked D I) V

private lemma forces_tau_dBot : (.dBot : D.World I) ⊩[𝓜] tau N := by
  rw [forces_tau];
  by_cases h : V .dBot 0;
  · exact Or.inl fun _ _ y hy => (eq_dBot_of_dBot_relItr hy) ▸ h;
  · exact Or.inr fun _ _ y hy => (eq_dBot_of_dBot_relItr hy) ▸ h;

include hreach h₁ h₂

private lemma not_forces_tau_of_ne_dBot {x : D.World I} (hx : ¬x.IsUnwound) (hxd : x ≠ .dBot) :
    x ⊮[𝓜] tau N :=
  not_forces_tau_of_reach (hreach x hx hxd) h₁ h₂

private lemma forces_delta_zero_iff {x : D.World I} (hx : ¬x.IsUnwound) :
    x ⊩[𝓜] delta N 0 ↔ x = .d 0 (Nat.zero_le _) := by
  rw [delta_zero, forces_and, forces_neg, forces_dia];
  constructor;
  · rintro ⟨⟨y, Rxy, hy⟩, hxτ⟩;
    by_contra hxd;
    have hxb : x ≠ .dBot := by
      rintro rfl;
      exact hxτ forces_tau_dBot;
    exact not_forces_tau_of_ne_dBot hreach h₁ h₂ (not_isUnwound_of_rel hx hxd Rxy)
      (ne_dBot_of_rel hxb hxd Rxy) hy;
  · rintro rfl;
    exact ⟨⟨.dBot, rfl, forces_tau_dBot⟩,
      not_forces_tau_of_ne_dBot hreach h₁ h₂ hx (by simp)⟩;

/-- If `¬x.IsUnwound`, then `x ⊩ delta N j ↔ x = .d j hj`.
- [CZ98, Example 10.57]
-/
private lemma forces_delta_iff {j : ℕ} (hj : j ≤ D.m) {x : D.World I} (hx : ¬x.IsUnwound) :
    x ⊩[𝓜] delta N j ↔ x = .d j hj := by
  induction j using Nat.strong_induction_on generalizing x with
  | _ j ih =>
    cases j with
    | zero => exact forces_delta_zero_iff hreach h₁ h₂ hx;
    | succ j =>
      rw [forces_delta_succ, forces_dia];
      constructor;
      · rintro ⟨⟨y, Rxy, hy⟩, hne⟩;
        by_cases hyu : y.IsUnwound;
        · rcases isUnwound_of_rel hyu Rxy with h | rfl;
          · exact absurd h hx;
          · exact absurd ((forces_delta_zero_iff hreach h₁ h₂ hx).mpr rfl) (hne 0 (by omega));
        · obtain rfl := (ih j (by omega) (by omega) hyu).mp hy;
          rcases rel_to_d_iff.mp Rxy with ⟨h, rfl⟩ | ⟨-, rfl⟩ | ⟨h, -⟩;
          · rfl;
          · simp [IsUnwound] at hx;
          · omega;
      · rintro rfl;
        constructor;
        · exact ⟨.d j (by omega), rfl, (ih j (by omega) (by omega) (by simp [IsUnwound])).mpr rfl⟩;
        · intro i hi h;
          have := (ih i (by omega) (by omega) hx).mp h;
          simp only [d.injEq] at this;
          omega;

private lemma forces_pi_d : ∀ j (hj : j ≤ D.m), (.d j hj : D.World I) ⊩[𝓜] pi N j
  | 0, _ => (forces_delta_zero_iff hreach h₁ h₂ (by simp [IsUnwound])).mpr rfl
  | j + 1, hj => forces_pi_succ.mpr
      ⟨(forces_delta_iff hreach h₁ h₂ hj (by simp [IsUnwound])).mpr rfl, World.d j (by omega), rfl,
        forces_pi_d j (by omega)⟩

private lemma exists_isUnwound_forces_delta {j : ℕ} (hj : j ≤ D.m) {x : D.World I}
    (hx : x.IsUnwound)
    (h : x ⊩[𝓜] pi N j) :
    ∀ i, 1 ≤ i → i ≤ j → ∃ w : D.World I, w.IsUnwound ∧ w ⊩[𝓜] delta N i := by
  induction j generalizing x with
  | zero => intro i hi hi'; omega;
  | succ j ih =>
    obtain ⟨hxδ, y, Rxy, hy⟩ := forces_pi_succ.mp h;
    intro i hi hi';
    rcases Nat.lt_or_ge j i with hji | hji;
    · rw [show i = j + 1 by omega];
      exact ⟨x, hx, hxδ⟩;
    · rcases isUnwound_of_isUnwound_rel hx Rxy with hyu | rfl;
      · exact ih (by omega) hyu hy i hi hji;
      · have := (forces_delta_iff hreach h₁ h₂ (j := j) (by omega) (by simp [IsUnwound])).mp
          (forces_delta_of_forces_pi hy);
        simp only [d.injEq] at this;
        omega;

/-- `x ⊩ pi N D.m ↔ x = .d D.m _`.
- [CZ98, Example 10.57]
-/
private lemma forces_pi_iff [Finite D.F.World] {x : D.World I} :
    x ⊩[𝓜] pi N D.m ↔ x = .d D.m le_rfl := by
  constructor;
  · intro h;
    by_cases hx : x.IsUnwound;
    · exfalso;
      choose w hwu hwδ using exists_isUnwound_forces_delta hreach h₁ h₂ le_rfl hx h;
      have hne : ∀ a b (ha : 1 ≤ a) (ha' : a ≤ D.m) (hb : 1 ≤ b) (hb' : b ≤ D.m), a < b →
          w a ha ha' ≠ w b hb hb' := by
        intro a b ha ha' hb hb' hab he;
        have h' := hwδ a ha ha';
        rw [he] at h';
        exact not_forces_delta_of_lt hab h' (hwδ b hb hb');
      let f : Fin D.m → D.World I := fun k => w (k + 1) (by omega) (by omega);
      have hinj : Set.InjOn f Set.univ := by
        intro k _ k' _ he;
        by_contra hkk;
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hkk) with hlt | hlt;
        · exact hne _ _ _ _ _ _ (by omega) he;
        · exact hne _ _ _ _ _ _ (by omega) he.symm;
      have := Set.ncard_le_ncard_of_injOn f (fun k _ => hwu _ _ _) hinj finite_isUnwound;
      rw [Set.ncard_univ, Nat.card_fin] at this;
      have := ncard_isUnwound_lt (D := D) (I := I);
      omega;
    · exact (forces_delta_iff hreach h₁ h₂ le_rfl hx).mp (forces_delta_of_forces_pi h);
  · rintro rfl;
    exact forces_pi_d hreach h₁ h₂ D.m le_rfl;

omit hreach h₁ h₂ in
private lemma forces_dia_alpha_iff_of {φ : Formula ℕ} {i : ℕ}
    (hα : ∀ x : D.World I, x ⊩[𝓜] φ ↔ x.IsA ∧ x.index = i) {x : D.World I} :
    x ⊩[𝓜] ◇φ ↔ x = .b ∨ (x.IsA ∧ i < x.index) := by
  rw [forces_dia];
  constructor;
  · rintro ⟨y, Rxy, hy⟩;
    obtain ⟨hyA, rfl⟩ := (hα y).mp hy;
    obtain ⟨i', t, h, rfl⟩ := isA_iff.mp hyA;
    exact rel_to_a_iff.mp Rxy;
  · rintro (rfl | ⟨hxA, hlt⟩);
    · exact ⟨.a i false (by simp), trivial, (hα _).mpr ⟨trivial, rfl⟩⟩;
    · obtain ⟨i', t, h, rfl⟩ := isA_iff.mp hxA;
      exact ⟨.a i false (by simp), hlt, (hα _).mpr ⟨trivial, rfl⟩⟩;

variable [Finite D.F.World]

/-- `x ⊩ alpha N D.m i ↔ x.IsA ∧ x.index = i`.
- [CZ98, Example 10.57]
-/
private lemma forces_alpha_iff (i : ℕ) {x : D.World I} :
    x ⊩[𝓜] alpha N D.m i ↔ x.IsA ∧ x.index = i := by
  induction i generalizing x with
  | zero =>
    have hm := two_le_m (D := D);
    rw [forces_alpha_zero, forces_dia];
    constructor;
    · rintro ⟨⟨y, Rxy, hy⟩, -⟩;
      rw [forces_pi_iff hreach h₁ h₂] at hy;
      subst hy;
      rcases rel_to_d_iff.mp Rxy with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩;
      · omega;
      · omega;
      · exact h;
    · rintro ⟨hxA, h0⟩;
      obtain ⟨i', t, h, rfl⟩ := isA_iff.mp hxA;
      simp only [index_a] at h0;
      subst h0;
      constructor;
      · exact ⟨.d D.m le_rfl, ⟨rfl, rfl⟩, (forces_pi_iff hreach h₁ h₂).mpr rfl⟩;
      · rw [NotForces, forces_dia];
        rintro ⟨y, Rxy, hy⟩;
        obtain ⟨z, Ryz, hz⟩ := forces_dia.mp hy;
        rw [forces_pi_iff hreach h₁ h₂] at hz;
        subst hz;
        rw [rel_a_zero_iff.mp Rxy] at Ryz;
        have : D.m = D.m + 1 := Ryz;
        omega;
  | succ i ih =>
    have hdia := fun {x : D.World I} => forces_dia_alpha_iff_of (x := x) fun _ => ih;
    rw [forces_alpha_succ, hdia, NotForces, forces_dia];
    constructor;
    · rintro ⟨hd, hdd⟩;
      rcases hd with rfl | ⟨hxA, hlt⟩;
      · exact absurd ⟨.a (i + 1) false (by simp), trivial, hdia.mpr <| Or.inr ⟨trivial, by simp⟩⟩
          hdd;
      · obtain ⟨i', t, h, rfl⟩ := isA_iff.mp hxA;
        simp only [index_a] at hlt;
        by_contra hne;
        apply hdd ⟨.a (i + 1) false (by simp), _, hdia.mpr <| Or.inr ⟨trivial, by simp⟩⟩;
        have : i' ≠ i + 1 := fun h' => hne ⟨hxA, h'⟩;
        exact (by omega : i + 1 < i');
    · rintro ⟨hxA, hx⟩;
      obtain ⟨i', t, h, rfl⟩ := isA_iff.mp hxA;
      simp only [index_a] at hx;
      subst hx;
      constructor;
      · exact Or.inr ⟨trivial, by simp⟩;
      · rintro ⟨y, Rxy, hy⟩;
        rcases hdia.mp hy with rfl | ⟨hyA, hlt⟩;
        · exact absurd Rxy (by simp [Rel]);
        · rcases rel_a_iff.mp Rxy with ⟨-, hlt'⟩ | ⟨h', -⟩;
          · omega;
          · omega;

/-- `x ⊩ theta N D.m ↔ x = .b ∨ (x.IsA ∧ 0 < x.index)`.
- [CZ98, Example 10.57]
-/
private lemma forces_theta_iff {x : D.World I} :
    x ⊩[𝓜] theta N D.m ↔ x = .b ∨ (x.IsA ∧ 0 < x.index) :=
  forces_dia_alpha_iff_of fun _ => forces_alpha_iff hreach h₁ h₂ 0

/-- `x ⊩ gamma N D.m ↔ x = .c`.
- [CZ98, Example 10.57]
-/
lemma forces_gamma_iff {x : D.World I} : x ⊩[𝓜] gamma N D.m ↔ x = .c := by
  have hθ := fun {x : D.World I} => forces_theta_iff (x := x) hreach h₁ h₂;
  rw [Naming.forces_gamma, ← theta, forces_dia, NotForces, hθ];
  constructor;
  · rintro ⟨⟨y, Rxy, hy⟩, hn⟩;
    rw [hθ] at hy;
    rcases hy with rfl | ⟨hyA, hpos⟩;
    · exact rel_to_b_iff.mp Rxy;
    · obtain ⟨j, t, h, rfl⟩ := isA_iff.mp hyA;
      rcases rel_to_a_iff.mp Rxy with rfl | ⟨hxA, hlt⟩;
      · exact absurd (Or.inl rfl) hn;
      · simp only [index_a] at hpos hlt;
        exact absurd (Or.inr ⟨hxA, by omega⟩) hn;
  · rintro rfl;
    constructor;
    · exact ⟨.b, trivial, hθ.mpr <| Or.inl rfl⟩;
    · rintro (h | ⟨h, -⟩);
      · simp at h;
      · exact h;

/-- Under an admissible valuation, `.b ⊩ löb N D.m`.
- [CZ98, p. 365]
-/
private lemma forces_löb_b (hV : (D.hooked I).IsAdmissible V) :
    (.b : D.World I) ⊩[𝓜] löb N D.m := by
  classical
  have hθ := fun {x : D.World I} => forces_theta_iff (x := x) hreach h₁ h₂;
  rw [forces_löb];
  intro h;
  by_contra hb;
  have hfin : {w : D.World I | w.IsA ∧ w ∈ {w | V w 1}}.Finite := (mem_adm_iff.mp (hV 1)).2 hb;
  have hex : ∃ i, 1 ≤ i ∧ ∃ z : D.World I, z.IsA ∧ z.index = i ∧ ¬V z 1 := by
    by_contra hne;
    push Not at hne;
    apply Set.infinite_of_injective_forall_mem
      (f := fun i : ℕ => (.a (i + 1) false (by simp) : D.World I)) _ _ hfin;
    · intro i i' he;
      simpa using he;
    · intro i;
      exact ⟨trivial, hne (i + 1) (by omega) _ trivial rfl⟩;
  obtain ⟨hi, z, hzA, hzi, hz⟩ := Nat.find_spec hex;
  have hmin : ∀ y : D.World I, y.IsA → 1 ≤ y.index → y.index < Nat.find hex → V y 1 := by
    intro y hyA hy hlt;
    by_contra hy';
    exact Nat.find_min hex hlt ⟨hy, y, hyA, rfl, hy'⟩;
  have hzθ : z ⊩[𝓜] theta N D.m := hθ.mpr <| Or.inr ⟨hzA, by omega⟩;
  apply hz;
  apply forces_imp.mp (forces_box₀.mp h z (rel_b_iff.mpr hzA) hzθ) |>.resolve_left;
  rw [NotForces, not_not, forces_box₀];
  intro y hzy hy;
  obtain ⟨i', t, h', rfl⟩ := isA_iff.mp hzA;
  rcases hθ.mp hy with rfl | ⟨hyA, hpos⟩;
  · exact absurd hzy (by simp [Rel]);
  · rcases rel_a_iff.mp hzy with ⟨-, hlt⟩ | ⟨h'', -⟩;
    · exact hmin y hyA hpos (by simpa [← hzi] using hlt);
    · simp only [index_a] at hzi;
      omega;

end Naming


section Validity

variable [Finite D.F.World] (hreach : D.Reaches I N)
include hreach

/-- `D.hooked I ⊧ gammaLöb N D.m`.
- [CZ98, p. 365]
-/
theorem validates_gammaLöb : D.hooked I ⊧ gammaLöb N D.m := by
  intro V hV x;
  rw [forces_gammaLöb];
  intro hx y Rxy;
  by_cases hq : (∀ w, V w 0) ∨ (∀ w, ¬V w 0);
  · exact absurd hx <| not_forces_gamma_of_const (M := (D.hooked I).model V) hq;
  · push Not at hq;
    obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := hq;
    rw [forces_gamma_iff hreach ⟨w₂, hw₂⟩ ⟨w₁, hw₁⟩] at hx;
    subst hx;
    rw [rel_c_iff.mp Rxy];
    exact forces_löb_b hreach ⟨w₂, hw₂⟩ ⟨w₁, hw₁⟩ hV;

/-- If `i ∉ I`, `x ⊩ alpha N D.m i` and `y ⊩ alpha N D.m i`, then `x = y`.
- [CZ98, p. 367]
-/
theorem alpha_unique {i : ℕ} (hi : i ∉ I) (V : D.World I → ℕ → Prop) {x y : D.World I}
    (hx : x ⊩[(D.hooked I).model V] alpha N D.m i) (hy : y ⊩[(D.hooked I).model V] alpha N D.m i) :
    x = y := by
  by_cases hq : (∀ w, V w 0) ∨ (∀ w, ¬V w 0);
  · exact absurd hx <| not_forces_alpha_of_const (M := (D.hooked I).model V) hq;
  · push Not at hq;
    obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := hq;
    obtain ⟨hxA, hxi⟩ := (forces_alpha_iff hreach ⟨w₂, hw₂⟩ ⟨w₁, hw₁⟩ i).mp hx;
    obtain ⟨hyA, hyi⟩ := (forces_alpha_iff hreach ⟨w₂, hw₂⟩ ⟨w₁, hw₁⟩ i).mp hy;
    obtain ⟨i₁, t₁, h₁, rfl⟩ := isA_iff.mp hxA;
    obtain ⟨i₂, t₂, h₂, rfl⟩ := isA_iff.mp hyA;
    simp only [index_a] at hxi hyi;
    subst hxi hyi;
    cases t₁ <;> cases t₂;
    · rfl;
    · exact absurd (h₂ rfl) hi;
    · exact absurd (h₁ rfl) hi;
    · rfl;

end Validity


section Interface

open NormalLogic

variable [Finite D.F.World] {L : NormalLogic ℕ} [L.IsNExt 𝐊]

omit [Finite D.F.World] [L.IsNExt 𝐊] in
lemma exists_rel_of_not_deadEnd (hF : ∀ u : D.F.World, ¬D.F.IsRootedBy u → D.F⥜u ⊧ L)
    (h : deadEnd ⊭ L) (u : D.F.World) : ∃ v, u ≺ v := by
  by_contra! hu;
  by_cases hr : D.F.IsRootedBy u;
  · obtain ⟨n, hn⟩ := hr (D.path 0);
    cases n with
    | zero =>
      rw [Frame.iff_relItr_zero] at hn;
      exact hu _ <| hn ▸ D.path_rel 0;
    | succ n =>
      obtain ⟨v, Ruv, -⟩ := hn;
      exact hu v Ruv;
  · apply h;
    have hreach : ∀ x ∈ D.F.Reach u, x = u := by
      rintro x ⟨n, hn⟩;
      cases n with
      | zero => exact (Frame.iff_relItr_zero.mp hn).symm;
      | succ n =>
        obtain ⟨v, Ruv, -⟩ := hn;
        exact absurd Ruv (hu v);
    let f : D.F⥜u →ₚ deadEnd :=
      { toFun := fun _ => 0
        forth := fun {x y} Rxy => by
          have Rxy' : x.1 ≺ y.1 := Rxy;
          rw [hreach x.1 x.2] at Rxy';
          exact absurd Rxy' (hu _)
        back := fun h => h.elim };
    exact Frame.ValidateLogic.of_surjective_pMorphism f
      (fun _ => ⟨(Frame.pointGenerate.root _ _).1, Subsingleton.elim _ _⟩) (hF u hr);

lemma reaches (I : Set ℕ) : D.Reaches I (2 * D.m + 7) := by
  intro x hx hxd y;
  apply exists_relItr_of_not_mem_detached _ y;
  intro hd;
  rcases eq_dBot_or_isUnwound_of_mem_detached hd with h | h;
  · exact hxd h;
  · exact hx h;

/-- `D.hooked I` satisfies `Naming.HookInterface`.
- [CZ98, p. 365, p. 367, p. 368]
-/
noncomputable def hookInterface (hc : L.Consistent)
    (hF : ∀ u : D.F.World, ¬D.F.IsRootedBy u → D.F⥜u ⊧ L)
    (hrefl : D.refl ↔ deadEnd ⊭ L) {φ : Formula ℕ} {V₀ : D.F.World → ℕ → Prop}
    (hV₀ : D.root ⊮[⟨D.F, V₀⟩] φ) (hdepth : φ.depth ≤ D.len + 1) (I : Set ℕ) :
    HookInterface L (2 * D.m + 7) D.m (D.m + 4) (D.m + 3) (shift φ) I (D.hooked I) where
  safe := D.detached I
  forces_of_mem_safe hx _ hA V := by
    apply forces_of_mem_detached hF _ _ hx hA V;
    · exact fun h => not_not.mp <| mt hrefl.mpr h;
    · intro h;
      apply reflPoint_validates_of_mem hc;
      by_contra h';
      exact hrefl.mp h <| deadEnd_validates_of_not_mem h';
  serial h x := exists_rel (hrefl.mpr h) (exists_rel_of_not_deadEnd hF h) x
  gammaPoint := .c
  gammaPoint_forces V _ h₁ h₂ := (forces_gamma_iff (reaches I) h₁ h₂).mpr rfl
  reach_gammaPoint hx := exists_relItr_c hx
  reach_deadEnd h _ hx := by
    obtain ⟨n, hn, h'⟩ := exists_relItr_dBot hx;
    use n, hn, .dBot, h';
    intro z hz;
    apply h;
    apply reflPoint_validates_of_mem hc;
    by_contra h'';
    exact hrefl.mp (rel_dBot_iff.mp hz).2 <| deadEnd_validates_of_not_mem h'';
  validates_gammaLöb := validates_gammaLöb (reaches I)
  alpha_unique hi V _ _ _ hx hy := alpha_unique (reaches I) hi V hx hy
  not_validates_xi {i} hi hval := by
    classical
    let V : D.World I → ℕ → Prop := fun w a =>
      if a = 0 then w = .a i false (by simp) else D.liftVal I V₀ w (a - 2);
    have hV : (D.hooked I).IsAdmissible V := by
      intro a;
      by_cases ha : a = 0;
      · subst ha;
        apply mem_adm_of_not_mem_of_finite;
        · simp [V];
        · apply (Set.finite_singleton (World.a i false (by simp) : D.World I)).subset;
          intro w hw;
          simpa [V] using hw.2;
      · simpa [V, ha] using isAdmissible_liftVal (I := I) V₀ (a - 2);
    have h₁ : ∃ w, V w 0 := ⟨.a i false (by simp), by simp [V]⟩;
    have h₂ : ∃ w, ¬V w 0 := ⟨.b, by simp [V]⟩;
    have hα := fun x => forces_alpha_iff (x := x) (reaches I) h₁ h₂ i;
    have h := hval V hV .b;
    rw [xi, forces_neg, NotForces, forces_and, forces_and, forces_dia, forces_dia, forces_neg,
      NotForces, forces_multidox] at h;
    apply h;
    and_intros;
    · exact ⟨.a i false (by simp), trivial, forces_and.mpr
        ⟨(hα _).mpr ⟨trivial, rfl⟩, by simp [V, Model.World.Forces, Model.Val]⟩⟩;
    · exact ⟨.a i true fun _ => hi, trivial, forces_and.mpr
        ⟨(hα _).mpr ⟨trivial, rfl⟩, by simp [V, Model.World.Forces, Model.Val]⟩⟩;
    · intro hbox;
      apply hV₀;
      have h₃ := hbox _ b_relItr_root;
      rwa [forces_shift (V := D.liftVal I V₀) (fun w a => by simp [V]),
        forces_liftVal_base_iff hdepth] at h₃;

end Interface

end

end HookData

/-! ## Minimal counterexample -/

namespace NormalLogic

section
open Frame Model.World

variable {L : NormalLogic ℕ} [L.IsNExt 𝐊]

private def IsCounter (L : NormalLogic ℕ) (n : ℕ) : Prop :=
  ∃ F : Frame (Fin n), F ⊧ coreUnionSplitting L ∧ F ⊭ L

omit [L.IsNExt 𝐊] in
private lemma isCounter_card {ι : Type*} {G : Frame ι} [Finite G.World]
    (h₁ : G ⊧ coreUnionSplitting L) (h₂ : G ⊭ L) : IsCounter L (Nat.card G.World) :=
  ⟨G.transport (Finite.equivFin G.World), validateLogic_transport_iff.mpr h₁,
    fun h => h₂ <| validateLogic_transport_iff.mp h⟩

private lemma exists_isCounter (hL : ¬L.IsUnionSplitting) : ∃ n, IsCounter L n := by
  obtain ⟨φ, hφ, hφc⟩ : ∃ φ ∈ L, φ ∉ coreUnionSplitting L := by
    by_contra! h;
    exact hL <| isUnionSplitting_iff_eq_core.mpr <| le_antisymm h coreUnionSplitting_le;
  obtain ⟨n, G, hG, hGφ⟩ := unionSplitting_fmp (𝔉 := coreFrames L) (fun _ hF => hF.1) hφc;
  exact ⟨n, G, hG, fun h => hGφ <| h φ hφ⟩;

private lemma card_reach_lt {n : ℕ} {F : Frame (Fin n)} {u : Fin n} (hu : ¬F.IsRootedBy u) :
    Nat.card (F.Reach u) < n := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, y ∉ F.Reach u := by simpa [IsRootedBy] using hu;
  calc Nat.card (F.Reach u) = Fintype.card {x // x ∈ F.Reach u} := Nat.card_eq_fintype_card
    _ < Fintype.card (Fin n) := Fintype.card_subtype_lt hy
    _ = n := Fintype.card_fin n;

/-- If `¬L.IsUnionSplitting`, there are a finite frame `F` with root `r`, validating
`coreUnionSplitting L` but not `L`, with `F⥜u ⊧ L` for every non-root `u`, refuting some `φ ∈ L`
at `r`, and with `F.HasCycle`.
- [CZ98, p. 366]
-/
theorem exists_minimal_counterexample (hL : ¬L.IsUnionSplitting) :
    ∃ (n : ℕ) (F : Frame (Fin n)) (r : F.Root),
      F ⊧ coreUnionSplitting L ∧ F ⊭ L ∧
      (∀ u : Fin n, ¬F.IsRootedBy u → F⥜u ⊧ L) ∧
      (∃ φ ∈ L, ∃ V : Fin n → ℕ → Prop, ¬r.1 ⊩[⟨F, V⟩] φ) ∧ F.HasCycle := by
  classical
  have hex := exists_isCounter hL;
  obtain ⟨F, hcore, hnL⟩ := Nat.find_spec hex;
  have hmin (u : Fin (Nat.find hex)) (hu : F⥜u ⊭ L) : F.IsRootedBy u := by
    by_contra hr;
    have h₁ := Nat.find_min' hex <| isCounter_card (ValidateLogic.pointGenerate hcore) hu;
    have h₂ : Nat.card (F⥜u).World < Nat.find hex := card_reach_lt hr;
    omega;
  obtain ⟨φ, hφ, hF⟩ : ∃ φ ∈ L, F ⊭ φ := by
    by_contra! h;
    exact hnL h;
  obtain ⟨V, r, hr⟩ : ∃ V r, ¬r ⊩[⟨F, V⟩] φ := by
    by_contra! h;
    exact hF h;
  have hroot : F.IsRootedBy r := hmin r fun h => hr <| forces_pointGenerate_root.mp <|
    h φ hφ (fun y a => V y.1 a) (pointGenerate.root F r).1;
  use Nat.find hex, F, ⟨r, hroot⟩, hcore, hnL;
  and_intros;
  · intro u hu;
    by_contra h;
    exact hu <| hmin u h;
  · exact ⟨φ, hφ, V, hr⟩;
  · by_contra hc;
    have hmem : (⟨_, F⟩ : FinFrame) ∈ coreFrames L := ⟨⟨⟨r, hroot⟩, hc⟩, hnL⟩;
    exact FinFrame.not_validates_jfFormula (F := ⟨_, F⟩) ⟨⟨r, hroot⟩, hc⟩ <|
      validates_map_finVal_iff.mp <| hcore _ <| jfFormula_mem_unionSplitting hmem;

/-- If `L.Consistent` and `¬L.IsUnionSplitting`, there are `D : HookData (Fin n)`, `φ ∈ L` and `V`
with `¬D.root ⊩[⟨D.F, V⟩] φ`, `φ.depth ≤ D.len + 1`, `D.F ⊧ coreUnionSplitting L`, `D.F ⊭ L`,
`D.F⥜u ⊧ L` for every non-root `u`, `D.refl ↔ deadEnd ⊭ L`, `deadEnd ⊧ L` if `¬D.refl`,
`reflPoint ⊧ L` and no dead end in `D.F` if `D.refl`.
- [CZ98, p. 366]
-/
theorem exists_hookData (hc : L.Consistent) (hL : ¬L.IsUnionSplitting) :
    ∃ (n : ℕ) (D : HookData (Fin n)) (φ : Formula ℕ) (V : Fin n → ℕ → Prop),
      φ ∈ L ∧ ¬D.root ⊩[⟨D.F, V⟩] φ ∧ φ.depth ≤ D.len + 1 ∧
      D.F ⊧ coreUnionSplitting L ∧ D.F ⊭ L ∧
      (∀ u, ¬D.F.IsRootedBy u → D.F⥜u ⊧ L) ∧
      (D.refl ↔ deadEnd ⊭ L) ∧ (¬D.refl → deadEnd ⊧ L) ∧
      (D.refl → reflPoint ⊧ L) ∧ (D.refl → ∀ u : D.F.World, ∃ v, u ≺ v) := by
  obtain ⟨n, F, r, hcore, hnL, hgen, ⟨φ, hφ, V, hV⟩, hcyc⟩ := exists_minimal_counterexample hL;
  obtain ⟨p, hp⟩ := hcyc.exists_path;
  let D : HookData (Fin n) :=
    { F := F, root := r, path := p, path_rel := hp, len := φ.depth,
      m := n + φ.depth + 2, card_add_len_lt := by simp, refl := deadEnd ⊭ L };
  use n, D, φ, V, hφ, hV, by simp [D], hcore, hnL, hgen, Iff.rfl, not_not.mp;
  and_intros;
  · exact (makinson hc).resolve_left;
  · intro hD u;
    by_contra! hu;
    exact hD <| deadEnd_validates_of_forall_not_rel hu <|
      hgen u <| not_isRootedBy_of_forall_not_rel hcyc hu;


end

/-! ## Blok dichotomy -/

section
open Cardinal

variable {L : NormalLogic ℕ} {P : {κ : Type u} → Frame κ → Prop}

/--
`degree P L ≤ 𝔠` for `L : NormalLogic ℕ`.
- [CZ98, §10.5]
-/
theorem degree_le_continuum : degree P L ≤ 𝔠 :=
  calc degree P L ≤ Cardinal.mk (Set (Formula ℕ)) :=
        mk_le_of_injective (f := fun L₁ : Companion P L => (L₁.1 : Set (Formula ℕ)))
          fun _ _ h => Subtype.ext <| SetLike.coe_injective h
    _ = 2 ^ Cardinal.mk (Formula ℕ) := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero mk_le_aleph0
    _ = 𝔠 := two_power_aleph0

variable [L.IsNExt 𝐊]

/--
If `L` is consistent and not a union-splitting of `𝐊`, then its degree is `𝔠`.
- [CZ98, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/
theorem degree_eq_continuum (hc : L.Consistent) (hL : ¬L.IsUnionSplitting)
  : L.degree.{u} (fun _ => True) = 𝔠 := by
  obtain ⟨n, D, φ, V, hφ, hV, hdepth, -, -, hgen, hrefl, -⟩ := exists_hookData hc hL;
  apply le_antisymm degree_le_continuum;
  exact Naming.HookInterface.continuum_le_degree (H := D.hooked)
    (fun I => D.hookInterface hc hgen hrefl hV hdepth I) (Naming.shift_mem hφ) (by omega);

/--
For consistent `L`, the degree of `L` is `1` iff `L` is a union-splitting of `𝐊`.
- [CZ98, Theorem 10.51, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/
theorem degree_eq_one_iff_isUnionSplitting (hc : L.Consistent)
  : L.degree (fun _ => True) = 1 ↔ L.IsUnionSplitting := by
  constructor;
  · intro h;
    exact
      not_not.mp fun hL => (one_lt_aleph0.trans aleph0_lt_continuum).ne'
      ((degree_eq_continuum hc hL).symm.trans h)
  · exact degree_eq_one_of_isUnionSplitting

/--
Blok's dichotomy: the degree of Kripke incompleteness of `L` is `1` or `𝔠`.
- [CZ98, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/
theorem blok_dichotomy : L.degree.{u} (fun _ => True) = 1 ∨ L.degree.{u} (fun _ => True) = 𝔠 := by
  by_cases hc : L.Consistent;
  · by_cases hL : L.IsUnionSplitting;
    · exact Or.inl <| degree_eq_one_of_isUnionSplitting hL;
    · exact Or.inr <| degree_eq_continuum hc hL;
  · exact Or.inl <| degree_eq_one_of_not_consistent hc;


end

end NormalLogic

end
