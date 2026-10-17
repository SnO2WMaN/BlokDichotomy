module

public import BlokDichotomy.Kripke.Basic

/-!
# Löb-type formulas naming the points of the hooked frames

The formulas `tau`, `delta`, `pi`, `alpha`, `gamma`, `theta`, `löb`, `gammaLöb` and `xi`, with
their truth conditions in Kripke models.

## References

- [CZ98, Example 10.57, Example 10.58, p. 365]
-/

@[expose] public section

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
lemma delta_succ : delta N (j + 1) = ◇delta N j ⋏ ∼deltaUpTo N j := rfl
@[simp] lemma deltaUpTo_zero : deltaUpTo N 0 = delta N 0 := rfl
lemma deltaUpTo_succ : deltaUpTo N (j + 1) = deltaUpTo N j ⋎ delta N (j + 1) := rfl


section Atoms

lemma atoms_tau : ∀ a ∈ (tau N).atoms, a = 0 := by
  intro a ha;
  simpa [tau] using ha;

lemma atoms_deltaPair (j : ℕ) :
    (∀ a ∈ (deltaPair N j).1.atoms, a = 0) ∧ ∀ a ∈ (deltaPair N j).2.atoms, a = 0 := by
  induction j with
  | zero => simpa [deltaPair] using atoms_tau;
  | succ j ih =>
    constructor <;>
    · intro a ha;
      simp only [deltaPair, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
      grind;

lemma atoms_pi : ∀ a ∈ (pi N j).atoms, a = 0 := by
  induction j with
  | zero => exact (atoms_deltaPair 0).1;
  | succ j ih =>
    intro a ha;
    simp only [pi, delta, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
    have := (atoms_deltaPair (N := N) (j + 1)).1 a;
    grind;

lemma atoms_alpha : ∀ a ∈ (alpha N m i).atoms, a = 0 := by
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

lemma atoms_gamma : ∀ a ∈ (gamma N m).atoms, a = 0 := by
  intro a ha;
  simp only [gamma, atoms_imp, atoms_dia, atoms_bot, Finset.mem_union] at ha;
  have := atoms_alpha (N := N) (m := m) (i := 0) a;
  grind;

end Atoms


section Semantics

variable {κ : Type*} {M : Model κ ℕ} {x : M.World}

lemma forces_congr_of_atoms_subset {φ : Formula ℕ} (hA : ∀ a ∈ φ.atoms, a = 0)
    {V : M.World → ℕ → Prop}
    (hV : ∀ w, M.Val w 0 ↔ V w 0) : x ⊩[M] φ ↔ x ⊩[⟨M.toFrame, V⟩] φ :=
  forces_congr_of_atoms fun a ha w => by rw [hA a ha]; exact hV w

lemma forces_tau :
    x ⊩ tau N ↔ (∀ i ≤ N, ∀ y, (x ≺^[i] y) → M.Val y 0) ∨
      (∀ i ≤ N, ∀ y, (x ≺^[i] y) → ¬M.Val y 0) := by
  simp only [tau, forces_or, forces_boxLe, forces_neg];
  rfl

/-- If `M.Val · 0` is constant, then `x ⊩ tau N`.
- [CZ98, Example 10.58]
-/
lemma forces_tau_of_const (h : (∀ w, M.Val w 0) ∨ (∀ w, ¬M.Val w 0)) : x ⊩ tau N := by
  rw [forces_tau];
  rcases h with h | h;
  · exact Or.inl fun _ _ y _ => h y;
  · exact Or.inr fun _ _ y _ => h y;

lemma not_forces_tau (hN : 1 ≤ N) {y : M.World} (hx : M.Val x 0) (Rxy : x ≺ y)
    (hy : ¬M.Val y 0) : x ⊮ tau N := by
  rw [NotForces, forces_tau];
  rintro (h | h);
  · exact hy <| h 1 hN y <| Frame.iff_relItr_one.mpr Rxy;
  · exact h 0 (Nat.zero_le _) x rfl hx;

/-- If every `y` satisfies `x ≺^[n] y` for some `n ≤ N` and `M.Val · 0` is not constant, then
`x ⊮ tau N`.
- [CZ98, Example 10.58]
-/
lemma not_forces_tau_of_reach (hreach : ∀ y, ∃ n ≤ N, x ≺^[n] y) (h₁ : ∃ w, M.Val w 0)
    (h₂ : ∃ w, ¬M.Val w 0) : x ⊮ tau N := by
  obtain ⟨w₁, hw₁⟩ := h₁;
  obtain ⟨w₂, hw₂⟩ := h₂;
  rw [NotForces, forces_tau];
  rintro (h | h);
  · obtain ⟨n, hn, hx⟩ := hreach w₂;
    exact hw₂ <| h n hn w₂ hx;
  · obtain ⟨n, hn, hx⟩ := hreach w₁;
    exact h n hn w₁ hx hw₁;

lemma forces_deltaUpTo : x ⊩ deltaUpTo N j ↔ ∃ i ≤ j, x ⊩ delta N i := by
  induction j with
  | zero => simp;
  | succ j ih =>
    rw [deltaUpTo_succ, forces_or, ih];
    grind

lemma forces_delta_succ :
    x ⊩ delta N (j + 1) ↔ x ⊩ ◇delta N j ∧ ∀ i ≤ j, x ⊮ delta N i := by
  rw [delta_succ, forces_and, forces_neg, NotForces, forces_deltaUpTo];
  push Not;
  rfl

lemma not_forces_delta_of_lt (hij : i < j) (h : x ⊩ delta N i) : x ⊮ delta N j := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hij;
  rw [show i + j + 1 = (i + j) + 1 by omega, NotForces, forces_delta_succ];
  exact fun h' => h'.2 i (by omega) h

lemma forces_pi_succ : x ⊩ pi N (j + 1) ↔ x ⊩ delta N (j + 1) ∧ ∃ y, x ≺ y ∧ y ⊩ pi N j := by
  simp only [pi, forces_and, forces_dia]

lemma forces_delta_of_forces_pi (h : x ⊩ pi N j) : x ⊩ delta N j := by
  cases j with
  | zero => exact h;
  | succ j => exact (forces_pi_succ.mp h).1

lemma forces_alpha_zero :
    x ⊩ alpha N m 0 ↔ x ⊩ ◇pi N m ∧ x ⊮ ◇◇pi N m := by
  rw [alpha, forces_and, forces_neg]

lemma forces_alpha_succ :
    x ⊩ alpha N m (i + 1) ↔ x ⊩ ◇alpha N m i ∧ x ⊮ ◇◇alpha N m i := by
  rw [alpha, forces_and, forces_neg]

lemma forces_gamma : x ⊩ gamma N m ↔ x ⊩ ◇◇alpha N m 0 ∧ x ⊮ ◇alpha N m 0 := by
  rw [gamma, forces_and, forces_neg]

lemma forces_box₀ {φ : Formula ℕ} :
    x ⊩ box₀ N m φ ↔ ∀ y, x ≺ y → y ⊩ theta N m → y ⊩ φ := by
  rw [box₀, forces_box];
  exact forall₂_congr fun _ _ => forces_imp.trans imp_iff_not_or.symm

lemma forces_löb :
    x ⊩ löb N m ↔ (x ⊩ box₀ N m (box₀ N m (#1) 🡒 #1) → M.Val x 1) := by
  rw [löb, forces_imp];
  exact imp_iff_not_or.symm

lemma forces_gammaLöb :
    x ⊩ gammaLöb N m ↔ (x ⊩ gamma N m → ∀ y, x ≺ y → y ⊩ löb N m) := by
  rw [gammaLöb, forces_imp, forces_box];
  exact imp_iff_not_or.symm

section Const

variable (h : (∀ w, M.Val w 0) ∨ (∀ w, ¬M.Val w 0))
include h

lemma not_forces_delta_of_const : x ⊮ delta N j := by
  induction j generalizing x with
  | zero =>
    rw [delta_zero, NotForces, forces_and, forces_neg];
    exact fun h' => h'.2 <| forces_tau_of_const h;
  | succ j ih =>
    rw [NotForces, forces_delta_succ, forces_dia];
    rintro ⟨⟨y, -, hy⟩, -⟩;
    exact ih hy;

lemma not_forces_pi_of_const : x ⊮ pi N j :=
  fun h' => not_forces_delta_of_const h <| forces_delta_of_forces_pi h'

lemma not_forces_alpha_of_const : x ⊮ alpha N m i := by
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
lemma not_forces_gamma_of_const : x ⊮ gamma N m := by
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

end
