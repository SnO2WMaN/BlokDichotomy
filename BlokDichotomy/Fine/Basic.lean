module

public import BlokDichotomy.Kripke.Basic

/-!
# Fine's logic

The formulas `A`, `B`, `C`, `D`, `E`, `F`, `G`, `H` of Fine's incomplete logic `𝐒𝟒 ⊕ G ⊕ H`, the
`K`-block that climbs one level along the accessibility relation of a transitive model, and the
shift substitution `σ_m` that moves the formulas up by `m` levels.

## References

- [Fin74]
- [Ger75, §4]
- [Lit04, p. 332]
-/

@[expose] public section

namespace Fine

open Formula

def p0 : Formula ℕ := #0
def p1 : Formula ℕ := #1
def q0 : Formula ℕ := #2
def q1 : Formula ℕ := #3
def r0 : Formula ℕ := #4
def r1 : Formula ℕ := #5
def s : Formula ℕ := #6
def t : Formula ℕ := #7

mutual

/-- `B_m`.

- [Fin74] -/
def B : ℕ → Formula ℕ
| 0     => q0
| 1     => q1
| m + 2 => ◇(B (m + 1)) ⋏ ◇(C m) ⋏ ∼◇(C (m + 1))

/-- `C_m`, a mirror image of `B`; the recursive clause here corrects a typo in the original
(which has `∼◇(B (m + 2))` instead).

- [Fin74]
- [Lit04, p. 332] -/
def C : ℕ → Formula ℕ
| 0     => r0
| 1     => r1
| m + 2 => ◇(C (m + 1)) ⋏ ◇(B m) ⋏ ∼◇(B (m + 1))

end

@[simp, grind =] lemma B_zero : B 0 = q0 := by simp [B]
@[simp, grind =] lemma B_one : B 1 = q1 := by simp [B]
@[simp, grind =]
lemma B_add_two (m : ℕ) : B (m + 2) = ◇(B (m + 1)) ⋏ ◇(C m) ⋏ ∼◇(C (m + 1)) := by simp [B]

@[simp, grind =] lemma C_zero : C 0 = r0 := by simp [C]
@[simp, grind =] lemma C_one : C 1 = r1 := by simp [C]
@[simp, grind =]
lemma C_add_two (m : ℕ) : C (m + 2) = ◇(C (m + 1)) ⋏ ◇(B m) ⋏ ∼◇(B (m + 1)) := by simp [C]

/-- `A_m`, with a fourth conjunct `∼◇(C (m + 2))` mirroring the third; the original has only
three conjuncts.

- [Fin74]
- [Lit04, p. 332] -/
def A (m : ℕ) : Formula ℕ := ◇(B (m + 1)) ⋏ ◇(C (m + 1)) ⋏ ∼◇(B (m + 2)) ⋏ ∼◇(C (m + 2))

/-- `D`, with the guard on `p₁` stated in both directions; the original states only one
direction.

- [Fin74]
- [Lit04, p. 332] -/
def D : Formula ℕ :=
  (p0 ⋎ p1) ⋏ □(p0 🡒 (∼p1 ⋏ ◇p1)) ⋏ □(p1 🡒 (∼p0 ⋏ ◇p0)) ⋏ □(∼(p0 ⋎ p1) 🡒 □(∼(p0 ⋎ p1)))

/-- The first conjunct of `K` at level `m`. -/
def K1 (m : ℕ) : Formula ℕ := □(B (m + 1) 🡒 (◇(B m) ⋏ ∼◇(C m)))

/-- The second conjunct of `K` at level `m`. -/
def K2 (m : ℕ) : Formula ℕ := □(C (m + 1) 🡒 (◇(C m) ⋏ ∼◇(B m)))

/-- The third conjunct of `K` at level `m`. -/
def K3 (m : ℕ) : Formula ℕ := □(B m 🡒 ∼◇(B (m + 1)))

/-- The fourth conjunct of `K` at level `m`. -/
def K4 (m : ℕ) : Formula ℕ := □(C m 🡒 ∼◇(C (m + 1)))

/-- `K^m`: the conjunction of `K1`–`K4` at level `m`, indexed by `ℕ` rather than inlined at
level `0` as in the original.

- [Fin74] -/
def K (m : ℕ) : Formula ℕ := K1 m ⋏ K2 m ⋏ K3 m ⋏ K4 m

/-- `E`.

- [Fin74] -/
def E : Formula ℕ := D ⋏ ◇(A 0) ⋏ K 0

/-- `F`.

- [Fin74] -/
def F : Formula ℕ := ◇((p0 ⋎ p1) ⋏ ∼◇(A 0) ⋏ ◇(A 1))

/-- `G`.

- [Fin74] -/
def G : Formula ℕ := E 🡒 F

/-- `H`.

- [Fin74] -/
def H : Formula ℕ := ∼(s ⋏ □(s 🡒 ◇((∼s ⋏ t) ⋏ ◇((∼s ⋏ ∼t) ⋏ ◇s))))

/-- Fine's logic `𝐒𝟒 ⊕ G ⊕ H`.

- [Fin74]
- [Ger75, §4]
- [Lit04, p. 332] -/
abbrev logic : NormalLogic ℕ := (𝐒𝟒 : NormalLogic ℕ) + ({G, H} : FormulaSet ℕ)

/-! ### The `K`-block climbs one level along the accessibility relation -/

open Model.World

variable {κ : Type*} {M : Model κ ℕ} {x y : M.World} {m n : ℕ}

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K1_succ : x ⊩ K1 (m + 1) := by grind [K1]

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K2_succ : x ⊩ K2 (m + 1) := by grind [K2]

section

variable [IsTrans κ M.Rel']

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K3_succ_of_K1 (h1 : x ⊩ K1 m) (Rxy : x ≺ y) : y ⊩ K3 (m + 1) := by
  rw [K3, forces_box];
  rintro z Ryz hz ⟨w, Rzw, hw⟩;
  rw [K1, forces_box] at h1;
  rw [B_add_two, forces_and, forces_and] at hw;
  exact (forces_and.mp <| h1 z (Frame.rel_trans Rxy Ryz) hz).2 <| forces_dia_of_rel hw.2.1 Rzw

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K4_succ_of_K2 (h2 : x ⊩ K2 m) (Rxy : x ≺ y) : y ⊩ K4 (m + 1) := by
  rw [K4, forces_box];
  rintro z Ryz hz ⟨w, Rzw, hw⟩;
  rw [K2, forces_box] at h2;
  rw [C_add_two, forces_and, forces_and] at hw;
  exact (forces_and.mp <| h2 z (Frame.rel_trans Rxy Ryz) hz).2 <| forces_dia_of_rel hw.2.1 Rzw

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K_succ (hK : x ⊩ K m) (Rxy : x ≺ y) : y ⊩ K (m + 1) := by
  simp only [K, forces_and] at hK ⊢;
  exact ⟨forces_K1_succ, forces_K2_succ, forces_K3_succ_of_K1 hK.1 Rxy,
    forces_K4_succ_of_K2 hK.2.1 Rxy⟩

variable [Std.Refl M.Rel']

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_K_succ' (hK : x ⊩ K m) : x ⊩ K (m + 1) := forces_K_succ hK <| Frame.rel_refl x

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
theorem forces_K_mono (hnm : n ≤ m) (hK : x ⊩ K n) : x ⊩ K m := by
  induction m, hnm using Nat.le_induction with
  | base => exact hK
  | succ m _ ih => exact forces_K_succ' ih

end

/-! ### The shift substitution `σ_m` -/

/-- The substitution `σ_m`: `q₀ ↦ B m`, `q₁ ↦ B (m+1)`, `r₀ ↦ C m`, `r₁ ↦ C (m+1)`, identity
elsewhere.

- [Fin74] -/
def shift (m : ℕ) : Substitution ℕ ℕ
| 2 => B m
| 3 => B (m + 1)
| 4 => C m
| 5 => C (m + 1)
| a => #a

@[simp, grind =] lemma shift_p0 (m : ℕ) : p0⟦shift m⟧ = p0 := rfl
@[simp, grind =] lemma shift_p1 (m : ℕ) : p1⟦shift m⟧ = p1 := rfl
@[simp, grind =] lemma shift_q0 (m : ℕ) : q0⟦shift m⟧ = B m := rfl
@[simp, grind =] lemma shift_q1 (m : ℕ) : q1⟦shift m⟧ = B (m + 1) := rfl
@[simp, grind =] lemma shift_r0 (m : ℕ) : r0⟦shift m⟧ = C m := rfl
@[simp, grind =] lemma shift_r1 (m : ℕ) : r1⟦shift m⟧ = C (m + 1) := rfl
@[simp, grind =] lemma shift_s (m : ℕ) : s⟦shift m⟧ = s := rfl
@[simp, grind =] lemma shift_t (m : ℕ) : t⟦shift m⟧ = t := rfl

lemma B_C_subst_shift (m n : ℕ) : (B n)⟦shift m⟧ = B (m + n) ∧ (C n)⟦shift m⟧ = C (m + n) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    obtain ⟨ihB1, ihC1⟩ := B_C_subst_shift m (n + 1);
    obtain ⟨ihB0, ihC0⟩ := B_C_subst_shift m n;
    have : m + (n + 1) = m + n + 1 := by omega;
    have : m + (n + 2) = m + n + 2 := by omega;
    constructor <;> simp_all

lemma B_subst_shift (m n : ℕ) : (B n)⟦shift m⟧ = B (m + n) := (B_C_subst_shift m n).1
lemma C_subst_shift (m n : ℕ) : (C n)⟦shift m⟧ = C (m + n) := (B_C_subst_shift m n).2

@[simp, grind =]
lemma A_subst_shift (m n : ℕ) : (A n)⟦shift m⟧ = A (m + n) := by
  simp [A, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma D_subst_shift (m : ℕ) : D⟦shift m⟧ = D := by
  simp [D]

@[simp, grind =]
lemma K1_subst_shift (m n : ℕ) : (K1 n)⟦shift m⟧ = K1 (m + n) := by
  simp [K1, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K2_subst_shift (m n : ℕ) : (K2 n)⟦shift m⟧ = K2 (m + n) := by
  simp [K2, B_subst_shift, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K3_subst_shift (m n : ℕ) : (K3 n)⟦shift m⟧ = K3 (m + n) := by
  simp [K3, B_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K4_subst_shift (m n : ℕ) : (K4 n)⟦shift m⟧ = K4 (m + n) := by
  simp [K4, C_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma K_subst_shift (m n : ℕ) : (K n)⟦shift m⟧ = K (m + n) := by
  simp [K]

lemma forces_E_iff : x ⊩ E ↔ x ⊩ D ∧ x ⊩ ◇(A 0) ∧ x ⊩ K 0 := by
  simp only [E, forces_and]

/-- Do not unfold `E` directly beyond this point; use this lemma instead. -/
lemma forces_E_subst_shift : x ⊩ E⟦shift m⟧ ↔ x ⊩ D ∧ x ⊩ ◇(A m) ∧ x ⊩ K m := by
  simp [E, forces_and]

lemma forces_F_subst_shift :
    x ⊩ F⟦shift m⟧ ↔ ∃ y, x ≺ y ∧ y ⊩ p0 ⋎ p1 ∧ y ⊩ ∼◇(A m) ∧ y ⊩ ◇(A (m + 1)) := by
  simp [F, forces_dia, forces_and]

end Fine

end
