module

public import BlokDichotomy.Kripke.Basic

/-!
# Fine's logic

The formulas `α`, `β`, `γ`, `δ`, `ε`, `ψ`, `θ`, `χ` of Fine's incomplete logic `𝐒𝟒 ⊕ θ ⊕ χ`, the
`ι`-block that climbs one level along the accessibility relation of a transitive model, and the
shift substitution `σ_m` that moves the formulas up by `m` levels.

## References

- [Fin74a]
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

/-- `β_m`.

- [Fin74a] -/
def β : ℕ → Formula ℕ
| 0     => q0
| 1     => q1
| m + 2 => ◇(β (m + 1)) ⋏ ◇(γ m) ⋏ ∼◇(γ (m + 1))

/-- `γ_m`, a mirror image of `β`; the recursive clause here corrects a typo in the original
(which has `∼◇(β (m + 2))` instead).

- [Fin74a]
- [Lit04, p. 332] -/
def γ : ℕ → Formula ℕ
| 0     => r0
| 1     => r1
| m + 2 => ◇(γ (m + 1)) ⋏ ◇(β m) ⋏ ∼◇(β (m + 1))

end

@[simp, grind =] lemma β_zero : β 0 = q0 := by simp [β]
@[simp, grind =] lemma β_one : β 1 = q1 := by simp [β]
@[simp, grind =]
lemma β_add_two (m : ℕ) : β (m + 2) = ◇(β (m + 1)) ⋏ ◇(γ m) ⋏ ∼◇(γ (m + 1)) := by simp [β]

@[simp, grind =] lemma γ_zero : γ 0 = r0 := by simp [γ]
@[simp, grind =] lemma γ_one : γ 1 = r1 := by simp [γ]
@[simp, grind =]
lemma γ_add_two (m : ℕ) : γ (m + 2) = ◇(γ (m + 1)) ⋏ ◇(β m) ⋏ ∼◇(β (m + 1)) := by simp [γ]

/-- `α_m`, with a fourth conjunct `∼◇(γ (m + 2))` mirroring the third; the original has only
three conjuncts.

- [Fin74a]
- [Lit04, p. 332] -/
def α (m : ℕ) : Formula ℕ := ◇(β (m + 1)) ⋏ ◇(γ (m + 1)) ⋏ ∼◇(β (m + 2)) ⋏ ∼◇(γ (m + 2))

/-- `δ`, with the guard on `p₁` stated in both directions; the original states only one
direction.

- [Fin74a]
- [Lit04, p. 332] -/
def δ : Formula ℕ :=
  (p0 ⋎ p1) ⋏ □(p0 🡒 (∼p1 ⋏ ◇p1)) ⋏ □(p1 🡒 (∼p0 ⋏ ◇p0)) ⋏ □(∼(p0 ⋎ p1) 🡒 □(∼(p0 ⋎ p1)))

/-- The first conjunct of `ι` at level `m`. -/
def ι₁ (m : ℕ) : Formula ℕ := □(β (m + 1) 🡒 (◇(β m) ⋏ ∼◇(γ m)))

/-- The second conjunct of `ι` at level `m`. -/
def ι₂ (m : ℕ) : Formula ℕ := □(γ (m + 1) 🡒 (◇(γ m) ⋏ ∼◇(β m)))

/-- The third conjunct of `ι` at level `m`. -/
def ι₃ (m : ℕ) : Formula ℕ := □(β m 🡒 ∼◇(β (m + 1)))

/-- The fourth conjunct of `ι` at level `m`. -/
def ι₄ (m : ℕ) : Formula ℕ := □(γ m 🡒 ∼◇(γ (m + 1)))

/-- `ι^m`: the conjunction of `ι₁`–`ι₄` at level `m`, indexed by `ℕ` rather than inlined at
level `0` as in the original.

- [Fin74a] -/
def ι (m : ℕ) : Formula ℕ := ι₁ m ⋏ ι₂ m ⋏ ι₃ m ⋏ ι₄ m

/-- `ε`.

- [Fin74a] -/
def ε : Formula ℕ := δ ⋏ ◇(α 0) ⋏ ι 0

/-- `ψ`.

- [Fin74a] -/
def ψ : Formula ℕ := ◇((p0 ⋎ p1) ⋏ ∼◇(α 0) ⋏ ◇(α 1))

/-- `θ`.

- [Fin74a] -/
def θ : Formula ℕ := ε 🡒 ψ

/-- `χ`.

- [Fin74a] -/
def χ : Formula ℕ := ∼(s ⋏ □(s 🡒 ◇((∼s ⋏ t) ⋏ ◇((∼s ⋏ ∼t) ⋏ ◇s))))

/-- Fine's logic `𝐒𝟒 ⊕ θ ⊕ χ`.

- [Fin74a]
- [Ger75, §4]
- [Lit04, p. 332] -/
abbrev logic : NormalLogic ℕ := (𝐒𝟒 : NormalLogic ℕ) + ({θ, χ} : FormulaSet ℕ)

/-! ### The `ι`-block climbs one level along the accessibility relation -/

open Model.World

variable {κ : Type*} {M : Model κ ℕ} {x y : M.World} {m n : ℕ}

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_ι₁_succ : x ⊩ ι₁ (m + 1) := by grind [ι₁]

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_ι₂_succ : x ⊩ ι₂ (m + 1) := by grind [ι₂]

section

variable [IsTrans κ M.Rel']

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_ι₃_succ_of_ι₁ (h1 : x ⊩ ι₁ m) (Rxy : x ≺ y) : y ⊩ ι₃ (m + 1) := by
  rw [ι₃, forces_box];
  rintro z Ryz hz ⟨w, Rzw, hw⟩;
  rw [ι₁, forces_box] at h1;
  rw [β_add_two, forces_and, forces_and] at hw;
  exact (forces_and.mp <| h1 z (Frame.rel_trans Rxy Ryz) hz).2 <| forces_dia_of_rel hw.2.1 Rzw

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_ι₄_succ_of_ι₂ (h2 : x ⊩ ι₂ m) (Rxy : x ≺ y) : y ⊩ ι₄ (m + 1) := by
  rw [ι₄, forces_box];
  rintro z Ryz hz ⟨w, Rzw, hw⟩;
  rw [ι₂, forces_box] at h2;
  rw [γ_add_two, forces_and, forces_and] at hw;
  exact (forces_and.mp <| h2 z (Frame.rel_trans Rxy Ryz) hz).2 <| forces_dia_of_rel hw.2.1 Rzw

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_ι_succ (hK : x ⊩ ι m) (Rxy : x ≺ y) : y ⊩ ι (m + 1) := by
  simp only [ι, forces_and] at hK ⊢;
  exact ⟨forces_ι₁_succ, forces_ι₂_succ, forces_ι₃_succ_of_ι₁ hK.1 Rxy,
    forces_ι₄_succ_of_ι₂ hK.2.1 Rxy⟩

variable [Std.Refl M.Rel']

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
lemma forces_ι_succ' (hK : x ⊩ ι m) : x ⊩ ι (m + 1) := forces_ι_succ hK <| Frame.rel_refl x

/-- - [Ger75, Claim 2]
- [Lit04, Lemma 2.2] -/
theorem forces_ι_mono (hnm : n ≤ m) (hK : x ⊩ ι n) : x ⊩ ι m := by
  induction m, hnm using Nat.le_induction with
  | base => exact hK
  | succ m _ ih => exact forces_ι_succ' ih

end

/-! ### The shift substitution `σ_m` -/

/-- The substitution `σ_m`: `q₀ ↦ β m`, `q₁ ↦ β (m+1)`, `r₀ ↦ γ m`, `r₁ ↦ γ (m+1)`, identity
elsewhere.

- [Fin74a] -/
def shift (m : ℕ) : Substitution ℕ ℕ
| 2 => β m
| 3 => β (m + 1)
| 4 => γ m
| 5 => γ (m + 1)
| a => #a

@[simp, grind =] lemma shift_p0 (m : ℕ) : p0⟦shift m⟧ = p0 := rfl
@[simp, grind =] lemma shift_p1 (m : ℕ) : p1⟦shift m⟧ = p1 := rfl
@[simp, grind =] lemma shift_q0 (m : ℕ) : q0⟦shift m⟧ = β m := rfl
@[simp, grind =] lemma shift_q1 (m : ℕ) : q1⟦shift m⟧ = β (m + 1) := rfl
@[simp, grind =] lemma shift_r0 (m : ℕ) : r0⟦shift m⟧ = γ m := rfl
@[simp, grind =] lemma shift_r1 (m : ℕ) : r1⟦shift m⟧ = γ (m + 1) := rfl
@[simp, grind =] lemma shift_s (m : ℕ) : s⟦shift m⟧ = s := rfl
@[simp, grind =] lemma shift_t (m : ℕ) : t⟦shift m⟧ = t := rfl

lemma β_γ_subst_shift (m n : ℕ) : (β n)⟦shift m⟧ = β (m + n) ∧ (γ n)⟦shift m⟧ = γ (m + n) :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    obtain ⟨ihB1, ihC1⟩ := β_γ_subst_shift m (n + 1);
    obtain ⟨ihB0, ihC0⟩ := β_γ_subst_shift m n;
    have : m + (n + 1) = m + n + 1 := by omega;
    have : m + (n + 2) = m + n + 2 := by omega;
    constructor <;> simp_all

lemma β_subst_shift (m n : ℕ) : (β n)⟦shift m⟧ = β (m + n) := (β_γ_subst_shift m n).1
lemma γ_subst_shift (m n : ℕ) : (γ n)⟦shift m⟧ = γ (m + n) := (β_γ_subst_shift m n).2

@[simp, grind =]
lemma α_subst_shift (m n : ℕ) : (α n)⟦shift m⟧ = α (m + n) := by
  simp [α, β_subst_shift, γ_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma δ_subst_shift (m : ℕ) : δ⟦shift m⟧ = δ := by
  simp [δ]

@[simp, grind =]
lemma ι₁_subst_shift (m n : ℕ) : (ι₁ n)⟦shift m⟧ = ι₁ (m + n) := by
  simp [ι₁, β_subst_shift, γ_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma ι₂_subst_shift (m n : ℕ) : (ι₂ n)⟦shift m⟧ = ι₂ (m + n) := by
  simp [ι₂, β_subst_shift, γ_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma ι₃_subst_shift (m n : ℕ) : (ι₃ n)⟦shift m⟧ = ι₃ (m + n) := by
  simp [ι₃, β_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma ι₄_subst_shift (m n : ℕ) : (ι₄ n)⟦shift m⟧ = ι₄ (m + n) := by
  simp [ι₄, γ_subst_shift, show m + (n + 1) = m + n + 1 from by omega]

@[simp, grind =]
lemma ι_subst_shift (m n : ℕ) : (ι n)⟦shift m⟧ = ι (m + n) := by
  simp [ι]

/-! ### The mirror substitution `tau` -/

/-- The substitution exchanging the atoms underlying `β` (`q0`, `q1`) with those underlying `γ`
(`r0`, `r1`), fixing every other atom. -/
def tau : Substitution ℕ ℕ
| 2 => r0
| 3 => r1
| 4 => q0
| 5 => q1
| a => #a

@[simp, grind =] lemma tau_p0 : p0⟦tau⟧ = p0 := rfl
@[simp, grind =] lemma tau_p1 : p1⟦tau⟧ = p1 := rfl
@[simp, grind =] lemma tau_q0 : q0⟦tau⟧ = r0 := rfl
@[simp, grind =] lemma tau_q1 : q1⟦tau⟧ = r1 := rfl
@[simp, grind =] lemma tau_r0 : r0⟦tau⟧ = q0 := rfl
@[simp, grind =] lemma tau_r1 : r1⟦tau⟧ = q1 := rfl
@[simp, grind =] lemma tau_s : s⟦tau⟧ = s := rfl
@[simp, grind =] lemma tau_t : t⟦tau⟧ = t := rfl

/-- Substituting `tau` exchanges `β` and `γ` at every index. -/
lemma β_γ_subst_tau (n : ℕ) : (β n)⟦tau⟧ = γ n ∧ (γ n)⟦tau⟧ = β n :=
  match n with
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    obtain ⟨ihB1, ihC1⟩ := β_γ_subst_tau (n + 1);
    obtain ⟨ihB0, ihC0⟩ := β_γ_subst_tau n;
    constructor <;> simp_all

@[simp] lemma β_subst_tau (n : ℕ) : (β n)⟦tau⟧ = γ n := (β_γ_subst_tau n).1
@[simp] lemma γ_subst_tau (n : ℕ) : (γ n)⟦tau⟧ = β n := (β_γ_subst_tau n).2

lemma ι_subst_tau (m : ℕ) : (ι m)⟦tau⟧ = ι₂ m ⋏ ι₁ m ⋏ ι₄ m ⋏ ι₃ m := by
  simp [ι, ι₁, ι₂, ι₃, ι₄]

lemma forces_ι_subst_tau_iff {x : M.World} {m : ℕ} : x ⊩ (ι m)⟦tau⟧ ↔ x ⊩ ι m := by
  rw [ι_subst_tau];
  simp only [ι, forces_and];
  tauto

lemma forces_α_iff : x ⊩ α m ↔
    x ⊩ ◇(β (m + 1)) ∧ x ⊩ ◇(γ (m + 1)) ∧ x ⊩ ∼◇(β (m + 2)) ∧ x ⊩ ∼◇(γ (m + 2)) := by
  simp only [α, forces_and]

lemma forces_δ_iff : x ⊩ δ ↔ x ⊩ p0 ⋎ p1 ∧ x ⊩ □(p0 🡒 (∼p1 ⋏ ◇p1)) ∧
    x ⊩ □(p1 🡒 (∼p0 ⋏ ◇p0)) ∧ x ⊩ □(∼(p0 ⋎ p1) 🡒 □(∼(p0 ⋎ p1))) := by
  simp only [δ, forces_and]

lemma forces_ι_iff : x ⊩ ι m ↔ x ⊩ ι₁ m ∧ x ⊩ ι₂ m ∧ x ⊩ ι₃ m ∧ x ⊩ ι₄ m := by
  simp only [ι, forces_and]

lemma forces_ε_iff : x ⊩ ε ↔ x ⊩ δ ∧ x ⊩ ◇(α 0) ∧ x ⊩ ι 0 := by
  simp only [ε, forces_and]

lemma forces_ε_subst_shift : x ⊩ ε⟦shift m⟧ ↔ x ⊩ δ ∧ x ⊩ ◇(α m) ∧ x ⊩ ι m := by
  simp [ε, forces_and]

lemma forces_ψ_subst_shift :
    x ⊩ ψ⟦shift m⟧ ↔ ∃ y, x ≺ y ∧ y ⊩ p0 ⋎ p1 ∧ y ⊩ ∼◇(α m) ∧ y ⊩ ◇(α (m + 1)) := by
  simp [ψ, forces_dia, forces_and]

end Fine

end
