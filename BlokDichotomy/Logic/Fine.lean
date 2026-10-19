module

public import BlokDichotomy.Kripke.Correspondence
public import BlokDichotomy.Kripke.Degree
public import BlokDichotomy.ToMathlib.Order.Monotone.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Fine's Kripke-incomplete logic

The normal extension `𝐒𝟒 ⊕ θ ⊕ χ` of `𝐒𝟒` (`logicS4Fine`), its countermodel `fineModel` forcing
`ε` at `d_0`, and the proof that it is Kripke-incomplete.

## References

- [Fin74a]
- [Lit04, p. 332]
-/

@[expose] public section

/-! ### The formulas -/

namespace Fine

open Formula

mutual

/-- `β_m`, on the atoms `#2` (`q₀`) and `#3` (`q₁`).

- [Fin74a] -/
def β : ℕ → Formula ℕ
| 0     => #2
| 1     => #3
| m + 2 => ◇(β (m + 1)) ⋏ ◇(γ m) ⋏ ∼◇(γ (m + 1))

/-- `γ_m`, the mirror image of `β_m` on `#4` (`r₀`) and `#5` (`r₁`); the original's last
conjunct has a typo.

- [Fin74a]
- [Lit04, p. 332] -/
def γ : ℕ → Formula ℕ
| 0     => #4
| 1     => #5
| m + 2 => ◇(γ (m + 1)) ⋏ ◇(β m) ⋏ ∼◇(β (m + 1))

end

@[simp, grind =] lemma β_zero : β 0 = #2 := by simp [β]
@[simp, grind =] lemma β_one : β 1 = #3 := by simp [β]
@[simp, grind =]
lemma β_add_two (m : ℕ) : β (m + 2) = ◇(β (m + 1)) ⋏ ◇(γ m) ⋏ ∼◇(γ (m + 1)) := by simp [β]

@[simp, grind =] lemma γ_zero : γ 0 = #4 := by simp [γ]
@[simp, grind =] lemma γ_one : γ 1 = #5 := by simp [γ]
@[simp, grind =]
lemma γ_add_two (m : ℕ) : γ (m + 2) = ◇(γ (m + 1)) ⋏ ◇(β m) ⋏ ∼◇(β (m + 1)) := by simp [γ]

/-- `α_m`; the original omits the last conjunct.

- [Fin74a]
- [Lit04, p. 332] -/
def α (m : ℕ) : Formula ℕ := ◇(β (m + 1)) ⋏ ◇(γ (m + 1)) ⋏ ∼◇(β (m + 2)) ⋏ ∼◇(γ (m + 2))

/-- `δ`; the original states the guard on `p₁` in one direction only.

- [Fin74a]
- [Lit04, p. 332] -/
def δ : Formula ℕ :=
  (#0 ⋎ #1) ⋏ □(#0 🡒 (∼#1 ⋏ ◇#1)) ⋏ □(#1 🡒 (∼#0 ⋏ ◇#0)) ⋏ □(∼(#0 ⋎ #1) 🡒 □(∼(#0 ⋎ #1)))

def ι₁ (m : ℕ) : Formula ℕ := □(β (m + 1) 🡒 (◇(β m) ⋏ ∼◇(γ m)))

def ι₂ (m : ℕ) : Formula ℕ := □(γ (m + 1) 🡒 (◇(γ m) ⋏ ∼◇(β m)))

def ι₃ (m : ℕ) : Formula ℕ := □(β m 🡒 ∼◇(β (m + 1)))

def ι₄ (m : ℕ) : Formula ℕ := □(γ m 🡒 ∼◇(γ (m + 1)))

/-- `ι^m`, the conjunction of `ι₁`–`ι₄`.

- [Fin74a] -/
def ι (m : ℕ) : Formula ℕ := ι₁ m ⋏ ι₂ m ⋏ ι₃ m ⋏ ι₄ m

/-- `ε`.

- [Fin74a] -/
def ε : Formula ℕ := δ ⋏ ◇(α 0) ⋏ ι 0

/-- `ψ`.

- [Fin74a] -/
def ψ : Formula ℕ := ◇((#0 ⋎ #1) ⋏ ∼◇(α 0) ⋏ ◇(α 1))

/-- `θ`.

- [Fin74a] -/
def θ : Formula ℕ := ε 🡒 ψ

/-- `χ`.

- [Fin74a] -/
def χ : Formula ℕ := ∼(#6 ⋏ □(#6 🡒 ◇((∼#6 ⋏ #7) ⋏ ◇((∼#6 ⋏ ∼#7) ⋏ ◇#6))))

end Fine

/-! ### The logic -/

open Fine in
/-- Fine's logic `𝐒𝟒 ⊕ θ ⊕ χ`.

- [Fin74a]
- [Ger75, §4]
- [Lit04, p. 332] -/
abbrev logicS4Fine : NormalLogic ℕ := (𝐒𝟒 : NormalLogic ℕ) + ({θ, χ} : FormulaSet ℕ)

namespace Fine

open Formula

/-! ### The `ι`-block climbs one level along the accessibility relation -/

section Climb

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

end Climb

/-! ### The shift substitution `σ_m` -/

/-- The substitution `σ_m`, sending `q₀, q₁, r₀, r₁` to `β m, β (m + 1), γ m, γ (m + 1)`.

- [Fin74a] -/
def shift (m : ℕ) : Substitution ℕ ℕ
| 2 => β m
| 3 => β (m + 1)
| 4 => γ m
| 5 => γ (m + 1)
| a => #a


@[simp, grind =] lemma shift_0 (m : ℕ) : shift m 0 = #0 := rfl
@[simp, grind =] lemma shift_1 (m : ℕ) : shift m 1 = #1 := rfl
@[simp, grind =] lemma shift_2 (m : ℕ) : shift m 2 = β m := rfl
@[simp, grind =] lemma shift_3 (m : ℕ) : shift m 3 = β (m + 1) := rfl
@[simp, grind =] lemma shift_4 (m : ℕ) : shift m 4 = γ m := rfl
@[simp, grind =] lemma shift_5 (m : ℕ) : shift m 5 = γ (m + 1) := rfl
@[simp, grind =] lemma shift_6 (m : ℕ) : shift m 6 = #6 := rfl
@[simp, grind =] lemma shift_7 (m : ℕ) : shift m 7 = #7 := rfl

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
  simp [α, β_subst_shift, γ_subst_shift, show m + (n + 1) = m + n + 1 by omega]

@[simp, grind =]
lemma δ_subst_shift (m : ℕ) : δ⟦shift m⟧ = δ := by
  simp [δ]

@[simp, grind =]
lemma ι₁_subst_shift (m n : ℕ) : (ι₁ n)⟦shift m⟧ = ι₁ (m + n) := by
  simp [ι₁, β_subst_shift, γ_subst_shift, show m + (n + 1) = m + n + 1 by omega]

@[simp, grind =]
lemma ι₂_subst_shift (m n : ℕ) : (ι₂ n)⟦shift m⟧ = ι₂ (m + n) := by
  simp [ι₂, β_subst_shift, γ_subst_shift, show m + (n + 1) = m + n + 1 by omega]

@[simp, grind =]
lemma ι₃_subst_shift (m n : ℕ) : (ι₃ n)⟦shift m⟧ = ι₃ (m + n) := by
  simp [ι₃, β_subst_shift, show m + (n + 1) = m + n + 1 by omega]

@[simp, grind =]
lemma ι₄_subst_shift (m n : ℕ) : (ι₄ n)⟦shift m⟧ = ι₄ (m + n) := by
  simp [ι₄, γ_subst_shift, show m + (n + 1) = m + n + 1 by omega]

@[simp, grind =]
lemma ι_subst_shift (m n : ℕ) : (ι n)⟦shift m⟧ = ι (m + n) := by
  simp [ι]

/-! ### The mirror substitution `tau` -/

/-- The substitution exchanging the atoms of `β` and `γ`. -/
def tau : Substitution ℕ ℕ
| 2 => #4
| 3 => #5
| 4 => #2
| 5 => #3
| a => #a


@[simp, grind =] lemma tau_0 : tau 0 = #0 := rfl
@[simp, grind =] lemma tau_1 : tau 1 = #1 := rfl
@[simp, grind =] lemma tau_2 : tau 2 = #4 := rfl
@[simp, grind =] lemma tau_3 : tau 3 = #5 := rfl
@[simp, grind =] lemma tau_4 : tau 4 = #2 := rfl
@[simp, grind =] lemma tau_5 : tau 5 = #3 := rfl
@[simp, grind =] lemma tau_6 : tau 6 = #6 := rfl
@[simp, grind =] lemma tau_7 : tau 7 = #7 := rfl

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

/-! ### Unfolding the forcing of the formulas -/

section Forces

open Model.World

variable {κ : Type*} {M : Model κ ℕ} {x : M.World} {m : ℕ}

lemma forces_ι_subst_tau_iff : x ⊩ (ι m)⟦tau⟧ ↔ x ⊩ ι m := by
  rw [ι_subst_tau];
  simp only [ι, forces_and];
  tauto

lemma forces_α_iff : x ⊩ α m ↔
    x ⊩ ◇(β (m + 1)) ∧ x ⊩ ◇(γ (m + 1)) ∧ x ⊩ ∼◇(β (m + 2)) ∧ x ⊩ ∼◇(γ (m + 2)) := by
  simp only [α, forces_and]

lemma forces_δ_iff : x ⊩ δ ↔ x ⊩ #0 ⋎ #1 ∧ x ⊩ □(#0 🡒 (∼#1 ⋏ ◇#1)) ∧
    x ⊩ □(#1 🡒 (∼#0 ⋏ ◇#0)) ∧ x ⊩ □(∼(#0 ⋎ #1) 🡒 □(∼(#0 ⋎ #1))) := by
  simp only [δ, forces_and]

lemma forces_ι_iff : x ⊩ ι m ↔ x ⊩ ι₁ m ∧ x ⊩ ι₂ m ∧ x ⊩ ι₃ m ∧ x ⊩ ι₄ m := by
  simp only [ι, forces_and]

lemma forces_ε_iff : x ⊩ ε ↔ x ⊩ δ ∧ x ⊩ ◇(α 0) ∧ x ⊩ ι 0 := by
  simp only [ε, forces_and]

lemma forces_ε_subst_shift : x ⊩ ε⟦shift m⟧ ↔ x ⊩ δ ∧ x ⊩ ◇(α m) ∧ x ⊩ ι m := by
  simp [ε, forces_and]

lemma forces_ψ_subst_shift :
    x ⊩ ψ⟦shift m⟧ ↔ ∃ y, x ≺ y ∧ y ⊩ #0 ⋎ #1 ∧ y ⊩ ∼◇(α m) ∧ y ⊩ ◇(α (m + 1)) := by
  simp [ψ, forces_dia, forces_and]

end Forces

end Fine

/-! ### The countermodel -/

section Countermodel

/-- Fine's frame, on the points `(0, m) = a_m`, `(1, m) = b_m`, `(2, m) = c_m` and
`(3, m) = d_m`.

- [Fin74a, p. 25] -/
abbrev fineFrame : Frame (Fin 4 × ℕ) where
  Rel'
  | (1, m), (1, k) => k ≤ m
  | (1, m), (2, k) => k + 2 ≤ m
  | (2, m), (2, k) => k ≤ m
  | (2, m), (1, k) => k + 2 ≤ m
  | (0, m), (0, k) => k = m
  | (0, m), (1, k) => k ≤ m + 1
  | (0, m), (2, k) => k ≤ m + 1
  | (3, n), (3, k) => n ≤ k
  | (3, n), (0, m) => n ≤ m
  | (3, _), (1, _) => True
  | (3, _), (2, _) => True
  | _, _ => False

namespace fineFrame

/-- The four families of points of Fine's model.

- [Fin74a, p. 25] -/
@[simp, match_pattern] abbrev a (m : ℕ) : fineFrame.World := (0, m)
@[simp, match_pattern] abbrev b (m : ℕ) : fineFrame.World := (1, m)
@[simp, match_pattern] abbrev c (m : ℕ) : fineFrame.World := (2, m)
@[simp, match_pattern] abbrev d (m : ℕ) : fineFrame.World := (3, m)

/-- Case analysis on the points of Fine's model. -/
@[elab_as_elim]
theorem casesOn {P : fineFrame.World → Prop} (x : fineFrame.World) (a : ∀ m, P (fineFrame.a m))
    (b : ∀ m, P (fineFrame.b m)) (c : ∀ m, P (fineFrame.c m)) (d : ∀ m, P (fineFrame.d m)) :
    P x := by
  obtain ⟨⟨_ | _ | _ | _ | i, hi⟩, m⟩ := x
  · exact a m
  · exact b m
  · exact c m
  · exact d m
  · omega

end fineFrame

/-! ### The accessibility relation -/

namespace fineFrame

open Fine

section Rel

variable {x y z : fineFrame.World} {m k n : ℕ}

@[simp] lemma not_rel_iff : x ⊀ y ↔ ¬ x ≺ y := Iff.rfl

@[simp] lemma rel_a_a : (a m ≺ a k) ↔ k = m := Iff.rfl
@[simp] lemma rel_a_b : (a m ≺ b k) ↔ k ≤ m + 1 := Iff.rfl
@[simp] lemma rel_a_c : (a m ≺ c k) ↔ k ≤ m + 1 := Iff.rfl
@[simp] lemma rel_a_d : a m ⊀ d k := id
@[simp] lemma rel_b_a : b m ⊀ a k := id
@[simp] lemma rel_b_b : (b m ≺ b k) ↔ k ≤ m := Iff.rfl
@[simp] lemma rel_b_c : (b m ≺ c k) ↔ k + 2 ≤ m := Iff.rfl
@[simp] lemma rel_b_d : b m ⊀ d k := id
@[simp] lemma rel_c_a : c m ⊀ a k := id
@[simp] lemma rel_c_b : (c m ≺ b k) ↔ k + 2 ≤ m := Iff.rfl
@[simp] lemma rel_c_c : (c m ≺ c k) ↔ k ≤ m := Iff.rfl
@[simp] lemma rel_c_d : c m ⊀ d k := id
@[simp] lemma rel_d_a : (d n ≺ a m) ↔ n ≤ m := Iff.rfl
@[simp] lemma rel_d_b : d n ≺ b k := trivial
@[simp] lemma rel_d_c : d n ≺ c k := trivial
@[simp] lemma rel_d_d : (d n ≺ d k) ↔ n ≤ k := Iff.rfl

instance : Std.Refl fineFrame.Rel' where
  refl w := by
    cases w using casesOn <;> simp

instance : IsTrans fineFrame.World fineFrame.Rel' where
  trans x y z hxy hyz := by
    cases x using casesOn <;> cases y using casesOn <;> cases z using casesOn <;> simp_all <;> omega

lemma rel_antisymm (hxy : x ≺ y) (hyx : y ≺ x) : x = y := by
  cases x using casesOn <;> cases y using casesOn <;> simp_all <;> omega

end Rel

/-- The cone above a point other than a `d`-point is finite. -/
lemma cone_finite {w : fineFrame.World} (hw : ∀ k, w ≠ d k) : {z | w ≺ z}.Finite := by
  obtain ⟨m, hm⟩ : ∃ m, ∀ z, w ≺ z → ∃ k ≤ m, z = a k ∨ z = b k ∨ z = c k := by
    cases w using casesOn with
    | d k => exact absurd rfl (hw k)
    | a m =>
      use m + 1
      intro z hz
      cases z using casesOn <;> simp_all
    | b m =>
      use m + 1
      intro z hz
      cases z using casesOn <;> simp_all <;> omega
    | c m =>
      use m + 1
      intro z hz
      cases z using casesOn <;> simp_all <;> omega
  apply ((Finset.range (m + 1)).image a ∪ (Finset.range (m + 1)).image b ∪
    (Finset.range (m + 1)).image c).finite_toSet.subset
  intro z hz
  obtain ⟨k, hk, rfl | rfl | rfl⟩ := hm z hz <;> simp [hk]

/-- An infinite strict chain consists of `d`-points. -/
lemma strict_chain_all_d {u : ℕ → fineFrame.World} (hR : ∀ m, u m ≺ u (m + 1))
    (hs : ∀ m, u (m + 1) ⊀ u m) (i : ℕ) : ∃ k, u i = d k := by
  have hinj : Function.Injective u := injective_of_forall_rel_succ hR hs
  have hchain : ∀ n, u i ≺ u (i + n) := by
    intro n
    induction n with
    | zero => exact Frame.rel_refl _
    | succ n ih => exact Frame.rel_trans ih (hR (i + n))
  have hinj' : Function.Injective fun n => u (i + n) := by
    intro a b hab
    have := hinj hab
    omega
  have hinf : {z | u i ≺ z}.Infinite := Set.infinite_of_injective_forall_mem hinj' hchain
  by_contra h
  push Not at h
  exact (cone_finite h).not_infinite hinf

/-- The involution exchanging the `b`- and `c`-families. -/
def swap : fineFrame.World → fineFrame.World
| a m => a m
| b m => c m
| c m => b m
| d m => d m

@[simp] lemma swap_a {m : ℕ} : swap (a m) = a m := rfl
@[simp] lemma swap_b {m : ℕ} : swap (b m) = c m := rfl
@[simp] lemma swap_c {m : ℕ} : swap (c m) = b m := rfl
@[simp] lemma swap_d {m : ℕ} : swap (d m) = d m := rfl

lemma swap_involutive : Function.Involutive swap := by
  intro x
  cases x using casesOn <;> rfl

@[simp] lemma swap_swap (w : fineFrame.World) : swap (swap w) = w := swap_involutive w

lemma rel_swap {x y : fineFrame.World} : (swap x ≺ swap y) ↔ x ≺ y := by
  cases x using casesOn <;> cases y using casesOn <;> simp

end fineFrame

namespace fineModel

open fineFrame

/-- The valuation of Fine's model: `q₀ = {b₀}`, `q₁ = {b₁}`, `r₀ = {c₀}`, `r₁ = {c₁}`,
`p₀ = {d_{2k}}`, `p₁ = {d_{2k+1}}`, and `∅` for the other atoms.

- [Fin74a, p. 25] -/
@[grind =]
def val : fineFrame.World → ℕ → Prop
| b 0, 2 => True
| b 1, 3 => True
| c 0, 4 => True
| c 1, 5 => True
| d n, 0 => n % 2 = 0
| d n, 1 => n % 2 = 1
| _, _ => False

@[simp] lemma val_a {m i : ℕ} : ¬ val (a m) i := by simp [val];
@[simp] lemma val_b_iff {m i : ℕ} : val (b m) i ↔ (m = 0 ∧ i = 2) ∨ (m = 1 ∧ i = 3) := by
  rcases m with _ | _ | m <;> rcases i with _ | _ | _ | _ | i <;> simp [val];
@[simp] lemma val_c_iff {m i : ℕ} : val (c m) i ↔ (m = 0 ∧ i = 4) ∨ (m = 1 ∧ i = 5) := by
  rcases m with _ | _ | m <;> rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [val];
@[simp] lemma val_d_iff {n i : ℕ} : val (d n) i ↔ (i = 0 ∧ n % 2 = 0) ∨ (i = 1 ∧ n % 2 = 1) := by
  rcases i with _ | _ | i <;> simp [val];

end fineModel

/-- Fine's model: `fineFrame` with the valuation `fineModel.val`.

- [Fin74a, p. 25] -/
abbrev fineModel : Model fineFrame.World ℕ := ⟨fineFrame, fineModel.val⟩

namespace fineFrame

open Fine fineFrame

variable {V : fineFrame.World → ℕ → Prop} {x y : fineFrame.World}

@[simp] lemma forces_atom {n : ℕ} : x ⊩[⟨fineFrame, V⟩] #n ↔ V x n := Iff.rfl

end fineFrame

namespace fineModel

open Fine fineFrame

variable {x : fineFrame.World}

@[simp high] lemma forces_atom_0_iff : x ⊩[fineModel] #0 ↔ ∃ k, x = d k ∧ k % 2 = 0 := by
  cases x using casesOn <;> simp
@[simp high] lemma forces_atom_1_iff : x ⊩[fineModel] #1 ↔ ∃ k, x = d k ∧ k % 2 = 1 := by
  cases x using casesOn <;> simp
@[simp high] lemma forces_atom_2_iff : x ⊩[fineModel] #2 ↔ x = b 0 := by
  cases x using casesOn <;> simp
@[simp high] lemma forces_atom_3_iff : x ⊩[fineModel] #3 ↔ x = b 1 := by
  cases x using casesOn <;> simp
@[simp high] lemma forces_atom_4_iff : x ⊩[fineModel] #4 ↔ x = c 0 := by
  cases x using casesOn <;> simp
@[simp high] lemma forces_atom_5_iff : x ⊩[fineModel] #5 ↔ x = c 1 := by
  cases x using casesOn <;> simp

end fineModel

/-! ### Forcing in the countermodel -/

namespace fineModel

open Fine fineFrame Model.World

/-- `β_2` is forced exactly at `b_2`. -/
lemma forces_β₂_iff (w : fineFrame.World) : w ⊩[fineModel] β 2 ↔ w = b 2 := by
  rw [β_add_two, forces_and, forces_and, forces_neg];
  simp only [Nat.zero_add, β_one, γ_zero, γ_one, forces_dia, forces_atom_3_iff, forces_atom_4_iff,
    forces_atom_5_iff, NotForces, exists_eq_right];
  cases w using casesOn <;> simp <;> omega

/-- `γ_2` is forced exactly at `c_2`. -/
lemma forces_γ₂_iff (w : fineFrame.World) : w ⊩[fineModel] γ 2 ↔ w = c 2 := by
  rw [γ_add_two, forces_and, forces_and, forces_neg];
  simp only [Nat.zero_add, β_zero, β_one, γ_one, forces_dia, forces_atom_2_iff, forces_atom_3_iff,
    forces_atom_5_iff, NotForces, exists_eq_right];
  cases w using casesOn <;> simp <;> omega

/-- `d_0` forces `δ`. -/
lemma forces_δ_d0 : d 0 ⊩[fineModel] δ := by
  rw [δ, forces_and, forces_and, forces_and, forces_box, forces_box, forces_box];
  and_intros;
  · rw [forces_or];
    simp;
  · rintro w -;
    rw [forces_imp, forces_and, forces_neg, forces_dia];
    cases w using casesOn with
    | d k =>
      simp only [NotForces, forces_atom_0_iff, forces_atom_1_iff,
        ↓existsAndEq, rel_d_d, true_and, d, Prod.mk.injEq];
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk;
      · exact Or.inr ⟨by omega, k + 1, by omega, by omega⟩;
      · exact Or.inl (by omega)
    | _ => simp [NotForces]
  · rintro w -;
    rw [forces_imp, forces_and, forces_neg, forces_dia];
    cases w using casesOn with
    | d k =>
      simp only [NotForces, forces_atom_0_iff, forces_atom_1_iff,
        ↓existsAndEq, rel_d_d, true_and, d, Prod.mk.injEq];
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk;
      · exact Or.inl (by omega);
      · exact Or.inr ⟨by omega, k + 1, by omega, by omega⟩
    | _ => simp [NotForces]
  · rintro w -
    rw [forces_imp, forces_box]
    cases w using casesOn with
    | d k =>
      left
      rw [not_forces_neg, forces_or]
      simp
      omega
    | _ =>
      right
      intro z hz
      rw [forces_neg, not_forces_or]
      cases z using casesOn <;> simp [NotForces] at hz ⊢

/-- `α_0` is forced at `a_0`. -/
lemma forces_α₀_a0 : a 0 ⊩[fineModel] α 0 := by
  rw [α, forces_and, forces_and, forces_and, forces_neg, forces_neg];
  simp only [Nat.zero_add, β_one, γ_one, forces_dia, forces_atom_3_iff, forces_atom_5_iff,
    forces_β₂_iff, forces_γ₂_iff, NotForces, exists_eq_right];
  simp

/-- `◇(α_0)` is forced at `d_0`. -/
lemma forces_dia_α₀_d0 : d 0 ⊩[fineModel] ◇(α 0) :=
  forces_dia.mpr ⟨a 0, by simp, forces_α₀_a0⟩

/-- `d_0` forces `ι 0`. -/
lemma forces_ι₀_d0 : d 0 ⊩[fineModel] ι 0 := by
  rw [ι, forces_and, forces_and, forces_and];
  and_intros;
  · rw [ι₁, forces_box];
    rintro y - hy;
    simp only [Nat.zero_add, β_one, forces_atom_3_iff] at hy;
    subst hy;
    rw [forces_and, forces_neg];
    simp [forces_dia, NotForces];
  · rw [ι₂, forces_box];
    rintro y - hy;
    simp only [Nat.zero_add, γ_one, forces_atom_5_iff] at hy;
    subst hy;
    rw [forces_and, forces_neg];
    simp [forces_dia, NotForces];
  · rw [ι₃, forces_box];
    rintro y - hy;
    simp only [β_zero, forces_atom_2_iff] at hy;
    subst hy;
    rw [forces_neg];
    simp [forces_dia, NotForces];
  · rw [ι₄, forces_box];
    rintro y - hy;
    simp only [γ_zero, forces_atom_4_iff] at hy;
    subst hy;
    rw [forces_neg];
    simp [forces_dia, NotForces]

/-- `d_0` forces `ε`. -/
lemma forces_ε_d0 : d 0 ⊩[fineModel] ε :=
  forces_ε_iff.mpr ⟨forces_δ_d0, forces_dia_α₀_d0, forces_ι₀_d0⟩

/-! ### `χ` is strongly valid in Fine's model -/

/-- Past some threshold, the truth of `A` at `d_i` depends only on the parity of `i`.

- [Fin74a, p.\ 28] -/
lemma d_eventually_period_two (A : Formula ℕ) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → i % 2 = j % 2 →
      ((d i ⊩[fineModel] A) ↔ (d j ⊩[fineModel] A)) := by
  induction A with
  | atom a =>
    use 0;
    intro i j _ _ hij;
    rcases a with _ | _ | a <;> simp [hij]
  | falsum =>
    use 0;
    intro i j _ _ _;
    simp [Forces]
  | imp B C ihB ihC =>
    obtain ⟨NA, hNA⟩ := ihB;
    obtain ⟨NB, hNB⟩ := ihC;
    use max NA NB;
    intro i j hi hj hij;
    simp only [forces_imp, NotForces, hNA i j (by omega) (by omega) hij,
      hNB i j (by omega) (by omega) hij]
  | dia B ih =>
    have hdia : ∀ i : ℕ, (d i ⊩[fineModel] ◇B) ↔
        (∃ k, i ≤ k ∧ (d k ⊩[fineModel] B)) ∨
        (∃ m, i ≤ m ∧ (a m ⊩[fineModel] B)) ∨
        (∃ k, (b k ⊩[fineModel] B)) ∨ (∃ k, (c k ⊩[fineModel] B)) := by
      intro i;
      rw [forces_dia];
      constructor;
      · rintro ⟨y, hy, hyA⟩;
        cases y using casesOn with
        | d k => exact Or.inl ⟨k, hy, hyA⟩;
        | a m => exact Or.inr <| Or.inl ⟨m, hy, hyA⟩;
        | b k => exact Or.inr <| Or.inr <| Or.inl ⟨k, hyA⟩;
        | c k => exact Or.inr <| Or.inr <| Or.inr ⟨k, hyA⟩;
      · rintro (⟨k, hk, hA⟩ | ⟨m, hm, hA⟩ | ⟨k, hA⟩ | ⟨k, hA⟩);
        · exact ⟨d k, hk, hA⟩;
        · exact ⟨a m, hm, hA⟩;
        · exact ⟨b k, trivial, hA⟩;
        · exact ⟨c k, trivial, hA⟩;
    obtain ⟨N1, hN1⟩ := exists_ge_eventually_const (fun k => d k ⊩[fineModel] B);
    obtain ⟨N2, hN2⟩ := exists_ge_eventually_const (fun m => a m ⊩[fineModel] B);
    use max N1 N2;
    intro i j hi hj _;
    rw [hdia i, hdia j, hN1 i j (by omega) (by omega), hN2 i j (by omega) (by omega)]

/-- The three pairwise incompatible phases of a refutation of `χ⟦σ⟧`. -/
def phase (σ : Formula.Substitution ℕ ℕ) (r : ℕ) : Formula ℕ :=
  match r with
  | 0 => #6⟦σ⟧
  | 1 => ∼(#6⟦σ⟧) ⋏ #7⟦σ⟧
  | _ => ∼(#6⟦σ⟧) ⋏ ∼(#7⟦σ⟧)

@[simp, grind =]
lemma phase_zero (σ : Formula.Substitution ℕ ℕ) : phase σ 0 = #6⟦σ⟧ := rfl
@[simp, grind =] lemma phase_one (σ : Formula.Substitution ℕ ℕ) :
    phase σ 1 = ∼(#6⟦σ⟧) ⋏ #7⟦σ⟧ := rfl
@[simp, grind =] lemma phase_add_two (σ : Formula.Substitution ℕ ℕ) (r : ℕ) :
    phase σ (r + 2) = ∼(#6⟦σ⟧) ⋏ ∼(#7⟦σ⟧) := rfl

private lemma d_eventually_period_two_phase (σ : Formula.Substitution ℕ ℕ) :
    ∃ N : ℕ, ∀ r < 3, ∀ i j : ℕ, N ≤ i → N ≤ j → i % 2 = j % 2 →
      (d i ⊩[fineModel] phase σ r ↔ d j ⊩[fineModel] phase σ r) := by
  obtain ⟨N0, h0⟩ := d_eventually_period_two (phase σ 0);
  obtain ⟨N1, h1⟩ := d_eventually_period_two (phase σ 1);
  obtain ⟨N2, h2⟩ := d_eventually_period_two (phase σ 2);
  use max N0 (max N1 N2);
  intro r hr i j hi hj hij;
  rcases r with _ | _ | _ | r;
  · exact h0 i j (by omega) (by omega) hij;
  · exact h1 i j (by omega) (by omega) hij;
  · exact h2 i j (by omega) (by omega) hij;
  · omega

private lemma phase_incompatible {σ : Formula.Substitution ℕ ℕ} {w : fineFrame.World} {i j : ℕ}
    (hi3 : i < 3) (hj3 : j < 3) (hij : i ≠ j)
    (hi : w ⊩[fineModel] phase σ i) (hj : w ⊩[fineModel] phase σ j) : False := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega;
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega;
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> simp_all <;> grind

private def Y (σ : Formula.Substitution ℕ ℕ) : ℕ → Formula ℕ
| 0 => phase σ 0
| 1 => phase σ 1 ⋏ ◇(phase σ 2 ⋏ ◇(phase σ 0))
| _ => phase σ 2 ⋏ ◇(phase σ 0)

private lemma Y_imp_phase {σ : Formula.Substitution ℕ ℕ} {w : fineFrame.World} {r : ℕ}
    (h : w ⊩[fineModel] Y σ r) : w ⊩[fineModel] phase σ r := by
  rcases r with _ | _ | r;
  · exact h;
  · exact (forces_and.mp h).1;
  · exact (forces_and.mp h).1

private lemma Y_step {σ : Formula.Substitution ℕ ℕ} {x w : fineFrame.World}
    (hbox : x ⊩[fineModel] □(phase σ 0 🡒 ◇(Y σ 1))) (m : ℕ)
    (hxw : x ≺ w) (hw : w ⊩[fineModel] Y σ (m % 3)) :
    ∃ v, w ≺ v ∧ v ⊀ w ∧ x ≺ v ∧ v ⊩[fineModel] Y σ ((m + 1) % 3) := by
  obtain ⟨v, hwv, hv⟩ : ∃ v, w ≺ v ∧ v ⊩[fineModel] Y σ ((m + 1) % 3) := by
    have h3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega;
    rcases h3 with h | h | h;
    · rw [h] at hw;
      rw [show (m + 1) % 3 = 1 by omega];
      exact forces_dia.mp (forces_box.mp hbox w hxw hw);
    · rw [h] at hw;
      rw [show (m + 1) % 3 = 2 by omega];
      exact forces_dia.mp (forces_and.mp hw).2;
    · rw [h] at hw;
      rw [show (m + 1) % 3 = 0 by omega];
      exact forces_dia.mp (forces_and.mp hw).2;
  use v, hwv;
  and_intros;
  · by_contra hvw;
    obtain rfl := rel_antisymm hvw hwv;
    exact phase_incompatible (Nat.mod_lt m (by omega)) (Nat.mod_lt (m + 1) (by omega))
      (by omega) (Y_imp_phase hw) (Y_imp_phase hv);
  · exact Frame.rel_trans hxw hwv;
  · exact hv

/-- A refutation of `χ` yields an infinite strict chain cycling through the three phases.

- [Fin74a, p.\ 28] -/
lemma exists_phase_chain (h : ∃ σ x, x ⊮[fineModel] χ⟦σ⟧) :
    ∃ (σ : Formula.Substitution ℕ ℕ) (u : ℕ → fineFrame.World),
      (∀ m, u m ≺ u (m + 1)) ∧ (∀ m, u (m + 1) ⊀ u m) ∧
      ∀ m, u m ⊩[fineModel] phase σ (m % 3) := by
  obtain ⟨σ, x, hx⟩ := h;
  obtain ⟨hxs, hbox⟩ := forces_and.mp (not_forces_neg.mp hx);
  have h₀ : x ⊩[fineModel] Y σ (0 % 3) := by
    rw [Nat.zero_mod];
    exact hxs;
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun w v => w ≺ v ∧ v ⊀ w)
    (P := fun m w => x ≺ w ∧ w ⊩[fineModel] Y σ (m % 3)) ⟨Frame.rel_refl x, h₀⟩ <| by
      intro m w hw;
      obtain ⟨v, hwv, hvw, hxv, hv⟩ := Y_step hbox m hw.1 hw.2;
      exact ⟨v, ⟨hwv, hvw⟩, hxv, hv⟩;
  use σ, u;
  and_intros;
  · intro m;
    exact (hu m).2.1;
  · intro m;
    exact (hu m).2.2;
  · intro m;
    exact Y_imp_phase (hu m).1.2

/-- `χ` is strongly valid in Fine's model.

- [Fin74a, p.\ 28] -/
theorem χ_mem_logic : χ ∈ fineModel.logic := by
  apply Model.mem_logic.mpr;
  intro σ x;
  by_contra hx;
  obtain ⟨σ, u, hR, hs, hphase⟩ := exists_phase_chain ⟨σ, x, hx⟩;
  choose k hk using fun i => strict_chain_all_d hR hs i;
  have hkmono : StrictMono k := by
    apply strictMono_nat_of_lt_succ;
    intro m;
    have h₁ := hR m;
    have h₂ := hs m;
    rw [hk m, hk (m + 1)] at h₁ h₂;
    simp at h₁ h₂;
    omega;
  obtain ⟨N, hN⟩ := d_eventually_period_two_phase σ;
  have hphase' : ∀ i, d (k i) ⊩[fineModel] phase σ (i % 3) := by
    intro i;
    rw [← hk i];
    exact hphase i;
  have clash : ∀ i j, i % 3 ≠ j % 3 → N ≤ i → N ≤ j → k i % 2 = k j % 2 → False := by
    intro i j hij hi hj hpar;
    apply phase_incompatible (Nat.mod_lt i (by omega)) (Nat.mod_lt j (by omega)) hij _
      (hphase' j);
    exact (hN _ (Nat.mod_lt i (by omega)) _ _ (hi.trans hkmono.le_apply)
      (hj.trans hkmono.le_apply) hpar).mp (hphase' i);
  have h₃ : k (3 * N) % 2 = k (3 * N + 1) % 2 ∨ k (3 * N) % 2 = k (3 * N + 2) % 2 ∨
      k (3 * N + 1) % 2 = k (3 * N + 2) % 2 := by omega;
  rcases h₃ with h | h | h;
  · exact clash _ _ (by omega) (by omega) (by omega) h;
  · exact clash _ _ (by omega) (by omega) (by omega) h;
  · exact clash _ _ (by omega) (by omega) (by omega) h

end fineModel

namespace fineFrame

open Fine Model.World

variable {V : fineFrame.World → ℕ → Prop} {x : fineFrame.World} {A : Formula ℕ}

/-! ### The mirror valuation -/

lemma forces_swap_iff :
    x ⊩[⟨fineFrame, V⟩] A ↔ swap x ⊩[⟨fineFrame, V ∘ swap⟩] A := by
  induction A generalizing x with
  | atom a => simp [Function.comp]
  | falsum => simp [Model.World.Forces]
  | imp B C ihB ihC => simp [Model.World.Forces, ihB, ihC]
  | dia B ih =>
    simp only [Model.World.Forces];
    constructor;
    · rintro ⟨y, hxy, hy⟩;
      exact ⟨swap y, rel_swap.mpr hxy, ih.mp hy⟩;
    · rintro ⟨y, hxy, hy⟩;
      use swap y;
      and_intros;
      · exact rel_swap.mp (by simpa using hxy);
      · exact ih.mpr (by simpa using hy)

/-- The valuation of `V` seen through `swap` and `tau`. -/
def mirrorVal (V : fineFrame.World → ℕ → Prop) : fineFrame.World → ℕ → Prop :=
  fun w a => swap w ⊩[⟨fineFrame, V⟩] tau a

lemma forces_mirror :
    x ⊩[⟨fineFrame, mirrorVal V⟩] A ↔ swap x ⊩[⟨fineFrame, V⟩] A⟦tau⟧ := by
  rw [forces_subst, forces_swap_iff (x := swap x), swap_swap];
  exact Iff.rfl

end fineFrame

namespace fineFrame

open Fine Model.World

section Extraction

variable {V : fineFrame.World → ℕ → Prop} {w x y : fineFrame.World} {A B : Formula ℕ}

/-! ### The V-shape extracted from `w ⊩ ε` -/

/-- The `V`-shape below a point forcing `ε`. -/
lemma exists_V_shape (hE : w ⊩[⟨fineFrame, V⟩] ε) :
    ∃ t u₀ u₁ v₀ v₁ : fineFrame.World,
      w ≺ t ∧ t ⊩[⟨fineFrame, V⟩] α 0 ∧
      t ≺ u₁ ∧ u₁ ≺ u₀ ∧
      t ≺ v₁ ∧ v₁ ≺ v₀ ∧
      u₁ ⊩[⟨fineFrame, V⟩] β 1 ∧ u₀ ⊩[⟨fineFrame, V⟩] β 0 ∧
      v₁ ⊩[⟨fineFrame, V⟩] γ 1 ∧ v₀ ⊩[⟨fineFrame, V⟩] γ 0 ∧
      u₀ ⊀ u₁ ∧ v₀ ⊀ v₁ ∧
      u₁ ⊀ v₀ ∧ v₁ ⊀ u₀ := by
  obtain ⟨-, hA0, hK⟩ := forces_ε_iff.mp hE;
  obtain ⟨t, hwt, htA0⟩ := forces_dia.mp hA0;
  obtain ⟨htB1, htC1, -, -⟩ := forces_α_iff.mp htA0;
  obtain ⟨hι₁, hι₂, hι₃, hι₄⟩ := forces_ι_iff.mp hK;
  obtain ⟨u₁, htu1, hu1B1⟩ := forces_dia.mp htB1;
  obtain ⟨v₁, htv1, hv1C1⟩ := forces_dia.mp htC1;
  obtain ⟨hu1B0, hu1nC0⟩ := forces_and.mp (forces_box.mp hι₁ u₁ (Frame.rel_trans hwt htu1) hu1B1);
  obtain ⟨u₀, hu1u0, hu0B0⟩ := forces_dia.mp hu1B0;
  obtain ⟨hv1C0, hv1nB0⟩ := forces_and.mp (forces_box.mp hι₂ v₁ (Frame.rel_trans hwt htv1) hv1C1);
  obtain ⟨v₀, hv1v0, hv0C0⟩ := forces_dia.mp hv1C0;
  have hu0nB1 := forces_box.mp hι₃ u₀ (Frame.rel_trans (Frame.rel_trans hwt htu1) hu1u0) hu0B0;
  have hv0nC1 := forces_box.mp hι₄ v₀ (Frame.rel_trans (Frame.rel_trans hwt htv1) hv1v0) hv0C0;
  use t, u₀, u₁, v₀, v₁;
  and_intros <;> try assumption;
  · by_contra h;
    exact forces_neg.mp hu0nB1 (forces_dia.mpr ⟨u₁, h, hu1B1⟩);
  · by_contra h;
    exact forces_neg.mp hv0nC1 (forces_dia.mpr ⟨v₁, h, hv1C1⟩);
  · by_contra h;
    exact forces_neg.mp hu1nC0 (forces_dia.mpr ⟨v₀, h, hv0C0⟩);
  · by_contra h;
    exact forces_neg.mp hv1nB0 (forces_dia.mpr ⟨u₀, h, hu0B0⟩)

private lemma false_of_neg_dia (hn : x ⊩[⟨fineFrame, V⟩] ∼◇A)
    (hxy : x ≺ y) (hy : y ⊩[⟨fineFrame, V⟩] A) : False :=
  forces_neg.mp hn (forces_dia.mpr ⟨y, hxy, hy⟩)

/-! ### Confinement of forced points to `d`-points -/

private lemma exists_rel_of_guard
    (hg : y ⊩[⟨fineFrame, V⟩] A 🡒 (∼B ⋏ ◇B)) (hp : y ⊩[⟨fineFrame, V⟩] A) :
    ∃ z, y ≺ z ∧ z ⊀ y ∧ z ⊩[⟨fineFrame, V⟩] B := by
  obtain ⟨hnq, hq⟩ := forces_and.mp (hg hp);
  obtain ⟨z, hyz, hz⟩ := forces_dia.mp hq;
  use z, hyz;
  and_intros;
  · by_contra hzy;
    obtain rfl := rel_antisymm hyz hzy;
    exact forces_neg.mp hnq hz;
  · exact hz

private lemma exists_p01_chain (hD : w ⊩[⟨fineFrame, V⟩] δ) :
    ∃ u : ℕ → fineFrame.World, u 0 = w ∧
      ∀ i, u i ≺ u (i + 1) ∧ u (i + 1) ⊀ u i ∧
        w ≺ u i ∧ u i ⊩[⟨fineFrame, V⟩] (#0 ⋎ #1) := by
  obtain ⟨hp01, hbox₁, hbox₂, -⟩ := forces_δ_iff.mp hD;
  have step : ∀ y : fineFrame.World, w ≺ y → y ⊩[⟨fineFrame, V⟩] (#0 ⋎ #1) →
      ∃ v, y ≺ v ∧ v ⊀ y ∧ w ≺ v ∧ v ⊩[⟨fineFrame, V⟩] (#0 ⋎ #1) := by
    intro y hwy hy;
    rcases forces_or.mp hy with hy₀ | hy₁;
    · obtain ⟨z, hyz, hzy, hz⟩ := exists_rel_of_guard (forces_box.mp hbox₁ y hwy) hy₀;
      exact ⟨z, hyz, hzy, Frame.rel_trans hwy hyz, forces_or.mpr (Or.inr hz)⟩;
    · obtain ⟨z, hyz, hzy, hz⟩ := exists_rel_of_guard (forces_box.mp hbox₂ y hwy) hy₁;
      exact ⟨z, hyz, hzy, Frame.rel_trans hwy hyz, forces_or.mpr (Or.inl hz)⟩;
  obtain ⟨u, hu₀, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => y ≺ v ∧ v ⊀ y)
    (P := fun _ y => w ≺ y ∧ y ⊩[⟨fineFrame, V⟩] (#0 ⋎ #1)) ⟨Frame.rel_refl w, hp01⟩ <| by
      rintro - y ⟨hwy, hy⟩;
      obtain ⟨v, hyv, hvy, hwv, hv⟩ := step y hwy hy;
      exact ⟨v, ⟨hyv, hvy⟩, hwv, hv⟩;
  use u;
  and_intros;
  · exact hu₀;
  · intro i;
    exact ⟨(hu i).2.1, (hu i).2.2, (hu i).1⟩

/-- A point forcing `δ` is a `d`-point. -/
lemma exists_d_of_forces_δ (hD : w ⊩[⟨fineFrame, V⟩] δ) :
    ∃ m, w = d m := by
  obtain ⟨u, hu₀, hu⟩ := exists_p01_chain hD;
  obtain ⟨m, hm⟩ := strict_chain_all_d (fun i => (hu i).1) (fun i => (hu i).2.1) 0;
  exact ⟨m, hu₀ ▸ hm⟩

/-- If `d_m` forces `δ`, every `d_k` with `m ≤ k` forces `#0 ⋎ #1`. -/
lemma forces_p01_at {m : ℕ} (hD : d m ⊩[⟨fineFrame, V⟩] δ) {k : ℕ} (hk : m ≤ k) :
    d k ⊩[⟨fineFrame, V⟩] #0 ⋎ #1 := by
  obtain ⟨u, hu₀, hu⟩ := exists_p01_chain hD;
  have hd : ∀ i, ∃ k, u i = d k := by
    intro i;
    exact strict_chain_all_d (fun j => (hu j).1) (fun j => (hu j).2.1) i;
  choose kf hkf using hd;
  have hmono : StrictMono kf := by
    apply strictMono_nat_of_lt_succ;
    intro i;
    have h := (hu i).2.1;
    rw [hkf i, hkf (i + 1)] at h;
    simpa using h;
  have h₁ : d (kf k) ⊩[⟨fineFrame, V⟩] #0 ⋎ #1 := by
    rw [← hkf k];
    exact (hu k).2.2.2;
  by_contra hcon;
  obtain ⟨-, -, -, hbox⟩ := forces_δ_iff.mp hD;
  have h₂ := forces_box.mp hbox (d k) (by simp [hk]) (forces_neg.mpr hcon);
  exact forces_neg.mp (forces_box.mp h₂ (d (kf k)) (by simpa using hmono.le_apply)) h₁

/-! ### Classification of the V-shape -/

/-- A `V`-shape is, up to `swap`, of the form `(b_{n+1}, b_n, c_{n+1}, c_n)`. -/
lemma v_shape_classify {t u₀ u₁ v₀ v₁ : fineFrame.World}
    (hRtu1 : t ≺ u₁) (hRu1u0 : u₁ ≺ u₀) (hRtv1 : t ≺ v₁) (hRv1v0 : v₁ ≺ v₀)
    (hnu0u1 : u₀ ⊀ u₁) (hnv0v1 : v₀ ⊀ v₁) (hnu1v0 : u₁ ⊀ v₀) (hnv1u0 : v₁ ⊀ u₀) :
    ∃ n : ℕ, (u₁ = b (n + 1) ∧ u₀ = b n ∧ v₁ = c (n + 1) ∧ v₀ = c n) ∨
             (u₁ = c (n + 1) ∧ u₀ = c n ∧ v₁ = b (n + 1) ∧ v₀ = b n) := by
  cases u₁ using casesOn <;> cases u₀ using casesOn <;> cases v₁ using casesOn <;>
    cases v₀ using casesOn <;> simp at * <;> omega

end Extraction

/-! ### The reference points of the V-shape -/

/-- The forcing data of an upright `V`-shape `(b_{n+1}, b_n, c_{n+1}, c_n)` below `d_m`. -/
structure ShapeData (m n : ℕ) (V : fineFrame.World → ℕ → Prop) : Prop where
  hwδ : d m ⊩[⟨fineFrame, V⟩] δ
  hwι₀ : d m ⊩[⟨fineFrame, V⟩] ι 0
  hbnβ₀ : b n ⊩[⟨fineFrame, V⟩] β 0
  hbn1β₁ : b (n + 1) ⊩[⟨fineFrame, V⟩] β 1
  hcnγ₀ : c n ⊩[⟨fineFrame, V⟩] γ 0
  hcn1γ₁ : c (n + 1) ⊩[⟨fineFrame, V⟩] γ 1

section Cone

variable {V : fineFrame.World → ℕ → Prop} {m n : ℕ} {z : fineFrame.World}

section

variable (hs : ShapeData m n V)

include hs

lemma ShapeData.hι₁ : d m ⊩[⟨fineFrame, V⟩] ι₁ 0 := (forces_ι_iff.mp hs.hwι₀).1
lemma ShapeData.hι₂ : d m ⊩[⟨fineFrame, V⟩] ι₂ 0 := (forces_ι_iff.mp hs.hwι₀).2.1
lemma ShapeData.hι₃ : d m ⊩[⟨fineFrame, V⟩] ι₃ 0 := (forces_ι_iff.mp hs.hwι₀).2.2.1
lemma ShapeData.hι₄ : d m ⊩[⟨fineFrame, V⟩] ι₄ 0 := (forces_ι_iff.mp hs.hwι₀).2.2.2

lemma ShapeData.ι₁_at (y : fineFrame.World) (hy : d m ≺ y) (h : y ⊩[⟨fineFrame, V⟩] β 1) :
    y ⊩[⟨fineFrame, V⟩] ◇(β 0) ⋏ ∼◇(γ 0) := forces_box.mp hs.hι₁ y hy h

lemma ShapeData.ι₂_at (y : fineFrame.World) (hy : d m ≺ y) (h : y ⊩[⟨fineFrame, V⟩] γ 1) :
    y ⊩[⟨fineFrame, V⟩] ◇(γ 0) ⋏ ∼◇(β 0) := forces_box.mp hs.hι₂ y hy h

lemma ShapeData.ι₃_at (y : fineFrame.World) (hy : d m ≺ y) (h : y ⊩[⟨fineFrame, V⟩] β 0) :
    y ⊩[⟨fineFrame, V⟩] ∼◇(β 1) := forces_box.mp hs.hι₃ y hy h

lemma ShapeData.ι₄_at (y : fineFrame.World) (hy : d m ≺ y) (h : y ⊩[⟨fineFrame, V⟩] γ 0) :
    y ⊩[⟨fineFrame, V⟩] ∼◇(γ 1) := forces_box.mp hs.hι₄ y hy h

lemma ShapeData.mirror : ShapeData m n (mirrorVal V) where
  hwδ := by simpa [forces_mirror, δ] using hs.hwδ
  hwι₀ := by rw [forces_mirror, forces_ι_subst_tau_iff]; exact hs.hwι₀
  hbnβ₀ := by simpa [forces_mirror, mirrorVal] using hs.hcnγ₀
  hbn1β₁ := by simpa [forces_mirror, mirrorVal] using hs.hcn1γ₁
  hcnγ₀ := by simpa [forces_mirror, mirrorVal] using hs.hbnβ₀
  hcn1γ₁ := by simpa [forces_mirror, mirrorVal] using hs.hbn1β₁

/-! ### The `β`-side facts on the cone of `a_n` -/

/-- On the cone of `a_n`, `β 0` is forced only at `b_n`. -/
lemma eq_b_of_forces_β₀ (hmn : m ≤ n) (hRz : a n ≺ z) (h : z ⊩[⟨fineFrame, V⟩] β 0) :
    z = b n := by
  have h₁ := hs.ι₃_at z (Frame.rel_trans (by simp [hmn]) hRz) h;
  have h₂ := (forces_and.mp (hs.ι₂_at (c (n + 1)) (by simp) hs.hcn1γ₁)).2;
  cases z using casesOn with
  | a k =>
    simp only [rel_a_a] at hRz;
    subst hRz;
    exact (false_of_neg_dia h₁ (y := b (k + 1)) (by simp) hs.hbn1β₁).elim;
  | b k =>
    simp at hRz;
    rcases Nat.lt_trichotomy k n with hk | rfl | hk;
    · exact (false_of_neg_dia h₂ (y := b k) (by simp; omega) h).elim;
    · rfl;
    · obtain rfl : k = n + 1 := by omega;
      exact (false_of_neg_dia h₁ (y := b (n + 1)) (by simp) hs.hbn1β₁).elim;
  | c k =>
    simp at hRz;
    exact (false_of_neg_dia h₂ (y := c k) (by simp; omega) h).elim;
  | d k => simp at hRz

/-- On the cone of `a_n`, `β 1` is forced only at `b_{n+1}`. -/
lemma eq_b_of_forces_β₁ (hmn : m ≤ n) (hRz : a n ≺ z) (h : z ⊩[⟨fineFrame, V⟩] β 1) :
    z = b (n + 1) := by
  have hR : d m ≺ z := Frame.rel_trans (by simp [hmn]) hRz;
  obtain ⟨h₁, h₂⟩ := forces_and.mp (hs.ι₁_at z hR h);
  have h₃ := hs.ι₃_at (b n) (by simp) hs.hbnβ₀;
  cases z using casesOn with
  | a k =>
    simp only [rel_a_a] at hRz;
    subst hRz;
    exact (false_of_neg_dia h₂ (y := c k) (by simp) hs.hcnγ₀).elim;
  | b k =>
    simp at hRz;
    rcases Nat.lt_or_ge k (n + 1) with hk | hk;
    · exact (false_of_neg_dia h₃ (y := b k) (by simp; omega) h).elim;
    · obtain rfl : k = n + 1 := by omega;
      rfl;
  | c k =>
    simp at hRz;
    rcases Nat.lt_or_ge k n with hk | hk;
    · obtain ⟨w, hcw, hw⟩ := forces_dia.mp h₁;
      obtain rfl := eq_b_of_forces_β₀ hs hmn (Frame.rel_trans (by simp; omega) hcw) hw;
      simp at hcw;
      omega;
    · exact (false_of_neg_dia h₂ (y := c n) (by simp [hk]) hs.hcnγ₀).elim;
  | d k => simp at hRz

/-- `b_{n+2}` forces `β 2`. -/
lemma forces_β₂_at : b (n + 2) ⊩[⟨fineFrame, V⟩] β 2 := by
  have h₁ := (forces_and.mp (hs.ι₁_at (b (n + 1)) (by simp) hs.hbn1β₁)).2;
  have h₂ := hs.ι₄_at (c n) (by simp) hs.hcnγ₀;
  rw [β_add_two, forces_and, forces_and];
  and_intros;
  · exact forces_dia.mpr ⟨b (n + 1), by simp, hs.hbn1β₁⟩;
  · exact forces_dia.mpr ⟨c n, by simp, hs.hcnγ₀⟩;
  · rw [forces_neg, not_forces_dia];
    intro q hq hqC1;
    cases q using casesOn with
    | a k => simp at hq;
    | d k => simp at hq;
    | c k =>
      simp at hq;
      exact false_of_neg_dia h₂ (by simp; omega) hqC1;
    | b k =>
      simp at hq;
      obtain ⟨hkC0, hkB0⟩ := forces_and.mp (hs.ι₂_at (b k) (by simp) hqC1);
      rcases Nat.lt_or_ge k (n + 2) with hk | hk;
      · obtain ⟨r, hbkr, hr⟩ := forces_dia.mp hkC0;
        exact false_of_neg_dia h₁ (Frame.rel_trans (by simp; omega) hbkr) hr;
      · obtain rfl : k = n + 2 := by omega;
        exact false_of_neg_dia hkB0 (y := b n) (by simp) hs.hbnβ₀

/-! ### The facts on the cone of `d_{n+1}` -/

/-- On the cone of `d_{n+1}`, `β 1` is forced only at `b_{n+1}`. -/
lemma eq_bn1_of_forces_β₁ (hmn : m ≤ n) (hRz : d (n + 1) ≺ z) (h : z ⊩[⟨fineFrame, V⟩] β 1) :
    z = b (n + 1) := by
  have h₁ := (forces_and.mp (hs.ι₁_at z (Frame.rel_trans (by simp; omega) hRz) h)).2;
  cases z using casesOn with
  | d k => exact (false_of_neg_dia h₁ (y := c n) (by simp) hs.hcnγ₀).elim;
  | a k =>
    simp at hRz;
    exact (false_of_neg_dia h₁ (y := c n) (by simp; omega) hs.hcnγ₀).elim;
  | c k =>
    rcases Nat.lt_or_ge k n with hk | hk;
    · have := eq_b_of_forces_β₁ hs hmn (by simp; omega) h;
      simp at this;
    · exact (false_of_neg_dia h₁ (y := c n) (by simp [hk]) hs.hcnγ₀).elim;
  | b k =>
    rcases Nat.lt_or_ge k (n + 2) with hk | hk;
    · exact eq_b_of_forces_β₁ hs hmn (by simp; omega) h;
    · exact (false_of_neg_dia h₁ (y := c n) (by simp; omega) hs.hcnγ₀).elim

/-- On the cone of `d_{n+1}`, `β 2` is forced only at `b_{n+2}`. -/
lemma eq_bn2_of_forces_β₂ (hmn : m ≤ n) (hRz : d (n + 1) ≺ z) (h : z ⊩[⟨fineFrame, V⟩] β 2) :
    z = b (n + 2) := by
  rw [β_add_two, forces_and, forces_and] at h;
  obtain ⟨h₁, h₂, h₃⟩ := h;
  obtain ⟨y, hzy, hy⟩ := forces_dia.mp h₁;
  obtain rfl := eq_bn1_of_forces_β₁ hs hmn (Frame.rel_trans hRz hzy) hy;
  have h₄ := (forces_and.mp (hs.ι₁_at (b (n + 1)) (by simp) hs.hbn1β₁)).2;
  cases z using casesOn with
  | a k =>
    simp at hRz;
    exact (false_of_neg_dia h₃ (y := c (n + 1)) (by simp; omega) hs.hcn1γ₁).elim;
  | d k => exact (false_of_neg_dia h₃ (y := c (n + 1)) (by simp) hs.hcn1γ₁).elim;
  | c k =>
    simp at hzy;
    exact (false_of_neg_dia h₃ (y := c (n + 1)) (by simp; omega) hs.hcn1γ₁).elim;
  | b k =>
    simp at hzy;
    rcases Nat.lt_or_ge k (n + 3) with hk | hk;
    · obtain rfl | rfl : k = n + 1 ∨ k = n + 2 := by omega;
      · exact (forces_neg.mp h₄ h₂).elim;
      · rfl;
    · exact (false_of_neg_dia h₃ (y := c (n + 1)) (by simp; omega) hs.hcn1γ₁).elim

/-! ### The `γ`-side facts, by the mirror -/

/-- `c_{n+2}` forces `γ 2`, the mirror of `forces_β₂_at`. -/
lemma forces_γ₂_at : c (n + 2) ⊩[⟨fineFrame, V⟩] γ 2 := by
  simpa [forces_mirror] using forces_β₂_at hs.mirror

/-- On the cone of `d_{n+1}`, `γ 1` is forced only at `c_{n+1}`. -/
lemma eq_cn1_of_forces_γ₁ (hmn : m ≤ n) (hRz : d (n + 1) ≺ z) (h : z ⊩[⟨fineFrame, V⟩] γ 1) :
    z = c (n + 1) := by
  have := eq_bn1_of_forces_β₁ hs.mirror hmn (by simpa using rel_swap.mpr hRz)
    (by simpa [forces_mirror, mirrorVal] using h);
  simpa [swap_involutive.eq_iff] using this

/-- On the cone of `d_{n+1}`, `γ 2` is forced only at `c_{n+2}`. -/
lemma eq_cn2_of_forces_γ₂ (hmn : m ≤ n) (hRz : d (n + 1) ≺ z) (h : z ⊩[⟨fineFrame, V⟩] γ 2) :
    z = c (n + 2) := by
  have := eq_bn2_of_forces_β₂ hs.mirror hmn (by simpa using rel_swap.mpr hRz)
    (by simpa [forces_mirror] using h);
  simpa [swap_involutive.eq_iff] using this

/-- `a_{n+1}` sees no point forcing `β 3`. -/
lemma not_forces_dia_β₃ (hmn : m ≤ n) : a (n + 1) ⊩[⟨fineFrame, V⟩] ∼◇(β 3) := by
  rw [forces_neg, not_forces_dia];
  intro p hp hpB3;
  rw [β_add_two, forces_and, forces_and] at hpB3;
  obtain ⟨h₁, h₂, h₃⟩ := hpB3;
  obtain ⟨q₂, hpq₂, hq₂⟩ := forces_dia.mp h₁;
  obtain ⟨q₁, hpq₁, hq₁⟩ := forces_dia.mp h₂;
  have hdp : d (n + 1) ≺ p := Frame.rel_trans (by simp) hp;
  obtain rfl := eq_bn2_of_forces_β₂ hs hmn (Frame.rel_trans hdp hpq₂) hq₂;
  obtain rfl := eq_cn1_of_forces_γ₁ hs hmn (Frame.rel_trans hdp hpq₁) hq₁;
  cases p using casesOn with
  | d j => simp at hp;
  | a j =>
    simp only [rel_a_a] at hp;
    subst hp;
    exact false_of_neg_dia h₃ (y := c (n + 2)) (by simp) (forces_γ₂_at hs)
  | b j =>
    simp at hp hpq₁;
    omega
  | c j =>
    simp at hp hpq₂;
    omega

/-- `a_{n+1}` sees no point forcing `γ 3`, the mirror of `not_forces_dia_β₃`. -/
lemma not_forces_dia_γ₃ (hmn : m ≤ n) : a (n + 1) ⊩[⟨fineFrame, V⟩] ∼◇(γ 3) := by
  simpa [forces_mirror] using not_forces_dia_β₃ hs.mirror hmn

/-- `a_{n+1}` forces `α 1`. -/
lemma forces_α₁_at (hmn : m ≤ n) : a (n + 1) ⊩[⟨fineFrame, V⟩] α 1 := by
  rw [forces_α_iff];
  and_intros;
  · exact forces_dia.mpr ⟨b (n + 2), by simp, forces_β₂_at hs⟩;
  · exact forces_dia.mpr ⟨c (n + 2), by simp, forces_γ₂_at hs⟩;
  · exact not_forces_dia_β₃ hs hmn;
  · exact not_forces_dia_γ₃ hs hmn

/-- `d_{n+1}` sees no point forcing `α 0`. -/
lemma not_dia_α₀_at (hmn : m ≤ n) : d (n + 1) ⊩[⟨fineFrame, V⟩] ∼◇(α 0) := by
  rw [forces_neg, not_forces_dia];
  intro z hz hzA0;
  obtain ⟨h₁, h₂, h₃, h₄⟩ := forces_α_iff.mp hzA0;
  obtain ⟨y₁, hzy₁, hy₁⟩ := forces_dia.mp h₁;
  obtain ⟨y₂, hzy₂, hy₂⟩ := forces_dia.mp h₂;
  obtain rfl := eq_bn1_of_forces_β₁ hs hmn (Frame.rel_trans hz hzy₁) hy₁;
  obtain rfl := eq_cn1_of_forces_γ₁ hs hmn (Frame.rel_trans hz hzy₂) hy₂;
  cases z using casesOn with
  | d k => exact false_of_neg_dia h₃ (y := b (n + 2)) (by simp) (forces_β₂_at hs)
  | a k =>
    simp at hz;
    exact false_of_neg_dia h₃ (y := b (n + 2)) (by simp; omega) (forces_β₂_at hs)
  | b k =>
    simp at hzy₂;
    exact false_of_neg_dia h₃ (y := b (n + 2)) (by simp; omega) (forces_β₂_at hs)
  | c k =>
    simp at hzy₁;
    exact false_of_neg_dia h₄ (y := c (n + 2)) (by simp; omega) (forces_γ₂_at hs)

/-- A point forcing `α 0` and seeing `b_{n+1}` and `c_{n+1}` is `a_n`. -/
lemma apex_eq (hzA0 : z ⊩[⟨fineFrame, V⟩] α 0) (hRzb : z ≺ b (n + 1)) (hRzc : z ≺ c (n + 1)) :
    z = a n := by
  obtain ⟨-, -, h₁, h₂⟩ := forces_α_iff.mp hzA0;
  cases z using casesOn with
  | d k => exact (false_of_neg_dia h₁ (y := b (n + 2)) (by simp) (forces_β₂_at hs)).elim;
  | b k =>
    simp at hRzb hRzc;
    exact (false_of_neg_dia h₁ (y := b (n + 2)) (by simp; omega) (forces_β₂_at hs)).elim;
  | c k =>
    simp at hRzb hRzc;
    exact (false_of_neg_dia h₂ (y := c (n + 2)) (by simp; omega) (forces_γ₂_at hs)).elim;
  | a k =>
    simp at hRzb hRzc;
    have hkn : k ≤ n := by
      by_contra hc;
      exact false_of_neg_dia h₁ (y := b (n + 2)) (by simp; omega) (forces_β₂_at hs);
    exact congrArg a (by omega)

end

/-! ### Assembly: the frame validates `θ` -/

lemma forces_ψ_of_shapeAndApex (hs : ShapeData m n V) {t : fineFrame.World}
    (hwt : d m ≺ t) (htA0 : t ⊩[⟨fineFrame, V⟩] α 0)
    (hRtb : t ≺ b (n + 1)) (hRtc : t ≺ c (n + 1)) :
    d m ⊩[⟨fineFrame, V⟩] ψ := by
  obtain rfl := apex_eq hs htA0 hRtb hRtc;
  have hmn : m ≤ n := by simpa using hwt;
  rw [ψ, forces_dia];
  use d (n + 1);
  rw [forces_and, forces_and];
  and_intros;
  · simp; omega;
  · exact forces_p01_at hs.hwδ (by omega);
  · exact not_dia_α₀_at hs hmn;
  · exact forces_dia.mpr ⟨a (n + 1), by simp, forces_α₁_at hs hmn⟩

end Cone

/-- Fine's frame validates `θ`: for every valuation and every point, `ε → ψ` holds.

- [Fin74a, Lemma 2]
- [Lit04, p. 332] -/
theorem validates_θ : fineFrame ⊧ θ := by
  intro V w hE;
  obtain ⟨t, u₀, u₁, v₀, v₁, hwt, htA0, htu1, hu1u0, htv1, hv1v0, hu1B1, hu0B0, hv1C1, hv0C0,
    hnu0u1, hnv0v1, hnu1v0, hnv1u0⟩ := exists_V_shape hE;
  obtain ⟨hD, -, hK0⟩ := forces_ε_iff.mp hE;
  obtain ⟨m, rfl⟩ := exists_d_of_forces_δ hD;
  obtain ⟨n, hcase⟩ := v_shape_classify htu1 hu1u0 htv1 hv1v0 hnu0u1 hnv0v1 hnu1v0 hnv1u0;
  rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩;
  · exact forces_ψ_of_shapeAndApex ⟨hD, hK0, hu0B0, hu1B1, hv0C0, hv1C1⟩ hwt htA0 htu1 htv1;
  · have hs : ShapeData m n (V ∘ swap) := by
      constructor;
      · simpa using forces_swap_iff.mp hD;
      · simpa using forces_swap_iff.mp hK0;
      · simpa using forces_swap_iff.mp hu0B0;
      · simpa using forces_swap_iff.mp hu1B1;
      · simpa using forces_swap_iff.mp hv0C0;
      · simpa using forces_swap_iff.mp hv1C1;
    have hF := forces_ψ_of_shapeAndApex hs (by simpa using rel_swap.mpr hwt)
      (forces_swap_iff.mp htA0) (by simpa using rel_swap.mpr htu1)
      (by simpa using rel_swap.mpr htv1);
    exact forces_swap_iff.mpr (by simpa using hF)

end fineFrame

end Countermodel

/-! ### Kripke-incompleteness -/

section Incomplete

universe u

variable {κ : Type*} {F : Frame κ}

namespace Fine

open Model.World

section Chain

variable {M : Model κ ℕ} [IsTrans κ M.Rel'] {x y : M.World} {m : ℕ}

lemma forces_δ_of_rel (hD : x ⊩ δ) (Rxy : x ≺ y) (hp : y ⊩ #0 ⋎ #1) : y ⊩ δ := by
  obtain ⟨-, h₁, h₂, h₃⟩ := forces_δ_iff.mp hD;
  rw [forces_δ_iff];
  and_intros;
  · exact hp;
  · exact forces_box_of_rel h₁ Rxy;
  · exact forces_box_of_rel h₂ Rxy;
  · exact forces_box_of_rel h₃ Rxy

/-- If `θ` is strongly valid and `x` forces `ε⟦σ_m⟧`, a strict successor forces `ε⟦σ_{m+1}⟧`.

- [Fin74a, (3)] -/
lemma chain_step (hG : θ ∈ M.logic) (hx : x ⊩ ε⟦shift m⟧) :
    ∃ y : M.World, x ≺ y ∧ y ⊀ x ∧ y ⊩ ε⟦shift (m + 1)⟧ := by
  obtain ⟨y, Rxy, hy01, hyA, hyA'⟩ := forces_ψ_subst_shift.mp <| hG (shift m) x hx;
  obtain ⟨hD, hAm, hK⟩ := forces_ε_subst_shift.mp hx;
  have hstrict : y ⊀ x := by
    by_contra Ryx;
    exact hyA <| forces_dia_of_rel hAm Ryx;
  exact ⟨y, Rxy, hstrict,
    forces_ε_subst_shift.mpr ⟨forces_δ_of_rel hD Rxy hy01, hyA', forces_ι_succ hK Rxy⟩⟩

end Chain

section Psi

variable {u : ℕ → F.World}

/-- The valuation making `#6` true at `u (3i)` and `#7` at `u (3i + 1)`.

- [Fin74a] -/
def chainVal (u : ℕ → F.World) : F.World → ℕ → Prop
| v, 6 => ∃ i, v = u (3 * i)
| v, 7 => ∃ i, v = u (3 * i + 1)
| _, _ => False

lemma forces_chainVal_6_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[⟨F, chainVal u⟩] #6 ↔ ∃ i, n = 3 * i := by
  constructor;
  · rintro ⟨i, hi⟩;
    exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩;
    use i;

lemma forces_chainVal_7_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[⟨F, chainVal u⟩] #7 ↔ ∃ i, n = 3 * i + 1 := by
  constructor;
  · rintro ⟨i, hi⟩;
    exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩;
    use i;

lemma chainVal_forces_neg_χ [IsTrans κ F.Rel'] (hR : ∀ m, u m ≺ u (m + 1))
    (hinj : Function.Injective u) : u 0 ⊩[⟨F, chainVal u⟩] ∼χ := by
  have hlt : ∀ {i j}, i < j → u i ≺ u j := fun h => Nat.rel_of_forall_rel_succ_of_lt F.Rel' hR h;
  unfold χ;
  rw [forces_neg, not_forces_neg, forces_and];
  and_intros;
  · exact (forces_chainVal_6_iff hinj 0).mpr ⟨0, rfl⟩;
  · rw [forces_box];
    rintro y - ⟨i, rfl⟩;
    use u (3 * i + 1);
    constructor;
    · exact hlt <| by omega;
    · simp only [forces_and];
      and_intros;
      · apply forces_chainVal_6_iff hinj _ |>.not.mpr;
        omega;
      · exact (forces_chainVal_7_iff hinj (3 * i + 1)).mpr ⟨i, rfl⟩;
      · use u (3 * i + 2);
        constructor;
        · exact hlt <| by omega;
        · simp only [forces_and];
          and_intros;
          · apply forces_chainVal_6_iff hinj _ |>.not.mpr;
            omega;
          · apply forces_chainVal_7_iff hinj _ |>.not.mpr;
            omega;
          · use u (3 * (i + 1));
            constructor;
            · exact hlt <| by omega;
            · exact (forces_chainVal_6_iff hinj (3 * (i + 1))).mpr ⟨i + 1, rfl⟩;

end Psi

end Fine

open Fine

/-- Every frame validating Fine's logic validates `∼ε`.

- [Fin74a, Lemma 1]
- [Lit04, p. 332] -/
theorem validates_neg_ε_of_validates_logicS4Fine (hL : F ⊧ logicS4Fine) : F ⊧ ∼ε := by
  obtain ⟨_, _⟩ :=
    Frame.validates_logicS4_iff.mp fun A h => hL A <| NormalLogic.mem_add_of_mem h;
  intro V x hxE;
  have hG : θ ∈ (Model.mk F V).logic :=
    Frame.logic_le_model_logic <| hL θ <| NormalLogic.mem_add <| by simp;
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => y ≺ v ∧ v ⊀ y)
    (P := fun m y => y ⊩[⟨F, V⟩] ε⟦shift m⟧)
    (forces_ε_subst_shift.mpr <| forces_ε_iff.mp hxE) fun m y hy => by
      obtain ⟨v, Ryv, Rvy, hv⟩ := chain_step hG hy;
      exact ⟨v, ⟨Ryv, Rvy⟩, hv⟩;
  have hR : ∀ m, u m ≺ u (m + 1) := fun m => (hu m).2.1;
  have hinj := injective_of_forall_rel_succ hR fun m => (hu m).2.2;
  exact chainVal_forces_neg_χ hR hinj <| hL χ (NormalLogic.mem_add <| by simp) (chainVal u) (u 0)

/-- Every theorem of Fine's logic is strongly valid in Fine's model.

- [Fin74a, Lemma 2] -/
lemma logicS4Fine_le_fineModel_logic : logicS4Fine ≤ fineModel.logic :=
  NormalLogic.add_le (fun _ h => Frame.logic_le_model_logic <| Frame.validates_logicS4 _ h) <| by
    rintro _ (rfl | rfl);
    · exact Frame.logic_le_model_logic fineFrame.validates_θ;
    · exact fineModel.χ_mem_logic

/-- `∼ε` is not a theorem of Fine's logic.

- [Fin74a, Lemma 2] -/
lemma neg_ε_not_mem_logicS4Fine : ∼ε ∉ logicS4Fine := by
  by_contra h;
  exact Model.validates_of_mem_logic (logicS4Fine_le_fineModel_logic h) (fineFrame.d 0)
    fineModel.forces_ε_d0

/-- `∼ε` is valid in every frame validating Fine's logic.

- [Fin74a, Lemma 1] -/
lemma neg_ε_mem_frameLogic_logicS4Fine : ∼ε ∈ logicS4Fine.frameLogic.{u} fun _ _ => True :=
  fun _ _ _ hL => validates_neg_ε_of_validates_logicS4Fine hL

/-- Fine's logic is Kripke-incomplete.

- [Fin74a]
- [Lit04, p. 332] -/
theorem not_kripkeComplete_logicS4Fine : ¬logicS4Fine.KripkeComplete.{u} fun _ _ => True := by
  by_contra h;
  exact neg_ε_not_mem_logicS4Fine <| h neg_ε_mem_frameLogic_logicS4Fine

end Incomplete

end
