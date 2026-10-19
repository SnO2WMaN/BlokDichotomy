module

public import BlokDichotomy.Fine.Model

/-!
# Forcing in Fine's model

Fine's model forces `ε` at `d_0`, and `χ` is strongly valid in it. The mirror valuation `mirrorVal`,
built from the `b`/`c` involution `swap` and the atom substitution `tau`, transports every
`β`-side lemma about a valuation to its `γ`-side twin. The facts about `fineModel` live in the
namespace `fineModel`, those about `fineFrame` with an arbitrary valuation in `fineFrame`.

## References

- [Fin74a, Lemma 2]
- [Lit04, p. 332]
-/

@[expose] public section

namespace fineModel

open Fine fineFrame Model.World

/-- `β_2` is forced exactly at `b_2`. -/
lemma forces_β₂_iff (w : fineFrame.World) : w ⊩[fineModel] β 2 ↔ w = .b 2 := by
  rw [β_add_two, forces_and, forces_and, forces_neg];
  simp only [Nat.zero_add, β_one, γ_zero, γ_one, forces_dia, forces_atom_3_iff, forces_atom_4_iff,
    forces_atom_5_iff, NotForces, fineFrame.rel_iff, exists_eq_right];
  cases w <;> simp <;> omega

/-- `γ_2` is forced exactly at `c_2`. -/
lemma forces_γ₂_iff (w : fineFrame.World) : w ⊩[fineModel] γ 2 ↔ w = .c 2 := by
  rw [γ_add_two, forces_and, forces_and, forces_neg];
  simp only [Nat.zero_add, β_zero, β_one, γ_one, forces_dia, forces_atom_2_iff, forces_atom_3_iff,
    forces_atom_5_iff, NotForces, fineFrame.rel_iff, exists_eq_right];
  cases w <;> simp <;> omega

/-- `d_0` forces `δ`. -/
lemma forces_δ_d0 : World.d 0 ⊩[fineModel] δ := by
  rw [δ, forces_and, forces_and, forces_and, forces_box, forces_box, forces_box];
  and_intros;
  · rw [forces_or];
    simp;
  · rintro w -;
    rw [forces_imp, forces_and, forces_neg, forces_dia];
    rcases w with _ | _ | _ | k;
    iterate 3 simp [NotForces];
    simp only [NotForces, forces_atom_0_iff, forces_atom_1_iff, fineFrame.rel_iff,
      ↓existsAndEq, R_d_d, true_and, World.d.injEq];
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk;
    · exact Or.inr ⟨by omega, k + 1, by omega, by omega⟩;
    · exact Or.inl (by omega);
  · rintro w -;
    rw [forces_imp, forces_and, forces_neg, forces_dia];
    rcases w with _ | _ | _ | k;
    iterate 3 simp [NotForces];
    simp only [NotForces, forces_atom_0_iff, forces_atom_1_iff, fineFrame.rel_iff,
      ↓existsAndEq, R_d_d, true_and, World.d.injEq];
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk;
    · exact Or.inl (by omega);
    · exact Or.inr ⟨by omega, k + 1, by omega, by omega⟩;
  · rintro (_ | _ | _ | k) -;
    all_goals rw [forces_imp, forces_box];
    · right;
      rintro (_ | _ | _ | n) hn <;> rw [forces_neg, not_forces_or] <;> simp [NotForces] at hn ⊢;
    · right;
      rintro (_ | _ | _ | n) hn <;> rw [forces_neg, not_forces_or] <;> simp [NotForces] at hn ⊢;
    · right;
      rintro (_ | _ | _ | n) hn <;> rw [forces_neg, not_forces_or] <;> simp [NotForces] at hn ⊢;
    · left;
      rw [not_forces_neg, forces_or];
      simp;
      omega

/-- `α_0` is forced at `a_0`. -/
lemma forces_α₀_a0 : World.a 0 ⊩[fineModel] α 0 := by
  rw [α, forces_and, forces_and, forces_and, forces_neg, forces_neg];
  simp only [Nat.zero_add, β_one, γ_one, forces_dia, forces_atom_3_iff, forces_atom_5_iff,
    forces_β₂_iff, forces_γ₂_iff, NotForces, fineFrame.rel_iff, exists_eq_right];
  simp

/-- `◇(α_0)` is forced at `d_0`. -/
lemma forces_dia_α₀_d0 : World.d 0 ⊩[fineModel] ◇(α 0) :=
  forces_dia.mpr ⟨.a 0, by simp, forces_α₀_a0⟩

/-- `d_0` forces `ι 0` (the block `ι₁ 0 ⋏ ι₂ 0 ⋏ ι₃ 0 ⋏ ι₄ 0`). -/
lemma forces_ι₀_d0 : World.d 0 ⊩[fineModel] ι 0 := by
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
lemma forces_ε_d0 : World.d 0 ⊩[fineModel] ε :=
  forces_ε_iff.mpr ⟨forces_δ_d0, forces_dia_α₀_d0, forces_ι₀_d0⟩

/-! ### `χ` is strongly valid in Fine's model -/

/-- Along the `d`-chain, the truth of any fixed formula `A` is *eventually periodic with
period (dividing) 2*: past some threshold `N`, `d_i ⊩ A` depends only on the parity of `i`.

- [Fin74a, p.\ 28]
-/
lemma d_eventually_period_two (A : Formula ℕ) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → i % 2 = j % 2 →
      ((World.d i ⊩[fineModel] A) ↔ (World.d j ⊩[fineModel] A)) := by
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
    have hdia : ∀ i : ℕ, (World.d i ⊩[fineModel] ◇B) ↔
        (∃ k, i ≤ k ∧ (World.d k ⊩[fineModel] B)) ∨
        (∃ m, i ≤ m ∧ (World.a m ⊩[fineModel] B)) ∨
        (∃ k, (World.b k ⊩[fineModel] B)) ∨ (∃ k, (World.c k ⊩[fineModel] B)) := by
      intro i;
      rw [forces_dia];
      constructor;
      · rintro ⟨y, hy, hyA⟩;
        cases y with
        | d k => exact Or.inl ⟨k, hy, hyA⟩;
        | a m => exact Or.inr <| Or.inl ⟨m, hy, hyA⟩;
        | b k => exact Or.inr <| Or.inr <| Or.inl ⟨k, hyA⟩;
        | c k => exact Or.inr <| Or.inr <| Or.inr ⟨k, hyA⟩;
      · rintro (⟨k, hk, hA⟩ | ⟨m, hm, hA⟩ | ⟨k, hA⟩ | ⟨k, hA⟩);
        · exact ⟨World.d k, hk, hA⟩;
        · exact ⟨World.a m, hm, hA⟩;
        · exact ⟨World.b k, trivial, hA⟩;
        · exact ⟨World.c k, trivial, hA⟩;
    obtain ⟨N1, hN1⟩ := exists_ge_eventually_const (fun k => World.d k ⊩[fineModel] B);
    obtain ⟨N2, hN2⟩ := exists_ge_eventually_const (fun m => World.a m ⊩[fineModel] B);
    use max N1 N2;
    intro i j hi hj _;
    rw [hdia i, hdia j, hN1 i j (by omega) (by omega), hN2 i j (by omega) (by omega)]

/-- The three pairwise-incompatible phases that a refutation point of `χ` cycles through under a
substitution `σ`. -/
def phase (σ : Formula.Substitution ℕ ℕ) (r : ℕ) : Formula ℕ :=
  match r with
  | 0 => (#6 : Formula ℕ)⟦σ⟧
  | 1 => ∼((#6 : Formula ℕ)⟦σ⟧) ⋏ (#7 : Formula ℕ)⟦σ⟧
  | _ => ∼((#6 : Formula ℕ)⟦σ⟧) ⋏ ∼((#7 : Formula ℕ)⟦σ⟧)

@[simp, grind =]
lemma phase_zero (σ : Formula.Substitution ℕ ℕ) : phase σ 0 = (#6 : Formula ℕ)⟦σ⟧ := rfl
@[simp, grind =] lemma phase_one (σ : Formula.Substitution ℕ ℕ) :
    phase σ 1 = ∼((#6 : Formula ℕ)⟦σ⟧) ⋏ (#7 : Formula ℕ)⟦σ⟧ := rfl
@[simp, grind =] lemma phase_add_two (σ : Formula.Substitution ℕ ℕ) (r : ℕ) :
    phase σ (r + 2) = ∼((#6 : Formula ℕ)⟦σ⟧) ⋏ ∼((#7 : Formula ℕ)⟦σ⟧) := rfl

/-- `d_eventually_period_two` for the three phases simultaneously. -/
private lemma d_eventually_period_two_phase (σ : Formula.Substitution ℕ ℕ) :
    ∃ N : ℕ, ∀ r < 3, ∀ i j : ℕ, N ≤ i → N ≤ j → i % 2 = j % 2 →
      (World.d i ⊩[fineModel] phase σ r ↔ World.d j ⊩[fineModel] phase σ r) := by
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

/-- No world forces two distinct phases (among residues `< 3`) at once. -/
private lemma phase_incompatible {σ : Formula.Substitution ℕ ℕ} {w : fineFrame.World} {i j : ℕ}
    (hi3 : i < 3) (hj3 : j < 3) (hij : i ≠ j)
    (hi : w ⊩[fineModel] phase σ i) (hj : w ⊩[fineModel] phase σ j) : False := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega;
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega;
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl <;> simp_all <;> grind

/-- Auxiliary formula along the phase chain, bundling the current phase with the `◇`-witness
needed to advance to the next phase. -/
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

/-- One step of the phase chain: `χ`'s box hypothesis `hbox` at `x` produces, from `w` forcing
`Y σ (m % 3)` (with `x ≺ w`), a strict successor `v` forcing `Y σ ((m + 1) % 3)`. -/
private lemma Y_step {σ : Formula.Substitution ℕ ℕ} {x w : fineFrame.World}
    (hbox : x ⊩[fineModel] □(phase σ 0 🡒 ◇(Y σ 1))) (m : ℕ)
    (hxw : R x w) (hw : w ⊩[fineModel] Y σ (m % 3)) :
    ∃ v, R w v ∧ ¬ R v w ∧ R x v ∧ v ⊩[fineModel] Y σ ((m + 1) % 3) := by
  obtain ⟨v, hwv, hv⟩ : ∃ v, R w v ∧ v ⊩[fineModel] Y σ ((m + 1) % 3) := by
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
    obtain rfl := R_antisymm hvw hwv;
    exact phase_incompatible (Nat.mod_lt m (by omega)) (Nat.mod_lt (m + 1) (by omega))
      (by omega) (Y_imp_phase hw) (Y_imp_phase hv);
  · exact R_trans hxw hwv;
  · exact hv

/-- If `χ` is not strongly valid in Fine's model, some refutation point `x` of `χ⟦σ⟧` starts an
infinite *strict* chain along `R` whose points cycle through the three
pairwise-incompatible phases `phase σ 0`, `phase σ 1`, `phase σ 2` in order.

- [Fin74a, p.\ 28]
-/
lemma exists_phase_chain (h : ∃ σ x, x ⊮[fineModel] χ⟦σ⟧) :
    ∃ (σ : Formula.Substitution ℕ ℕ) (u : ℕ → fineFrame.World),
      (∀ m, R (u m) (u (m + 1))) ∧ (∀ m, ¬ R (u (m + 1)) (u m)) ∧
      ∀ m, u m ⊩[fineModel] phase σ (m % 3) := by
  obtain ⟨σ, x, hx⟩ := h;
  obtain ⟨hxs, hbox⟩ := forces_and.mp (not_forces_neg.mp hx);
  have h₀ : x ⊩[fineModel] Y σ (0 % 3) := by
    rw [Nat.zero_mod];
    exact hxs;
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun w v => R w v ∧ ¬R v w)
    (P := fun m w => R x w ∧ w ⊩[fineModel] Y σ (m % 3)) ⟨R_refl x, h₀⟩ <| by
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

- [Fin74a, p.\ 28]
-/
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
  have hphase' : ∀ i, World.d (k i) ⊩[fineModel] phase σ (i % 3) := by
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

/-- Forcing is invariant under simultaneously permuting the points of Fine's model by `swap`
and permuting the valuation along `swap`. -/
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
      exact ⟨swap y, R_swap.mpr hxy, ih.mp hy⟩;
    · rintro ⟨y, hxy, hy⟩;
      use swap y;
      and_intros;
      · exact R_swap.mp (by simpa using hxy);
      · exact ih.mpr (by simpa using hy)

/-- The valuation whose forcing relation is that of `V` seen through `swap` and `tau`. -/
def mirrorVal (V : fineFrame.World → ℕ → Prop) : fineFrame.World → ℕ → Prop :=
  fun w a => swap w ⊩[⟨fineFrame, V⟩] tau a

lemma forces_mirror :
    x ⊩[⟨fineFrame, mirrorVal V⟩] A ↔ swap x ⊩[⟨fineFrame, V⟩] A⟦tau⟧ := by
  rw [forces_subst, forces_swap_iff (x := swap x), swap_swap];
  exact Iff.rfl

end fineFrame

end
