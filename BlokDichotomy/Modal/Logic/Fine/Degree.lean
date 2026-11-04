module

public import BlokDichotomy.Modal.Logic.Fine
public import BlokDichotomy.ToMathlib.Data.Nat.Basic

/-!
# The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε`

Generalizing Fine's formula `χ` to the formulas `H m`, which are refuted on a strict chain
cycling through `m` pairwise incompatible phases, we obtain infinitely many pairwise distinct
frame companions of `𝐒𝟒 ⊕ ∼ε`, one for each periodic valuation of Fine's frame.

## References

- [Fin74a]
- [CZ98, §10.5, Problem 10.5]
-/

@[expose] public section

namespace Modal

namespace Fine

open Formula Model.World

variable {κ : Type*} {M : Model κ ℕ} {x y : M.World} {m n r r' : ℕ}

/-- The `r`-th phase: `#(8 + r)` holds but `#(8 + j)` fails for every `j < r`.

- [Fin74a] -/
def ph (r : ℕ) : Formula ℕ := #(8 + r) ⋏ ∼⋁((List.range r).map fun j => #(8 + j))

/-- `cycAux k r` says that the phases `r, r + 1, …, r + k - 1, 0` can be visited in turn.

- [Fin74a] -/
def cycAux : ℕ → ℕ → Formula ℕ
| 0, _ => ◇(ph 0)
| k + 1, r => ◇(ph r ⋏ cycAux k (r + 1))

/-- `cyc n` says that the phases `1, …, n - 1, 0` can be visited in turn.

- [Fin74a] -/
def cyc (n : ℕ) : Formula ℕ := cycAux (n - 1) 1

/-- The generalization of `χ` to a cycle of `n` phases.

- [Fin74a] -/
def H (n : ℕ) : Formula ℕ := ∼(ph 0 ⋏ □(ph 0 🡒 cyc n))

lemma forces_ph : x ⊩ ph r ↔ x ⊩ #(8 + r) ∧ ∀ j < r, x ⊮ #(8 + j) := by
  rw [ph, forces_and, forces_neg, NotForces, forces_disj_map];
  simp

lemma ph_incompatible (h : r ≠ r') (hr : x ⊩ ph r) (hr' : x ⊩ ph r') : False := by
  rcases Nat.lt_or_gt_of_ne h with hlt | hlt;
  · exact (forces_ph.mp hr').2 r hlt (forces_ph.mp hr).1;
  · exact (forces_ph.mp hr).2 r' hlt (forces_ph.mp hr').1

section Cycle

variable {u : ℕ → M.World}

lemma forces_ph_of_atom (hatom : ∀ p r, u p ⊩ #(8 + r) ↔ r < m ∧ p % m = r) (p r : ℕ) :
    u p ⊩ ph r ↔ r < m ∧ p % m = r := by
  rw [forces_ph, hatom];
  constructor;
  · exact fun h => h.1;
  · intro h;
    constructor;
    · exact h;
    · intro j hj hu;
      have := ((hatom p j).mp hu).2;
      omega

lemma forces_cycAux (hR : ∀ p, u p ≺ u (p + 1))
    (hatom : ∀ p r, u p ⊩ #(8 + r) ↔ r < m ∧ p % m = r) :
    ∀ k r p, p % m + 1 = r → r + k = m → u p ⊩ cycAux k r := by
  intro k;
  induction k with
  | zero =>
    intro r p hr hk;
    rw [cycAux, forces_dia];
    exact ⟨u (p + 1), hR p,
      (forces_ph_of_atom hatom _ _).mpr ⟨by omega, Nat.succ_mod_of_eq (by omega)⟩⟩
  | succ k ih =>
    intro r p hr hk;
    have hlt : p % m + 1 < m := by omega;
    rw [cycAux, forces_dia];
    exact ⟨u (p + 1), hR p, forces_and.mpr
      ⟨(forces_ph_of_atom hatom _ _).mpr ⟨by omega, by rw [Nat.succ_mod_of_lt hlt, hr]⟩,
      ih _ _ (by rw [Nat.succ_mod_of_lt hlt, hr]) (by omega)⟩⟩

lemma forces_neg_H (hm : 1 ≤ m) (hR : ∀ p, u p ≺ u (p + 1))
    (hatom : ∀ p r, u p ⊩ #(8 + r) ↔ r < m ∧ p % m = r)
    (hcov : ∀ y : M.World, y ⊩ ph 0 → ∃ i, y = u (m * i)) : u 0 ⊩ ∼H m := by
  rw [H, forces_neg, not_forces_neg, forces_and];
  and_intros;
  · exact (forces_ph_of_atom hatom 0 0).mpr ⟨hm, Nat.zero_mod m⟩;
  · rw [forces_box];
    intro y _ hy;
    obtain ⟨i, rfl⟩ := hcov y hy;
    exact forces_cycAux hR hatom (m - 1) 1 (m * i) (by simp) (by omega)

end Cycle

section CycVal

variable {F : Frame κ} {u : ℕ → F.World}

/-- The valuation making `#(8 + r)` true exactly at the points `u (n * i + r)`, for `r < n`.

- [Fin74a] -/
def cycVal (n : ℕ) (u : ℕ → F.World) : F.World → ℕ → Prop :=
  fun v a => ∃ i r, r < n ∧ a = 8 + r ∧ v = u (n * i + r)

lemma forces_cycVal_atom (hinj : Function.Injective u) (p r : ℕ) :
    u p ⊩[⟨F, cycVal n u⟩] #(8 + r) ↔ r < n ∧ p % n = r := by
  constructor;
  · rintro ⟨i, r', hr', h8, hp⟩;
    obtain rfl : r = r' := by omega;
    rw [hinj hp, Nat.mul_add_mod, Nat.mod_eq_of_lt hr'];
    exact ⟨hr', rfl⟩;
  · rintro ⟨hr, hp⟩;
    exact ⟨p / n, r, hr, rfl, congrArg u <| by rw [← hp, Nat.div_add_mod]⟩

/-- A strict chain along a transitive relation refutes `H n` at its first point.

- [Fin74a] -/
lemma cycVal_forces_neg_H (hn : 1 ≤ n) (hR : ∀ p, u p ≺ u (p + 1))
    (hinj : Function.Injective u) : u 0 ⊩[⟨F, cycVal n u⟩] ∼H n := by
  apply forces_neg_H hn hR (forces_cycVal_atom hinj);
  intro y hy;
  obtain ⟨i, r, hr, h8, rfl⟩ := (forces_ph.mp hy).1;
  obtain rfl : r = 0 := by omega;
  exact ⟨i, rfl⟩

end CycVal

/-- Every frame validating `𝐒𝟒`, `θ` and `H n` validates `∼ε`.

- [Fin74a, Lemma 1] -/
theorem validates_neg_ε_of_validates_H {F : Frame κ} (hn : 1 ≤ n) (hS4 : F ⊧ (𝐒𝟒 : NormalLogic ℕ))
    (hθ : F ⊧ θ) (hH : F ⊧ H n) : F ⊧ ∼ε := by
  obtain ⟨_, _⟩ := Frame.validates_logicS4_iff.mp hS4;
  intro V x hxE;
  have hG : θ ∈ (Model.mk F V).logic := Frame.logic_le_model_logic hθ;
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => y ≺ v ∧ v ⊀ y)
    (P := fun m y => y ⊩[⟨F, V⟩] ε⟦shift m⟧)
    (forces_ε_subst_shift.mpr <| forces_ε_iff.mp hxE) fun m y hy => by
      obtain ⟨v, Ryv, Rvy, hv⟩ := chain_step hG hy;
      exact ⟨v, ⟨Ryv, Rvy⟩, hv⟩;
  have hR : ∀ m, u m ≺ u (m + 1) := fun m => (hu m).2.1;
  have hinj := injective_of_forall_rel_succ hR fun m => (hu m).2.2;
  exact cycVal_forces_neg_H hn hR hinj <| hH (cycVal n u) (u 0)

section Chain

variable {w : M.World}

private def Y (m : ℕ) : ℕ → Formula ℕ
| 0 => ph 0
| r + 1 => ph (r + 1) ⋏ cycAux (m - 2 - r) (r + 2)

private lemma Y_imp_ph {r : ℕ} (h : x ⊩ Y m r) : x ⊩ ph r := by
  rcases r with _ | r;
  · exact h;
  · exact (forces_and.mp h).1

private lemma succ_mod_ne (hm : 2 ≤ m) (p : ℕ) : (p + 1) % m ≠ p % m := by
  have := Nat.mod_lt p (show 0 < m by omega);
  by_cases h : p % m + 1 < m;
  · rw [Nat.succ_mod_of_lt h];
    omega;
  · rw [Nat.succ_mod_of_eq (by omega)];
    omega

private lemma exists_succ_Y (hm : 2 ≤ m) (hbox : x ⊩ □(ph 0 🡒 cyc m)) (hxw : x ≺ w) (p : ℕ)
    (hw : w ⊩ Y m (p % m)) : ∃ v, w ≺ v ∧ v ⊩ Y m ((p + 1) % m) := by
  have hlt := Nat.mod_lt p (show 0 < m by omega);
  rcases hp : p % m with _ | r;
  · rw [hp] at hw;
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩;
    rw [Nat.succ_mod_of_lt (by omega), hp];
    exact forces_dia.mp (forces_imp.mp (forces_box.mp hbox w hxw) |>.resolve_left (not_not.mpr hw));
  · rw [hp] at hw hlt;
    obtain ⟨hw₁, hw₂⟩ := forces_and.mp hw;
    by_cases h : r + 2 < m;
    · obtain ⟨j, hj⟩ : ∃ j, m - 2 - r = j + 1 := ⟨m - 3 - r, by omega⟩;
      rw [hj, cycAux] at hw₂;
      obtain ⟨v, hwv, hv⟩ := forces_dia.mp hw₂;
      rw [Nat.succ_mod_of_lt (by omega), hp];
      use v, hwv;
      rw [Y, show m - 2 - (r + 1) = j by omega];
      exact hv;
    · rw [show m - 2 - r = 0 by omega, cycAux] at hw₂;
      obtain ⟨v, hwv, hv⟩ := forces_dia.mp hw₂;
      rw [Nat.succ_mod_of_eq (by omega)];
      exact ⟨v, hwv, hv⟩

/-- A refutation of `H m` yields an infinite strict chain cycling through the `m` phases.

- [Fin74a, p. 28] -/
lemma exists_ph_chain [Std.Refl M.Rel] [IsTrans _ M.Rel]
    (hanti : ∀ ⦃x y : M.World⦄, x ≺ y → y ≺ x → x = y) (hm : 2 ≤ m) (h : x ⊮ H m) :
    ∃ u : ℕ → M.World, (∀ p, u p ≺ u (p + 1)) ∧ (∀ p, u (p + 1) ⊀ u p) ∧
      ∀ p, u p ⊩ ph (p % m) := by
  obtain ⟨hxs, hbox⟩ := forces_and.mp (not_forces_neg.mp h);
  have h₀ : x ⊩ Y m (0 % m) := by
    rw [Nat.zero_mod];
    exact hxs;
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun w v => w ≺ v ∧ v ⊀ w)
    (P := fun p w => x ≺ w ∧ w ⊩ Y m (p % m)) ⟨Frame.rel_refl x, h₀⟩ <| by
      intro p w hw;
      obtain ⟨v, hwv, hv⟩ := exists_succ_Y hm hbox hw.1 p hw.2;
      have hvw : v ⊀ w := by
        intro hvw;
        obtain rfl := hanti hwv hvw;
        exact ph_incompatible (succ_mod_ne hm p) (Y_imp_ph hv) (Y_imp_ph hw.2);
      exact ⟨v, ⟨hwv, hvw⟩, Frame.rel_trans hw.1 hwv, hv⟩;
  exact ⟨u, fun p => (hu p).2.1, fun p => (hu p).2.2, fun p => Y_imp_ph (hu p).1.2⟩

end Chain

lemma atoms_β_γ_lt (m : ℕ) : (∀ a ∈ (β m).atoms, a < 6) ∧ (∀ a ∈ (γ m).atoms, a < 6) :=
  match m with
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    obtain ⟨h₁, h₂⟩ := atoms_β_γ_lt (m + 1);
    obtain ⟨h₃, h₄⟩ := atoms_β_γ_lt m;
    constructor <;> simp <;> grind

lemma atoms_ε_lt : ∀ a ∈ ε.atoms, a < 6 := by
  simp only [ε, δ, α, ι, ι₁, ι₂, ι₃, ι₄];
  simp

end Fine

/-- The valuation of the periodic model: that of `fineModel`, together with `#(8 + r)` true at the
`d_j` with `j ≡ r (mod 2n)`, for `r < 2n`.

- [Fin74a] -/
def periodicVal (n : ℕ) (w : fineFrame.World) (i : ℕ) : Prop :=
  fineModel.val w i ∨ ∃ j r, w = fineFrame.d j ∧ r < 2 * n ∧ i = 8 + r ∧ j % (2 * n) = r

/-- Fine's frame with the valuation `periodicVal n`.

- [Fin74a] -/
abbrev periodicModel (n : ℕ) : Model fineFrame.World ℕ := ⟨fineFrame, periodicVal n⟩

namespace periodicModel

open Fine fineFrame Model.World

variable {n m i j : ℕ}

lemma forces_atom_d_iff {a : ℕ} :
    d i ⊩[periodicModel n] #a ↔
      (a = 0 ∧ i % 2 = 0) ∨ (a = 1 ∧ i % 2 = 1) ∨ ∃ r, r < 2 * n ∧ a = 8 + r ∧ i % (2 * n) = r := by
  simp [periodicVal];
  tauto

lemma forces_atom_phase_d_iff {r : ℕ} :
    d i ⊩[periodicModel n] #(8 + r) ↔ r < 2 * n ∧ i % (2 * n) = r := by
  rw [forces_atom_d_iff];
  constructor;
  · rintro (h | h | ⟨r', hr', h8, hi⟩);
    · omega;
    · omega;
    · obtain rfl : r = r' := by omega;
      exact ⟨hr', hi⟩;
  · exact fun ⟨hr, hi⟩ => Or.inr <| Or.inr ⟨r, hr, rfl, hi⟩

/-- Past some threshold, the truth of `A` at `d_i` depends only on `i` modulo `2n`.

- [Fin74a, p. 28] -/
lemma d_eventually_periodic (A : Formula ℕ) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → i % (2 * n) = j % (2 * n) →
      (d i ⊩[periodicModel n] A ↔ d j ⊩[periodicModel n] A) := by
  induction A with
  | atom a =>
    use 0;
    intro i j _ _ hij;
    have hp : i % 2 = j % 2 := by
      rw [← Nat.mod_mod_of_dvd i (dvd_mul_right 2 n), hij,
        Nat.mod_mod_of_dvd j (dvd_mul_right 2 n)];
    simp only [forces_atom_d_iff, hp, hij]
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
    obtain ⟨N1, hN1⟩ := exists_ge_eventually_const (fun k => d k ⊩[periodicModel n] B);
    obtain ⟨N2, hN2⟩ := exists_ge_eventually_const (fun m => a m ⊩[periodicModel n] B);
    use max N1 N2;
    intro i j hi hj _;
    rw [forces_dia_d_iff, forces_dia_d_iff (i := j), hN1 i j (by omega) (by omega),
      hN2 i j (by omega) (by omega)]

/-- `d_0` forces `ε` in the periodic model.

- [Fin74a] -/
lemma forces_ε_d0 : d 0 ⊩[periodicModel n] ε := by
  apply (forces_congr_of_atoms (M := fineModel) (V := periodicVal n) _).mp fineModel.forces_ε_d0;
  intro a ha w;
  have := atoms_ε_lt a ha;
  constructor;
  · exact Or.inl;
  · rintro (h | ⟨_, r, _, _, h8, _⟩);
    · exact h;
    · omega

/-- `d_0` refutes `H (2n)` in the periodic model.

- [Fin74a] -/
lemma not_forces_H_d0 (hn : 1 ≤ n) : d 0 ⊮[periodicModel n] H (2 * n) := by
  apply forces_neg.mp;
  apply forces_neg_H (u := d) (by omega) (fun p => by simp) (fun p r => forces_atom_phase_d_iff);
  intro y hy;
  have h := (forces_ph.mp hy).1;
  cases y using casesOn with
  | d k =>
    obtain ⟨_, hk⟩ := forces_atom_phase_d_iff.mp h;
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hk;
    exact ⟨c, by rw [← hc]⟩;
  | _ => simp [periodicVal] at h

lemma d_eventually_periodic_family (s : ℕ → Formula ℕ) (m : ℕ) :
    ∃ N : ℕ, ∀ r < m, ∀ i j : ℕ, N ≤ i → N ≤ j → i % (2 * n) = j % (2 * n) →
      (d i ⊩[periodicModel n] s r ↔ d j ⊩[periodicModel n] s r) := by
  induction m with
  | zero => exact ⟨0, fun r hr => by omega⟩
  | succ m ih =>
    obtain ⟨N₁, h₁⟩ := ih;
    obtain ⟨N₂, h₂⟩ := d_eventually_periodic (n := n) (s m);
    use max N₁ N₂;
    intro r hr i j hi hj hij;
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl;
    · exact h₁ r hr i j (by omega) (by omega) hij;
    · exact h₂ i j (by omega) (by omega) hij

/-- An infinite strict chain in Fine's frame is a strictly increasing sequence of `d`-points. -/
lemma exists_strictMono_d {u : ℕ → fineFrame.World} (hR : ∀ p, u p ≺ u (p + 1))
    (hs : ∀ p, u (p + 1) ⊀ u p) : ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ p, u p = d (k p) := by
  choose k hk using fun p => strict_chain_all_d hR hs p;
  use k;
  constructor;
  · apply strictMono_nat_of_lt_succ;
    intro p;
    have h₁ := hR p;
    have h₂ := hs p;
    rw [hk p, hk (p + 1)] at h₁ h₂;
    simp at h₁ h₂;
    omega;
  · exact hk

/-- Fine's frame with the valuation `w ↦ {a | w ⊩ σ a}` in the periodic model. -/
abbrev substModel (n : ℕ) (σ : Formula.Substitution ℕ ℕ) : Model fineFrame.World ℕ :=
  ⟨fineFrame, fun w a => w ⊩[periodicModel n] σ a⟩

/-- `H m` is strongly valid in the periodic model for `2n < m`.

- [Fin74a, p. 28] -/
theorem H_mem_logic (hn : 1 ≤ n) (hm : 2 * n < m) : H m ∈ (periodicModel n).logic := by
  apply Model.mem_logic.mpr;
  intro σ x;
  by_contra hx;
  obtain ⟨u, hR, hs, hu⟩ := exists_ph_chain (M := substModel n σ) (fun _ _ => rel_antisymm)
    (by omega) ((forces_subst σ).not.mp hx);
  obtain ⟨k, hkmono, hk⟩ := exists_strictMono_d hR hs;
  have hphase : ∀ p, d (k p) ⊩[periodicModel n] (ph (p % m))⟦σ⟧ := by
    intro p;
    have := hu p;
    rw [hk p] at this;
    exact (forces_subst σ).mpr this;
  obtain ⟨N, hN⟩ := d_eventually_periodic_family (n := n) (fun r => (ph r)⟦σ⟧) m;
  obtain ⟨r, hr, r', hr', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range m) (t := Finset.range (2 * n)) (f := fun r => k (m * N + r) % (2 * n))
    (by simpa using hm) (fun r _ => Finset.mem_range.mpr (Nat.mod_lt _ (show 0 < 2 * n by omega)));
  simp only [Finset.mem_range] at hr hr';
  have hN₁ : N ≤ k (m * N + r) :=
    le_trans (by have := Nat.le_mul_of_pos_left N (show 0 < m by omega); omega)
      hkmono.le_apply;
  have hN₂ : N ≤ k (m * N + r') :=
    le_trans (by have := Nat.le_mul_of_pos_left N (show 0 < m by omega); omega)
      hkmono.le_apply;
  have h₁ := hphase (m * N + r);
  have h₂ := (hN r' hr' _ _ hN₁ hN₂ heq).mpr
    (by simpa [Nat.mod_eq_of_lt hr'] using hphase (m * N + r'));
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr] at h₁;
  exact ph_incompatible hne ((forces_subst σ).mp h₁) ((forces_subst σ).mp h₂)

end periodicModel

universe u

open Fine in
/-- The normal extension `𝐒𝟒 ⊕ ∼ε` of `𝐒𝟒` by the negation of Fine's formula `ε`.

- [Fin74a]
- [CZ98, Problem 10.5] -/
abbrev logicS4NegEpsilon : NormalLogic ℕ := 𝐒𝟒 + ({∼ε} : FormulaSet ℕ)

lemma logicS4_le_periodicModel_logic {n : ℕ} : (𝐒𝟒 : NormalLogic ℕ) ≤ (periodicModel n).logic :=
  fun _ h => Frame.logic_le_model_logic (Frame.validates_logicS4 _ h)

instance {n : ℕ} : (periodicModel n).logic.IsNExt 𝐒𝟒 := ⟨logicS4_le_periodicModel_logic⟩

/-- The intersection of `𝐒𝟒 ⊕ ∼ε` with the logic of the periodic model of period `2n`.

- [Fin74a] -/
abbrev fineCompanion (n : ℕ) : NormalLogic ℕ := logicS4NegEpsilon ∩ (periodicModel n).logic

open Fine Model.World in
/-- The frames validating `𝐒𝟒 ⊕ ∼ε` are those validating `fineCompanion n`.

- [Fin74a]
- [CZ98, Problem 10.5] -/
theorem frameEquiv_logicS4NegEpsilon_fineCompanion {n : ℕ} (hn : 1 ≤ n) :
    logicS4NegEpsilon ≊[fun _ _ => True] fineCompanion n := by
  intro κ F _;
  constructor;
  · intro h φ hφ;
    exact h φ hφ.1;
  · intro h;
    rw [Frame.validateLogic_iff_forall_pointGenerate];
    intro x;
    rcases Frame.validates_inter_of_isRooted_of_infinite Frame.isRooted_pointGenerate
      (Frame.ValidateLogic.pointGenerate (x := x) h) with h' | h';
    · exact h';
    · have hS4 : F⥜x ⊧ (𝐒𝟒 : NormalLogic ℕ) :=
        fun φ hφ => h' φ (logicS4_le_periodicModel_logic hφ);
      have hθ : F⥜x ⊧ θ :=
        h' θ (Frame.logic_le_model_logic (V := periodicVal n) fineFrame.validates_θ);
      have hH : F⥜x ⊧ H (2 * n + 1) := h' _ (periodicModel.H_mem_logic hn (by omega));
      have hneg := validates_neg_ε_of_validates_H (by omega) hS4 hθ hH;
      exact Frame.validates_add hS4 (by rintro φ rfl; exact hneg)

open Fine Model.World in
lemma imp_H_mem_fineCompanion {n m : ℕ} (hn : 1 ≤ n) (hm : 2 * n < m) :
    ε 🡒 H m ∈ fineCompanion n := by
  constructor;
  · exact NormalLogic.mem_mdp (NormalLogic.mem_add rfl) NormalLogic.neg_efq;
  · exact NormalLogic.imp_of_mem (periodicModel.H_mem_logic hn hm)

open Fine Model.World in
lemma imp_H_not_mem_fineCompanion {n : ℕ} (hn : 1 ≤ n) : ε 🡒 H (2 * n) ∉ fineCompanion n := by
  intro h;
  exact periodicModel.not_forces_H_d0 hn <|
    Model.validates_of_mem_logic h.2 (fineFrame.d 0) periodicModel.forces_ε_d0

/-- The logics `fineCompanion n` are pairwise distinct.

- [Fin74a] -/
lemma fineCompanion_injOn : Set.InjOn (fun n => fineCompanion (n + 1)) Set.univ := by
  have key : ∀ a b : ℕ, a < b → fineCompanion (a + 1) ≠ fineCompanion (b + 1) := by
    intro a b hab h;
    apply imp_H_not_mem_fineCompanion (n := b + 1) (by omega);
    rw [← h];
    exact imp_H_mem_fineCompanion (by omega) (by omega);
  intro a _ b _ h;
  rcases lt_trichotomy a b with hab | rfl | hab;
  · exact (key a b hab h).elim;
  · rfl;
  · exact (key b a hab h.symm).elim

/-- The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε` in `NExt 𝐒𝟒` is at least `ℵ₀`.

- [Fin74a]
- [CZ98, §10.5]
- [CZ98, Problem 10.5] -/
theorem aleph0_le_degree_logicS4NegEpsilon :
    Cardinal.aleph0 ≤ logicS4NegEpsilon.degree 𝐒𝟒 (fun _ _ => True) := by
  rw [NormalLogic.degree, ← Cardinal.mk_nat];
  apply Cardinal.mk_le_of_injective
    (f := fun n : ℕ => (⟨fineCompanion (n + 1), inferInstance,
      frameEquiv_logicS4NegEpsilon_fineCompanion (by omega)⟩ :
        logicS4NegEpsilon.Companion 𝐒𝟒 fun _ _ => True));
  intro a b h;
  exact fineCompanion_injOn trivial trivial (congrArg Subtype.val h)

/-- The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε` in `NExt 𝐊𝟒` is at least `ℵ₀`.

- [Fin74a]
- [CZ98, §10.5]
- [CZ98, Problem 10.5] -/
theorem aleph0_le_degree_logicS4NegEpsilon_logicK4 :
    Cardinal.aleph0 ≤ logicS4NegEpsilon.degree 𝐊𝟒 (fun _ _ => True) :=
  aleph0_le_degree_logicS4NegEpsilon.trans NormalLogic.degree_le_degree_of_isNExt

end Modal

end
