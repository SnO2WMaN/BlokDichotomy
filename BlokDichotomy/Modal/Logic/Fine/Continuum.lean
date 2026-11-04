module

public import BlokDichotomy.Modal.Logic.Fine.Coding
public import BlokDichotomy.Modal.Logic.Fine.Degree
public import BlokDichotomy.Modal.Logic.Fine.Pin
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε'`

For each set `I` of natural numbers, we endow the coding frame with a valuation which makes the
formulas `ε' → ◇η_i` valid, in the strong sense, exactly for `i ∈ I`. This yields continuum many
pairwise distinct frame companions of `𝐒𝟒 ⊕ ∼ε'`.

## References

- [Fin74a]
- [CZ98, §10.5, Problem 10.5]
-/

@[expose] public section

namespace Modal

namespace Fine

open Formula

/-- The coding formula `ε' → ◇η_i`, strongly valid in the coding model exactly when `i ∈ I`.

- [Fin74a] -/
def φCode (i : ℕ) : Formula ℕ := ε' 🡒 ◇(η i)

end Fine

/-- The valuation of the coding model: that of Fine's model on the points `a_m`, `b_m`, `c_m` and
`d_m`, and no atom true at the points `t_m`.

- [Fin74a, p. 25] -/
def codingVal (I : Set ℕ) : (codingFrame I).World → ℕ → Prop
| codingFrame.b 0, 2 => True
| codingFrame.b 1, 3 => True
| codingFrame.c 0, 4 => True
| codingFrame.c 1, 5 => True
| codingFrame.d n, 0 => n % 2 = 0
| codingFrame.d n, 1 => n % 2 = 1
| _, _ => False

/-- The coding frame with the valuation `codingVal I`.

- [Fin74a, p. 25] -/
abbrev codingModel (I : Set ℕ) : Model (codingFrame I).World ℕ := ⟨codingFrame I, codingVal I⟩

namespace codingModel

open Fine codingFrame Model.World

variable {I : Set ℕ} {x : (codingFrame I).World} {m i j n : ℕ}

@[simp] lemma val_a {i : ℕ} : ¬ codingVal I (a m) i := by simp [codingVal]
@[simp] lemma val_t {i : ℕ} : ¬ codingVal I (t m) i := by simp [codingVal]
@[simp] lemma val_b_iff : codingVal I (b m) i ↔ (m = 0 ∧ i = 2) ∨ (m = 1 ∧ i = 3) := by
  rcases m with _ | _ | m <;> rcases i with _ | _ | _ | _ | i <;> simp [codingVal];
@[simp] lemma val_c_iff : codingVal I (c m) i ↔ (m = 0 ∧ i = 4) ∨ (m = 1 ∧ i = 5) := by
  rcases m with _ | _ | m <;> rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [codingVal];
@[simp] lemma val_d_iff : codingVal I (d n) i ↔ (i = 0 ∧ n % 2 = 0) ∨ (i = 1 ∧ n % 2 = 1) := by
  rcases i with _ | _ | i <;> simp [codingVal];

@[simp high] lemma forces_atom_0_iff : x ⊩[codingModel I] #0 ↔ ∃ k, x = d k ∧ k % 2 = 0 := by
  cases x using casesOn <;> simp;
@[simp high] lemma forces_atom_1_iff : x ⊩[codingModel I] #1 ↔ ∃ k, x = d k ∧ k % 2 = 1 := by
  cases x using casesOn <;> simp;
@[simp high] lemma forces_atom_2_iff : x ⊩[codingModel I] #2 ↔ x = b 0 := by
  cases x using casesOn <;> simp;
@[simp high] lemma forces_atom_3_iff : x ⊩[codingModel I] #3 ↔ x = b 1 := by
  cases x using casesOn <;> simp;
@[simp high] lemma forces_atom_4_iff : x ⊩[codingModel I] #4 ↔ x = c 0 := by
  cases x using casesOn <;> simp;
@[simp high] lemma forces_atom_5_iff : x ⊩[codingModel I] #5 ↔ x = c 1 := by
  cases x using casesOn <;> simp;

/-- `β_2` is forced exactly at `b_2`. -/
lemma forces_β₂_iff (w : (codingFrame I).World) : w ⊩[codingModel I] β 2 ↔ w = b 2 := by
  rw [β_add_two, forces_and, forces_and, forces_neg];
  simp only [Nat.zero_add, β_one, γ_zero, γ_one, forces_dia, forces_atom_3_iff, forces_atom_4_iff,
    forces_atom_5_iff, NotForces, exists_eq_right];
  cases w using casesOn <;> simp <;> omega;

/-- `γ_2` is forced exactly at `c_2`. -/
lemma forces_γ₂_iff (w : (codingFrame I).World) : w ⊩[codingModel I] γ 2 ↔ w = c 2 := by
  rw [γ_add_two, forces_and, forces_and, forces_neg];
  simp only [Nat.zero_add, β_zero, β_one, γ_one, forces_dia, forces_atom_2_iff, forces_atom_3_iff,
    forces_atom_5_iff, NotForces, exists_eq_right];
  cases w using casesOn <;> simp <;> omega;

/-- `d_0` forces `δ`. -/
lemma forces_δ_d0 : d 0 ⊩[codingModel I] δ := by
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
      · exact Or.inl (by omega);
    | _ => simp [NotForces]
  · rintro w -;
    rw [forces_imp, forces_and, forces_neg, forces_dia];
    cases w using casesOn with
    | d k =>
      simp only [NotForces, forces_atom_0_iff, forces_atom_1_iff,
        ↓existsAndEq, rel_d_d, true_and, d, Prod.mk.injEq];
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk;
      · exact Or.inl (by omega);
      · exact Or.inr ⟨by omega, k + 1, by omega, by omega⟩;
    | _ => simp [NotForces]
  · rintro w -;
    rw [forces_imp, forces_box];
    cases w using casesOn with
    | d k =>
      left;
      rw [not_forces_neg, forces_or];
      simp;
      omega;
    | _ =>
      right;
      intro z hz;
      rw [forces_neg, not_forces_or];
      cases z using casesOn <;> simp [NotForces] at hz ⊢;

/-- `α_0` is forced at `a_0`. -/
lemma forces_α₀_a0 : a 0 ⊩[codingModel I] α 0 := by
  rw [α, forces_and, forces_and, forces_and, forces_neg, forces_neg];
  simp only [Nat.zero_add, β_one, γ_one, forces_dia, forces_atom_3_iff, forces_atom_5_iff,
    forces_β₂_iff, forces_γ₂_iff, NotForces, exists_eq_right];
  simp;

/-- `◇(α_0)` is forced at `d_0`. -/
lemma forces_dia_α₀_d0 : d 0 ⊩[codingModel I] ◇(α 0) :=
  forces_dia.mpr ⟨a 0, by simp, forces_α₀_a0⟩

/-- `d_0` forces `ι 0`. -/
lemma forces_ι₀_d0 : d 0 ⊩[codingModel I] ι 0 := by
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
    simp [forces_dia, NotForces];

/-- `d_0` forces `ε`. -/
lemma forces_ε_d0 : d 0 ⊩[codingModel I] ε :=
  forces_ε_iff.mpr ⟨forces_δ_d0, forces_dia_α₀_d0, forces_ι₀_d0⟩

/-- `d_0` forces `pin`. -/
lemma forces_pin_d0 : d 0 ⊩[codingModel I] pin := by
  rw [forces_pin_iff];
  and_intros;
  · rw [forces_box];
    rintro w - hw;
    rw [forces_atom_2_iff] at hw;
    subst hw;
    rw [forces_box];
    rintro z hz;
    cases z using casesOn <;> simp_all;
  · rw [forces_box];
    rintro w - hw;
    rw [forces_atom_4_iff] at hw;
    subst hw;
    rw [forces_box];
    rintro z hz;
    cases z using casesOn <;> simp_all;
  all_goals
    rw [forces_box];
    rintro w -;
    rw [forces_neg];
    intro h;
    obtain ⟨h₁, h₂⟩ := forces_and.mp h;
    simp only [forces_atom_2_iff, forces_atom_3_iff, forces_atom_4_iff, forces_atom_5_iff] at h₁ h₂;
    simp [h₁] at h₂;

/-- `d_0` forces `ε'`. -/
lemma forces_ε'_d0 : d 0 ⊩[codingModel I] ε' :=
  forces_ε'_iff.mpr ⟨forces_ε_d0, forces_pin_d0⟩

end codingModel

namespace codingFrame

open Fine Model.World

variable {I : Set ℕ} {V : (codingFrame I).World → ℕ → Prop} {x : (codingFrame I).World} {m i : ℕ}

lemma pinData_of_forces_εPin (h : x ⊩[⟨codingFrame I, V⟩] εPin m) : PinData I V x m := by
  obtain ⟨hδ, hα, hι, hP⟩ := forces_εPin_iff.mp h;
  obtain ⟨h₂, h₄, h₂₄, h₂₃, h₄₅, h₂₅, h₄₃⟩ := forces_pin_iff.mp hP;
  exact ⟨hδ, hα, hι, h₂, h₄, h₂₄, h₂₃, h₄₅, h₂₅, h₄₃⟩;

/-- The successors of `d_i` are the `d_k` and `a_k` with `i ≤ k`, the `t_k` with `k ∈ I` and
`i ≤ k`, and all `b`- and `c`-points. -/
lemma forces_dia_d_iff {A : Formula ℕ} :
    d i ⊩[⟨codingFrame I, V⟩] ◇A ↔
      (∃ k, i ≤ k ∧ (d k ⊩[⟨codingFrame I, V⟩] A)) ∨
      (∃ m, i ≤ m ∧ (a m ⊩[⟨codingFrame I, V⟩] A)) ∨
      (∃ k, i ≤ k ∧ k ∈ I ∧ (t k ⊩[⟨codingFrame I, V⟩] A)) ∨
      (∃ k, (b k ⊩[⟨codingFrame I, V⟩] A)) ∨ (∃ k, (c k ⊩[⟨codingFrame I, V⟩] A)) := by
  rw [forces_dia];
  constructor;
  · rintro ⟨y, hy, hyA⟩;
    cases y using casesOn with
    | d k => exact Or.inl ⟨k, hy, hyA⟩
    | a m => exact Or.inr <| Or.inl ⟨m, hy, hyA⟩
    | t k => exact Or.inr <| Or.inr <| Or.inl ⟨k, hy.2, hy.1, hyA⟩
    | b k => exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨k, hyA⟩
    | c k => exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨k, hyA⟩
  · rintro (⟨k, hk, hA⟩ | ⟨m, hm, hA⟩ | ⟨k, hik, hk, hA⟩ | ⟨k, hA⟩ | ⟨k, hA⟩);
    · exact ⟨d k, hk, hA⟩;
    · exact ⟨a m, hm, hA⟩;
    · exact ⟨t k, ⟨hk, hik⟩, hA⟩;
    · exact ⟨b k, trivial, hA⟩;
    · exact ⟨c k, trivial, hA⟩;

/-- An infinite strict chain in the coding frame is a strictly increasing sequence of
`d`-points. -/
lemma exists_strictMono_d {u : ℕ → (codingFrame I).World} (hR : ∀ p, u p ≺ u (p + 1))
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
  · exact hk;

/-- The coding frame validates every `θPin m`.

- [Fin74a] -/
theorem validates_θPin : codingFrame I ⊧ θPin m := by
  intro V x hx;
  have hP := pinData_of_forces_εPin hx;
  obtain ⟨k, rfl, hk⟩ := hP.exists_d_le;
  have hk' : k ≤ m + 1 := hk.trans (Nat.le_succ m);
  apply forces_ψ_subst_shift.mpr;
  use d (m + 1);
  and_intros;
  · simpa using hk';
  · exact hP.forces_p01 rfl hk';
  · rw [forces_neg];
    rintro ⟨z, hz, hzα⟩;
    have hz' : d k ≺ z := Frame.rel_trans (by simpa using hk') hz;
    rcases (hP.forces_α_iff_of_pin m hz').mp hzα with rfl | ⟨h₁, h₂, rfl⟩;
    · simp at hz;
    · simp at hz;
      omega;
  · apply forces_dia.mpr;
    use a (m + 1);
    and_intros;
    · simp;
    · exact (hP.forces_α_iff_of_pin (m + 1) (by simpa using hk')).mpr (Or.inl rfl);

/-- The coding frame validates `ε' → ◇η_i` for `i ∈ I`.

- [Fin74a] -/
theorem validates_φCode (hi : i ∈ I) : codingFrame I ⊧ φCode i := by
  intro V x hx;
  have hP := pinData_of_forces_εPin (m := 0) hx;
  obtain ⟨k, rfl, hk⟩ := hP.exists_d_le;
  have hd : d k ≺ t i := rel_d_t.mpr ⟨hi, hk.trans (Nat.zero_le i)⟩;
  exact forces_dia.mpr ⟨t i, hd, (hP.forces_η_iff_of_pin i hd).mpr ⟨hi, rfl⟩⟩;

end codingFrame

namespace codingModel

open Fine codingFrame Model.World

variable {I : Set ℕ} {m i : ℕ}

/-- Past some threshold, the truth of `A` at `d_i` in the coding model depends only on the parity
of `i`.

- [Fin74a, p. 28] -/
lemma d_eventually_periodic (A : Formula ℕ) :
    ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → i % 2 = j % 2 →
      (d i ⊩[codingModel I] A ↔ d j ⊩[codingModel I] A) := by
  induction A with
  | atom a =>
    use 0;
    intro i j _ _ hij;
    rcases a with _ | _ | a <;> simp [hij];
  | falsum =>
    use 0;
    intro i j _ _ _;
    simp [Forces];
  | imp B C ihB ihC =>
    obtain ⟨NA, hNA⟩ := ihB;
    obtain ⟨NB, hNB⟩ := ihC;
    use max NA NB;
    intro i j hi hj hij;
    simp only [forces_imp, NotForces, hNA i j (by omega) (by omega) hij,
      hNB i j (by omega) (by omega) hij];
  | dia B ih =>
    obtain ⟨N1, hN1⟩ := exists_ge_eventually_const (fun k => d k ⊩[codingModel I] B);
    obtain ⟨N2, hN2⟩ := exists_ge_eventually_const (fun m => a m ⊩[codingModel I] B);
    obtain ⟨N3, hN3⟩ := exists_ge_eventually_const (fun k => k ∈ I ∧ t k ⊩[codingModel I] B);
    use max N1 (max N2 N3);
    intro i j hi hj _;
    rw [forces_dia_d_iff, forces_dia_d_iff (i := j), hN1 i j (by omega) (by omega),
      hN2 i j (by omega) (by omega), hN3 i j (by omega) (by omega)];

lemma d_eventually_periodic_family (s : ℕ → Formula ℕ) (m : ℕ) :
    ∃ N : ℕ, ∀ r < m, ∀ i j : ℕ, N ≤ i → N ≤ j → i % 2 = j % 2 →
      (d i ⊩[codingModel I] s r ↔ d j ⊩[codingModel I] s r) := by
  induction m with
  | zero => exact ⟨0, fun r hr => by omega⟩
  | succ m ih =>
    obtain ⟨N₁, h₁⟩ := ih;
    obtain ⟨N₂, h₂⟩ := d_eventually_periodic (I := I) (s m);
    use max N₁ N₂;
    intro r hr i j hi hj hij;
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl;
    · exact h₁ r hr i j (by omega) (by omega) hij;
    · exact h₂ i j (by omega) (by omega) hij;

/-- The coding frame with the valuation `w ↦ {a | w ⊩ σ a}` in the coding model. -/
abbrev substModel (I : Set ℕ) (σ : Formula.Substitution ℕ ℕ) : Model (codingFrame I).World ℕ :=
  ⟨codingFrame I, fun w a => w ⊩[codingModel I] σ a⟩

/-- `H m` is strongly valid in the coding model for `2 < m`.

- [Fin74a, p. 28] -/
theorem H_mem_logic (hm : 2 < m) : H m ∈ (codingModel I).logic := by
  apply Model.mem_logic.mpr;
  intro σ x;
  by_contra hx;
  obtain ⟨u, hR, hs, hu⟩ := exists_ph_chain (M := substModel I σ) (fun _ _ => rel_antisymm)
    (by omega) ((forces_subst σ).not.mp hx);
  obtain ⟨k, hkmono, hk⟩ := exists_strictMono_d hR hs;
  have hphase : ∀ p, d (k p) ⊩[codingModel I] (ph (p % m))⟦σ⟧ := by
    intro p;
    have := hu p;
    rw [hk p] at this;
    exact (forces_subst σ).mpr this;
  obtain ⟨N, hN⟩ := d_eventually_periodic_family (I := I) (fun r => (ph r)⟦σ⟧) m;
  obtain ⟨r, hr, r', hr', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range m) (t := Finset.range 2) (f := fun r => k (m * N + r) % 2)
    (by simpa using hm) (fun r _ => Finset.mem_range.mpr (Nat.mod_lt _ (by omega)));
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
  exact ph_incompatible hne ((forces_subst σ).mp h₁) ((forces_subst σ).mp h₂);

/-- `ε' → ◇η_i` is refuted at `d_0` in the coding model for `i ∉ I`.

- [Fin74a] -/
theorem not_forces_φCode (hi : i ∉ I) : d 0 ⊮[codingModel I] φCode i := by
  intro h;
  obtain ⟨z, hz, hzη⟩ := forces_dia.mp (h (codingModel.forces_ε'_d0));
  exact hi ((pinData_of_forces_εPin (V := codingVal I) (m := 0)
    codingModel.forces_ε'_d0).forces_η_iff_of_pin i hz |>.mp hzη).1;

end codingModel

universe u

open Fine in
/-- The normal extension `𝐒𝟒 ⊕ ∼ε'` of `𝐒𝟒` by the negation of Fine's formula `ε'`.

- [Fin74a]
- [CZ98, Problem 10.5] -/
abbrev logicS4NegEpsilonPin : NormalLogic ℕ := 𝐒𝟒 + ({∼ε'} : FormulaSet ℕ)

lemma logicS4_le_codingModel_logic {I : Set ℕ} : (𝐒𝟒 : NormalLogic ℕ) ≤ (codingModel I).logic :=
  fun _ h => Frame.logic_le_model_logic (Frame.validates_logicS4 _ h)

instance {I : Set ℕ} : (codingModel I).logic.IsNExt 𝐒𝟒 := ⟨logicS4_le_codingModel_logic⟩

/-- The intersection of `𝐒𝟒 ⊕ ∼ε'` with the logic of the coding model of `I`.

- [Fin74a] -/
abbrev codingCompanion (I : Set ℕ) : NormalLogic ℕ :=
  logicS4NegEpsilonPin ∩ (codingModel I).logic

open Fine Model.World in
/-- The frames validating `𝐒𝟒 ⊕ ∼ε'` are those validating `codingCompanion I`.

- [Fin74a]
- [CZ98, Problem 10.5] -/
theorem frameEquiv_logicS4NegEpsilonPin_codingCompanion (I : Set ℕ) :
    logicS4NegEpsilonPin ≊[fun _ _ => True] codingCompanion I := by
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
        fun φ hφ => h' φ (logicS4_le_codingModel_logic hφ);
      have hθ : ∀ m, F⥜x ⊧ θPin m := fun m =>
        h' _ (Frame.logic_le_model_logic (V := codingVal I) codingFrame.validates_θPin);
      have hH : F⥜x ⊧ H 3 := h' _ (codingModel.H_mem_logic (by omega));
      have hneg := validates_neg_ε'_of_validates_θPin_H (by omega) hS4 hθ hH;
      exact Frame.validates_add hS4 (by rintro φ rfl; exact hneg);

open Fine in
lemma φCode_mem_logic_iff {I : Set ℕ} {i : ℕ} : φCode i ∈ (codingModel I).logic ↔ i ∈ I := by
  constructor;
  · intro h;
    by_contra hi;
    exact codingModel.not_forces_φCode hi <| Model.validates_of_mem_logic h (codingFrame.d 0);
  · intro hi;
    exact Frame.logic_le_model_logic (V := codingVal I) (codingFrame.validates_φCode hi);

open Fine in
lemma φCode_mem_codingCompanion_iff {I : Set ℕ} {i : ℕ} : φCode i ∈ codingCompanion I ↔ i ∈ I := by
  rw [← φCode_mem_logic_iff (I := I)];
  constructor;
  · exact fun h => h.2;
  · intro h;
    exact ⟨NormalLogic.mem_mdp (NormalLogic.mem_add rfl) NormalLogic.neg_efq, h⟩;

/-- The logics `codingCompanion I` are pairwise distinct. -/
lemma codingCompanion_injective : Function.Injective codingCompanion := by
  intro I J h;
  ext i;
  rw [← φCode_mem_codingCompanion_iff, h, φCode_mem_codingCompanion_iff];

open Cardinal in
/-- The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε'` in `NExt 𝐒𝟒` is at least `𝔠`.

- [Fin74a]
- [CZ98, §10.5]
- [CZ98, Problem 10.5] -/
theorem continuum_le_degree_logicS4NegEpsilonPin :
    𝔠 ≤ logicS4NegEpsilonPin.degree 𝐒𝟒 (fun _ _ => True) := by
  rw [NormalLogic.degree, ← mk_set_nat];
  apply mk_le_of_injective
    (f := fun I : Set ℕ => (⟨codingCompanion I, inferInstance,
      frameEquiv_logicS4NegEpsilonPin_codingCompanion I⟩ :
        logicS4NegEpsilonPin.Companion 𝐒𝟒 fun _ _ => True));
  intro I J h;
  exact codingCompanion_injective (congrArg Subtype.val h);

open Cardinal in
/-- The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε'` in `NExt 𝐊𝟒` is at least `𝔠`.

- [Fin74a]
- [CZ98, §10.5]
- [CZ98, Problem 10.5] -/
theorem continuum_le_degree_logicS4NegEpsilonPin_logicK4 :
    𝔠 ≤ logicS4NegEpsilonPin.degree 𝐊𝟒 (fun _ _ => True) :=
  continuum_le_degree_logicS4NegEpsilonPin.trans NormalLogic.degree_le_degree_of_isNExt

open Cardinal in
/-- The degree of Kripke incompleteness of a normal logic over `ℕ` is at most `𝔠`.

- [CZ98, §10.5] -/
theorem degree_le_continuum (L L₀ : NormalLogic ℕ) (P : ⦃κ : Type u⦄ → Frame κ → Prop) :
    L.degree L₀ P ≤ 𝔠 := by
  calc
    _ ≤ Cardinal.mk (Set (Formula ℕ)) :=
      mk_le_of_injective (f := fun L' : L.Companion L₀ P => (L'.1 : Set (Formula ℕ)))
        fun _ _ h => Subtype.ext <| SetLike.coe_injective h
    _ = 2 ^ Cardinal.mk (Formula ℕ) := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero mk_le_aleph0
    _ = 𝔠 := two_power_aleph0

open Cardinal in
/-- The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε'` in `NExt 𝐒𝟒` is exactly `𝔠`.

- [Fin74a]
- [CZ98, §10.5]
- [CZ98, Problem 10.5] -/
theorem degree_logicS4NegEpsilonPin_eq_continuum :
    logicS4NegEpsilonPin.degree 𝐒𝟒 (fun _ _ => True) = 𝔠 :=
  le_antisymm (degree_le_continuum _ _ _) continuum_le_degree_logicS4NegEpsilonPin

open Cardinal in
/-- The degree of Kripke incompleteness of `𝐒𝟒 ⊕ ∼ε'` in `NExt 𝐊𝟒` is exactly `𝔠`.

- [Fin74a]
- [CZ98, §10.5]
- [CZ98, Problem 10.5] -/
theorem degree_logicS4NegEpsilonPin_logicK4_eq_continuum :
    logicS4NegEpsilonPin.degree 𝐊𝟒 (fun _ _ => True) = 𝔠 :=
  le_antisymm (degree_le_continuum _ _ _) continuum_le_degree_logicS4NegEpsilonPin_logicK4

end Modal

end
