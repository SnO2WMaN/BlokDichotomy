module

public import BlokDichotomy.Fine.ModelForcing

/-!
# Fine's frame validates `G`

Given any valuation and a point forcing `E`, the point is some `d_m`, the "V-shape" below it is
pinned (up to the `b`/`c` mirror `swap`) to an apex `a_n`, and `d_{n+1}` witnesses `F`.

## References

- [Fin74a, Lemma 2]
- [Lit04, p. 332]
-/

@[expose] public section

namespace Fine

open Model.World

variable {ψ : World → ℕ → Prop}

/-! ### The V-shape extracted from `w ⊩ E` -/

/-- The witnesses of the "V-shape" extracted from `w ⊩ E`, for an arbitrary valuation `ψ`. -/
lemma exists_V_shape {w : World} (hE : w ⊩[⟨frame, ψ⟩] E) :
    ∃ t u₀ u₁ v₀ v₁ : World,
      R w t ∧ t ⊩[⟨frame, ψ⟩] A 0 ∧
      R t u₁ ∧ R u₁ u₀ ∧
      R t v₁ ∧ R v₁ v₀ ∧
      u₁ ⊩[⟨frame, ψ⟩] B 1 ∧ u₀ ⊩[⟨frame, ψ⟩] B 0 ∧
      v₁ ⊩[⟨frame, ψ⟩] C 1 ∧ v₀ ⊩[⟨frame, ψ⟩] C 0 ∧
      ¬ R u₀ u₁ ∧ ¬ R v₀ v₁ ∧
      ¬ R u₁ v₀ ∧ ¬ R v₁ u₀ := by
  obtain ⟨-, hA0, hK⟩ := forces_E_iff.mp hE;
  obtain ⟨t, hwt, htA0⟩ := forces_dia.mp hA0;
  obtain ⟨htB1, htC1, -, -⟩ := forces_A_iff.mp htA0;
  obtain ⟨hK1, hK2, hK3, hK4⟩ := forces_K_iff.mp hK;
  obtain ⟨u₁, htu1, hu1B1⟩ := forces_dia.mp htB1;
  obtain ⟨v₁, htv1, hv1C1⟩ := forces_dia.mp htC1;
  obtain ⟨hu1B0, hu1nC0⟩ := forces_and.mp (forces_box.mp hK1 u₁ (R_trans hwt htu1) hu1B1);
  obtain ⟨u₀, hu1u0, hu0B0⟩ := forces_dia.mp hu1B0;
  obtain ⟨hv1C0, hv1nB0⟩ := forces_and.mp (forces_box.mp hK2 v₁ (R_trans hwt htv1) hv1C1);
  obtain ⟨v₀, hv1v0, hv0C0⟩ := forces_dia.mp hv1C0;
  have hu0nB1 := forces_box.mp hK3 u₀ (R_trans (R_trans hwt htu1) hu1u0) hu0B0;
  have hv0nC1 := forces_box.mp hK4 v₀ (R_trans (R_trans hwt htv1) hv1v0) hv0C0;
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

/-- A point forcing `∼◇φ` sees no point forcing `φ`. -/
private lemma false_of_neg_dia {x y : World} {φ : Formula ℕ} (hn : x ⊩[⟨frame, ψ⟩] ∼◇φ)
    (hxy : R x y) (hy : y ⊩[⟨frame, ψ⟩] φ) : False :=
  forces_neg.mp hn (forces_dia.mpr ⟨y, hxy, hy⟩)

/-! ### Confinement of forced points to `d`-points -/

/-- One guard conjunct of `D` produces a strict successor forcing the other atom. -/
private lemma exists_rel_of_guard {y : World} {p q : Formula ℕ}
    (hg : y ⊩[⟨frame, ψ⟩] p 🡒 (∼q ⋏ ◇q)) (hp : y ⊩[⟨frame, ψ⟩] p) :
    ∃ z, R y z ∧ ¬ R z y ∧ z ⊩[⟨frame, ψ⟩] q := by
  obtain ⟨hnq, hq⟩ := forces_and.mp (hg hp);
  obtain ⟨z, hyz, hz⟩ := forces_dia.mp hq;
  use z, hyz;
  and_intros;
  · by_contra hzy;
    obtain rfl := R_antisymm hyz hzy;
    exact forces_neg.mp hnq hz;
  · exact hz

/-- `D`'s two guard conjuncts drive an infinite, strictly ascending chain of points forced
into the cone of `w`, alternating between `p0` and `p1`. -/
private lemma exists_p01_chain {w : World} (hD : w ⊩[⟨frame, ψ⟩] D) :
    ∃ u : ℕ → World, u 0 = w ∧
      ∀ i, R (u i) (u (i + 1)) ∧ ¬ R (u (i + 1)) (u i) ∧
        R w (u i) ∧ u i ⊩[⟨frame, ψ⟩] (p0 ⋎ p1) := by
  obtain ⟨hp01, hbox₁, hbox₂, -⟩ := forces_D_iff.mp hD;
  have step : ∀ y : World, R w y → y ⊩[⟨frame, ψ⟩] (p0 ⋎ p1) →
      ∃ v, R y v ∧ ¬ R v y ∧ R w v ∧ v ⊩[⟨frame, ψ⟩] (p0 ⋎ p1) := by
    intro y hwy hy;
    rcases forces_or.mp hy with hy₀ | hy₁;
    · obtain ⟨z, hyz, hzy, hz⟩ := exists_rel_of_guard (forces_box.mp hbox₁ y hwy) hy₀;
      exact ⟨z, hyz, hzy, R_trans hwy hyz, forces_or.mpr (Or.inr hz)⟩;
    · obtain ⟨z, hyz, hzy, hz⟩ := exists_rel_of_guard (forces_box.mp hbox₂ y hwy) hy₁;
      exact ⟨z, hyz, hzy, R_trans hwy hyz, forces_or.mpr (Or.inl hz)⟩;
  obtain ⟨u, hu₀, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => R y v ∧ ¬ R v y)
    (P := fun _ y => R w y ∧ y ⊩[⟨frame, ψ⟩] (p0 ⋎ p1)) ⟨R_refl w, hp01⟩ <| by
      rintro - y ⟨hwy, hy⟩;
      obtain ⟨v, hyv, hvy, hwv, hv⟩ := step y hwy hy;
      exact ⟨v, ⟨hyv, hvy⟩, hwv, hv⟩;
  use u;
  and_intros;
  · exact hu₀;
  · intro i;
    exact ⟨(hu i).2.1, (hu i).2.2, (hu i).1⟩

/-- Any point forcing `D` under an arbitrary valuation `ψ` is a `d`-point. -/
lemma exists_d_of_forces_D {w : World} (hD : w ⊩[⟨frame, ψ⟩] D) : ∃ m, w = World.d m := by
  obtain ⟨u, hu₀, hu⟩ := exists_p01_chain hD;
  obtain ⟨m, hm⟩ := strict_chain_all_d (fun i => (hu i).1) (fun i => (hu i).2.1) 0;
  exact ⟨m, hu₀ ▸ hm⟩

/-- A `d`-point forcing `D` forces `p0 ⋎ p1` at every `d`-point at or above its index: the fourth
conjunct of `D` makes `∼(p0 ⋎ p1)` upward-closed, so `p0 ⋎ p1` is inherited downward from the
strict `p0 ⋎ p1`-chain, which reaches every `d`-point index from above. -/
lemma forces_p01_at {m : ℕ} (hD : World.d m ⊩[⟨frame, ψ⟩] D) {k : ℕ} (hk : m ≤ k) :
    World.d k ⊩[⟨frame, ψ⟩] p0 ⋎ p1 := by
  obtain ⟨u, hu₀, hu⟩ := exists_p01_chain hD;
  have hd : ∀ i, ∃ k, u i = World.d k := by
    intro i;
    exact strict_chain_all_d (fun j => (hu j).1) (fun j => (hu j).2.1) i;
  choose kf hkf using hd;
  have hmono : StrictMono kf := by
    apply strictMono_nat_of_lt_succ;
    intro i;
    have h := (hu i).2.1;
    rw [hkf i, hkf (i + 1)] at h;
    simpa using h;
  have h₁ : World.d (kf k) ⊩[⟨frame, ψ⟩] p0 ⋎ p1 := by
    rw [← hkf k];
    exact (hu k).2.2.2;
  by_contra hcon;
  obtain ⟨-, -, -, hbox⟩ := forces_D_iff.mp hD;
  have h₂ := forces_box.mp hbox (World.d k) (by simp [hk]) (forces_neg.mpr hcon);
  exact forces_neg.mp (forces_box.mp h₂ (World.d (kf k)) (by simpa using hmono.le_apply)) h₁

/-! ### Classification of the V-shape -/

/-- Any tuple `(u₁, u₀, v₁, v₀)` with `R u₁ u₀`, `R v₁ v₀` and the four
incomparability facts (`¬ R u₀ u₁`, `¬ R v₀ v₁`, `¬ R u₁ v₀`,
`¬ R v₁ u₀`) must, up to swapping the `b`- and `c`-branches, have the shape
`(b_{n+1}, b_n, c_{n+1}, c_n)`. -/
lemma v_shape_classify {t u₀ u₁ v₀ v₁ : World}
    (hRtu1 : R t u₁) (hRu1u0 : R u₁ u₀) (hRtv1 : R t v₁) (hRv1v0 : R v₁ v₀)
    (hnu0u1 : ¬ R u₀ u₁) (hnv0v1 : ¬ R v₀ v₁) (hnu1v0 : ¬ R u₁ v₀) (hnv1u0 : ¬ R v₁ u₀) :
    ∃ n : ℕ, (u₁ = .b (n + 1) ∧ u₀ = .b n ∧ v₁ = .c (n + 1) ∧ v₀ = .c n) ∨
             (u₁ = .c (n + 1) ∧ u₀ = .c n ∧ v₁ = .b (n + 1) ∧ v₀ = .b n) := by
  cases u₁ <;> cases u₀ <;> cases v₁ <;> cases v₀ <;> simp_all <;> omega

/-! ### The reference points of the V-shape -/

/-- The forcing data available after extracting the V-shape from `w = d_m ⊩ E` and pinning it
(via `v_shape_classify`) to the upright configuration `(b_{n+1}, b_n, c_{n+1}, c_n)`: the guard
formula `D` and the `K`-block hold at `d_m`, and the four reference points force the atomic Litak
formulas. -/
structure ShapeData (m n : ℕ) (ψ : World → ℕ → Prop) : Prop where
  hwD : World.d m ⊩[⟨frame, ψ⟩] D
  hwK0 : World.d m ⊩[⟨frame, ψ⟩] K 0
  hbnB0 : World.b n ⊩[⟨frame, ψ⟩] B 0
  hbn1B1 : World.b (n + 1) ⊩[⟨frame, ψ⟩] B 1
  hcnC0 : World.c n ⊩[⟨frame, ψ⟩] C 0
  hcn1C1 : World.c (n + 1) ⊩[⟨frame, ψ⟩] C 1

variable {m n : ℕ} {z : World}

section

variable (hs : ShapeData m n ψ)

include hs

lemma ShapeData.hK1 : World.d m ⊩[⟨frame, ψ⟩] K1 0 := (forces_K_iff.mp hs.hwK0).1
lemma ShapeData.hK2 : World.d m ⊩[⟨frame, ψ⟩] K2 0 := (forces_K_iff.mp hs.hwK0).2.1
lemma ShapeData.hK3 : World.d m ⊩[⟨frame, ψ⟩] K3 0 := (forces_K_iff.mp hs.hwK0).2.2.1
lemma ShapeData.hK4 : World.d m ⊩[⟨frame, ψ⟩] K4 0 := (forces_K_iff.mp hs.hwK0).2.2.2

lemma ShapeData.K1_at (y : World) (hy : R (World.d m) y) (h : y ⊩[⟨frame, ψ⟩] B 1) :
    y ⊩[⟨frame, ψ⟩] ◇(B 0) ⋏ ∼◇(C 0) := forces_box.mp hs.hK1 y hy h

lemma ShapeData.K2_at (y : World) (hy : R (World.d m) y) (h : y ⊩[⟨frame, ψ⟩] C 1) :
    y ⊩[⟨frame, ψ⟩] ◇(C 0) ⋏ ∼◇(B 0) := forces_box.mp hs.hK2 y hy h

lemma ShapeData.K3_at (y : World) (hy : R (World.d m) y) (h : y ⊩[⟨frame, ψ⟩] B 0) :
    y ⊩[⟨frame, ψ⟩] ∼◇(B 1) := forces_box.mp hs.hK3 y hy h

lemma ShapeData.K4_at (y : World) (hy : R (World.d m) y) (h : y ⊩[⟨frame, ψ⟩] C 0) :
    y ⊩[⟨frame, ψ⟩] ∼◇(C 1) := forces_box.mp hs.hK4 y hy h

/-- The data of a V-shape, seen through the mirror valuation. -/
lemma ShapeData.mirror : ShapeData m n (mirrorVal ψ) where
  hwD := by simpa [forces_mirror, D] using hs.hwD
  hwK0 := by rw [forces_mirror, forces_K_subst_tau_iff]; exact hs.hwK0
  hbnB0 := by simpa [forces_mirror] using hs.hcnC0
  hbn1B1 := by simpa [forces_mirror] using hs.hcn1C1
  hcnC0 := by simpa [forces_mirror] using hs.hbnB0
  hcn1C1 := by simpa [forces_mirror] using hs.hbn1B1

/-! ### The `B`-side facts on the cone of `a_n` -/

/-- On the cone of `a_n`, `B 0` is forced only at `b_n`. -/
lemma eq_b_of_forces_B0 (hmn : m ≤ n) (hRz : R (.a n) z) (h : z ⊩[⟨frame, ψ⟩] B 0) :
    z = .b n := by
  have h₁ := hs.K3_at z (R_trans (by simp [hmn]) hRz) h;
  have h₂ := (forces_and.mp (hs.K2_at (.c (n + 1)) (by simp) hs.hcn1C1)).2;
  cases z with
  | a k =>
    simp only [R_a_a] at hRz;
    subst hRz;
    exact (false_of_neg_dia h₁ (y := .b (k + 1)) (by simp) hs.hbn1B1).elim;
  | b k =>
    simp at hRz;
    rcases Nat.lt_trichotomy k n with hk | rfl | hk;
    · exact (false_of_neg_dia h₂ (y := .b k) (by simp; omega) h).elim;
    · rfl;
    · obtain rfl : k = n + 1 := by omega;
      exact (false_of_neg_dia h₁ (y := .b (n + 1)) (by simp) hs.hbn1B1).elim;
  | c k =>
    simp at hRz;
    exact (false_of_neg_dia h₂ (y := .c k) (by simp; omega) h).elim;
  | d k => simp at hRz

/-- On the cone of `a_n`, `B 1` is forced only at `b_{n+1}`. -/
lemma eq_b_of_forces_B1 (hmn : m ≤ n) (hRz : R (.a n) z) (h : z ⊩[⟨frame, ψ⟩] B 1) :
    z = .b (n + 1) := by
  have hR : R (.d m) z := R_trans (by simp [hmn]) hRz;
  obtain ⟨h₁, h₂⟩ := forces_and.mp (hs.K1_at z hR h);
  have h₃ := hs.K3_at (.b n) (by simp) hs.hbnB0;
  cases z with
  | a k =>
    simp only [R_a_a] at hRz;
    subst hRz;
    exact (false_of_neg_dia h₂ (y := .c k) (by simp) hs.hcnC0).elim;
  | b k =>
    simp at hRz;
    rcases Nat.lt_or_ge k (n + 1) with hk | hk;
    · exact (false_of_neg_dia h₃ (y := .b k) (by simp; omega) h).elim;
    · obtain rfl : k = n + 1 := by omega;
      rfl;
  | c k =>
    simp at hRz;
    rcases Nat.lt_or_ge k n with hk | hk;
    · obtain ⟨w, hcw, hw⟩ := forces_dia.mp h₁;
      obtain rfl := eq_b_of_forces_B0 hs hmn (R_trans (by simp; omega) hcw) hw;
      simp at hcw;
      omega;
    · exact (false_of_neg_dia h₂ (y := .c n) (by simp [hk]) hs.hcnC0).elim;
  | d k => simp at hRz

/-- `b_{n+2}` forces `B 2`. -/
lemma forces_B2_at : World.b (n + 2) ⊩[⟨frame, ψ⟩] B 2 := by
  have h₁ := (forces_and.mp (hs.K1_at (.b (n + 1)) (by simp) hs.hbn1B1)).2;
  have h₂ := hs.K4_at (.c n) (by simp) hs.hcnC0;
  rw [B_add_two, forces_and, forces_and];
  and_intros;
  · exact forces_dia.mpr ⟨.b (n + 1), by simp, hs.hbn1B1⟩;
  · exact forces_dia.mpr ⟨.c n, by simp, hs.hcnC0⟩;
  · rw [forces_neg, not_forces_dia];
    intro q hq hqC1;
    cases q with
    | a k => simp at hq;
    | d k => simp at hq;
    | c k =>
      simp at hq;
      exact false_of_neg_dia h₂ (by simp; omega) hqC1;
    | b k =>
      simp at hq;
      obtain ⟨hkC0, hkB0⟩ := forces_and.mp (hs.K2_at (.b k) (by simp) hqC1);
      rcases Nat.lt_or_ge k (n + 2) with hk | hk;
      · obtain ⟨r, hbkr, hr⟩ := forces_dia.mp hkC0;
        exact false_of_neg_dia h₁ (R_trans (by simp; omega) hbkr) hr;
      · obtain rfl : k = n + 2 := by omega;
        exact false_of_neg_dia hkB0 (y := .b n) (by simp) hs.hbnB0

/-! ### The facts on the cone of `d_{n+1}` -/

/-- On the cone of `d_{n+1}`, `B 1` is forced only at `b_{n+1}`. -/
lemma eq_bn1_of_forces_B1 (hmn : m ≤ n) (hRz : R (.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] B 1) :
    z = .b (n + 1) := by
  have h₁ := (forces_and.mp (hs.K1_at z (R_trans (by simp; omega) hRz) h)).2;
  cases z with
  | d k => exact (false_of_neg_dia h₁ (y := .c n) (by simp) hs.hcnC0).elim;
  | a k =>
    simp at hRz;
    exact (false_of_neg_dia h₁ (y := .c n) (by simp; omega) hs.hcnC0).elim;
  | c k =>
    rcases Nat.lt_or_ge k n with hk | hk;
    · have := eq_b_of_forces_B1 hs hmn (z := .c k) (by simp; omega) h;
      simp at this;
    · exact (false_of_neg_dia h₁ (y := .c n) (by simp [hk]) hs.hcnC0).elim;
  | b k =>
    rcases Nat.lt_or_ge k (n + 2) with hk | hk;
    · exact eq_b_of_forces_B1 hs hmn (by simp; omega) h;
    · exact (false_of_neg_dia h₁ (y := .c n) (by simp; omega) hs.hcnC0).elim

/-- On the cone of `d_{n+1}`, `B 2` is forced only at `b_{n+2}`. -/
lemma eq_bn2_of_forces_B2 (hmn : m ≤ n) (hRz : R (.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] B 2) :
    z = .b (n + 2) := by
  rw [B_add_two, forces_and, forces_and] at h;
  obtain ⟨h₁, h₂, h₃⟩ := h;
  obtain ⟨y, hzy, hy⟩ := forces_dia.mp h₁;
  obtain rfl := eq_bn1_of_forces_B1 hs hmn (R_trans hRz hzy) hy;
  have h₄ := (forces_and.mp (hs.K1_at (.b (n + 1)) (by simp) hs.hbn1B1)).2;
  cases z with
  | a k =>
    simp at hRz;
    exact (false_of_neg_dia h₃ (y := .c (n + 1)) (by simp; omega) hs.hcn1C1).elim;
  | d k => exact (false_of_neg_dia h₃ (y := .c (n + 1)) (by simp) hs.hcn1C1).elim;
  | c k =>
    simp at hzy;
    exact (false_of_neg_dia h₃ (y := .c (n + 1)) (by simp; omega) hs.hcn1C1).elim;
  | b k =>
    simp at hzy;
    rcases Nat.lt_or_ge k (n + 3) with hk | hk;
    · obtain rfl | rfl : k = n + 1 ∨ k = n + 2 := by omega;
      · exact (forces_neg.mp h₄ h₂).elim;
      · rfl;
    · exact (false_of_neg_dia h₃ (y := .c (n + 1)) (by simp; omega) hs.hcn1C1).elim

/-! ### The `C`-side facts, by the mirror -/

/-- `c_{n+2}` forces `C 2`, the mirror of `forces_B2_at`. -/
lemma forces_C2_at : World.c (n + 2) ⊩[⟨frame, ψ⟩] C 2 := by
  simpa [forces_mirror] using forces_B2_at hs.mirror

/-- On the cone of `d_{n+1}`, `C 1` is forced only at `c_{n+1}`. -/
lemma eq_cn1_of_forces_C1 (hmn : m ≤ n) (hRz : R (.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] C 1) :
    z = .c (n + 1) := by
  have := eq_bn1_of_forces_B1 hs.mirror hmn (z := swap z) (by simpa using R_swap.mpr hRz)
    (by simpa [forces_mirror] using h);
  simpa [swap_involutive.eq_iff] using this

/-- On the cone of `d_{n+1}`, `C 2` is forced only at `c_{n+2}`. -/
lemma eq_cn2_of_forces_C2 (hmn : m ≤ n) (hRz : R (.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] C 2) :
    z = .c (n + 2) := by
  have := eq_bn2_of_forces_B2 hs.mirror hmn (z := swap z) (by simpa using R_swap.mpr hRz)
    (by simpa [forces_mirror] using h);
  simpa [swap_involutive.eq_iff] using this

/-- `a_{n+1}` sees no point forcing `B 3`. -/
lemma not_forces_dia_B3 (hmn : m ≤ n) : World.a (n + 1) ⊩[⟨frame, ψ⟩] ∼◇(B 3) := by
  rw [forces_neg, not_forces_dia];
  intro p hp hpB3;
  rw [B_add_two, forces_and, forces_and] at hpB3;
  obtain ⟨h₁, h₂, h₃⟩ := hpB3;
  obtain ⟨q₂, hpq₂, hq₂⟩ := forces_dia.mp h₁;
  obtain ⟨q₁, hpq₁, hq₁⟩ := forces_dia.mp h₂;
  have hdp : R (.d (n + 1)) p := R_trans (by simp) hp;
  obtain rfl := eq_bn2_of_forces_B2 hs hmn (R_trans hdp hpq₂) hq₂;
  obtain rfl := eq_cn1_of_forces_C1 hs hmn (R_trans hdp hpq₁) hq₁;
  cases p with
  | d j => simp at hp;
  | a j =>
    simp only [rel_frame, R_a_a] at hp;
    subst hp;
    exact false_of_neg_dia h₃ (y := .c (n + 2)) (by simp) (forces_C2_at hs)
  | b j =>
    simp at hp hpq₁;
    omega
  | c j =>
    simp at hp hpq₂;
    omega

/-- `a_{n+1}` sees no point forcing `C 3`, the mirror of `not_forces_dia_B3`. -/
lemma not_forces_dia_C3 (hmn : m ≤ n) : World.a (n + 1) ⊩[⟨frame, ψ⟩] ∼◇(C 3) := by
  simpa [forces_mirror] using not_forces_dia_B3 hs.mirror hmn

/-- `a_{n+1}` forces `A 1`. -/
lemma forces_A1_at (hmn : m ≤ n) : World.a (n + 1) ⊩[⟨frame, ψ⟩] A 1 := by
  rw [forces_A_iff];
  and_intros;
  · exact forces_dia.mpr ⟨.b (n + 2), by simp, forces_B2_at hs⟩;
  · exact forces_dia.mpr ⟨.c (n + 2), by simp, forces_C2_at hs⟩;
  · exact not_forces_dia_B3 hs hmn;
  · exact not_forces_dia_C3 hs hmn

/-- No point in the cone of `d_{n+1}` forces `A 0`: the only `A 0`-point `a_n` is not
reachable from `d_{n+1}`. -/
lemma not_dia_A0_at (hmn : m ≤ n) : World.d (n + 1) ⊩[⟨frame, ψ⟩] ∼◇(A 0) := by
  rw [forces_neg, not_forces_dia];
  intro z hz hzA0;
  obtain ⟨h₁, h₂, h₃, h₄⟩ := forces_A_iff.mp hzA0;
  obtain ⟨y₁, hzy₁, hy₁⟩ := forces_dia.mp h₁;
  obtain ⟨y₂, hzy₂, hy₂⟩ := forces_dia.mp h₂;
  obtain rfl := eq_bn1_of_forces_B1 hs hmn (R_trans hz hzy₁) hy₁;
  obtain rfl := eq_cn1_of_forces_C1 hs hmn (R_trans hz hzy₂) hy₂;
  cases z with
  | d k => exact false_of_neg_dia h₃ (y := .b (n + 2)) (by simp) (forces_B2_at hs)
  | a k =>
    simp at hz;
    exact false_of_neg_dia h₃ (y := .b (n + 2)) (by simp; omega) (forces_B2_at hs)
  | b k =>
    simp at hzy₂;
    exact false_of_neg_dia h₃ (y := .b (n + 2)) (by simp; omega) (forces_B2_at hs)
  | c k =>
    simp at hzy₁;
    exact false_of_neg_dia h₄ (y := .c (n + 2)) (by simp; omega) (forces_C2_at hs)

/-- Any point forcing `A 0` and seeing the `B 1`-point `b_{n+1}` and the `C 1`-point `c_{n+1}`
is the apex `a_n`. -/
lemma apex_eq (hzA0 : z ⊩[⟨frame, ψ⟩] A 0) (hRzb : R z (.b (n + 1))) (hRzc : R z (.c (n + 1))) :
    z = .a n := by
  obtain ⟨-, -, h₁, h₂⟩ := forces_A_iff.mp hzA0;
  cases z with
  | d k => exact (false_of_neg_dia h₁ (y := .b (n + 2)) (by simp) (forces_B2_at hs)).elim;
  | b k =>
    simp at hRzb hRzc;
    exact (false_of_neg_dia h₁ (y := .b (n + 2)) (by simp; omega) (forces_B2_at hs)).elim;
  | c k =>
    simp at hRzb hRzc;
    exact (false_of_neg_dia h₂ (y := .c (n + 2)) (by simp; omega) (forces_C2_at hs)).elim;
  | a k =>
    simp at hRzb hRzc;
    have hkn : k ≤ n := by
      by_contra hc;
      exact false_of_neg_dia h₁ (y := .b (n + 2)) (by simp; omega) (forces_B2_at hs);
    exact congrArg World.a (by omega)

end

/-! ### Assembly: the frame validates `G` -/

/-- The upright core of `validates_G`: from the V-shape data (with reference forcings in the
`(b_{n+1}, b_n, c_{n+1}, c_n)` configuration) and the apex `t` forcing `A 0` and seeing
`b_{n+1}` and `c_{n+1}`, the point `d_m` forces `F`. The witness is `d_{n+1}`. -/
lemma forces_F_of_shapeAndApex (hs : ShapeData m n ψ) {t : World}
    (hwt : R (.d m) t) (htA0 : t ⊩[⟨frame, ψ⟩] A 0)
    (hRtb : R t (.b (n + 1))) (hRtc : R t (.c (n + 1))) :
    World.d m ⊩[⟨frame, ψ⟩] F := by
  obtain rfl := apex_eq hs htA0 hRtb hRtc;
  have hmn : m ≤ n := by simpa using hwt;
  rw [F, forces_dia];
  use World.d (n + 1);
  rw [forces_and, forces_and];
  and_intros;
  · simp; omega;
  · exact forces_p01_at hs.hwD (by omega);
  · exact not_dia_A0_at hs hmn;
  · exact forces_dia.mpr ⟨.a (n + 1), by simp, forces_A1_at hs hmn⟩

/-- Fine's frame validates `G`: for every valuation and every point, `E → F` holds.

- [Fin74a, Lemma 2]
- [Lit04, p. 332] -/
theorem validates_G : frame ⊧ G := by
  intro ψ w hE;
  obtain ⟨t, u₀, u₁, v₀, v₁, hwt, htA0, htu1, hu1u0, htv1, hv1v0, hu1B1, hu0B0, hv1C1, hv0C0,
    hnu0u1, hnv0v1, hnu1v0, hnv1u0⟩ := exists_V_shape hE;
  obtain ⟨hD, -, hK0⟩ := forces_E_iff.mp hE;
  obtain ⟨m, rfl⟩ := exists_d_of_forces_D hD;
  obtain ⟨n, hcase⟩ := v_shape_classify htu1 hu1u0 htv1 hv1v0 hnu0u1 hnv0v1 hnu1v0 hnv1u0;
  rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩;
  · exact forces_F_of_shapeAndApex ⟨hD, hK0, hu0B0, hu1B1, hv0C0, hv1C1⟩ hwt htA0 htu1 htv1;
  · have hs : ShapeData m n (ψ ∘ swap) := by
      constructor;
      · simpa using forces_swap_iff.mp hD;
      · simpa using forces_swap_iff.mp hK0;
      · simpa using forces_swap_iff.mp hu0B0;
      · simpa using forces_swap_iff.mp hu1B1;
      · simpa using forces_swap_iff.mp hv0C0;
      · simpa using forces_swap_iff.mp hv1C1;
    have hF := forces_F_of_shapeAndApex hs (t := swap t) (by simpa using R_swap.mpr hwt)
      (forces_swap_iff.mp htA0) (by simpa using R_swap.mpr htu1)
      (by simpa using R_swap.mpr htv1);
    exact forces_swap_iff.mpr (by simpa using hF)

end Fine

end
