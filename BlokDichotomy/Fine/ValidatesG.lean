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
  obtain ⟨hD, hA0, hK⟩ := forces_E_iff.mp hE;
  obtain ⟨t, hwt, htA0⟩ := forces_dia.mp hA0;
  have htA0' := htA0;
  rw [A] at htA0;
  simp only [forces_and] at htA0;
  obtain ⟨htB1, htC1, _htnB2, _htnC2⟩ := htA0;
  obtain ⟨u₁, htu1, hu1B1⟩ := forces_dia.mp htB1;
  obtain ⟨v₁, htv1, hv1C1⟩ := forces_dia.mp htC1;
  simp only [K, forces_and] at hK;
  obtain ⟨hK1, hK2, hK3, hK4⟩ := hK;
  -- Apply K1 at u₁ (reachable from w via t)
  rw [K1, forces_box] at hK1;
  have hwu1 : R w u₁ := R_trans hwt htu1;
  have hu1' := hK1 u₁ hwu1 hu1B1;
  rw [forces_and] at hu1';
  obtain ⟨hu1B0dia, hu1nC0⟩ := hu1';
  obtain ⟨u₀, hu1u0, hu0B0⟩ := forces_dia.mp hu1B0dia;
  -- Apply K2 at v₁
  rw [K2, forces_box] at hK2;
  have hwv1 : R w v₁ := R_trans hwt htv1;
  have hv1' := hK2 v₁ hwv1 hv1C1;
  rw [forces_and] at hv1';
  obtain ⟨hv1C0dia, hv1nB0⟩ := hv1';
  obtain ⟨v₀, hv1v0, hv0C0⟩ := forces_dia.mp hv1C0dia;
  -- K3 at u₀ : u₀ ⊮ ◇ B 1
  rw [K3, forces_box] at hK3;
  have hwu0 : R w u₀ := R_trans hwu1 hu1u0;
  have hu0nB1 := hK3 u₀ hwu0 hu0B0;
  rw [forces_neg] at hu0nB1;
  -- K4 at v₀ : v₀ ⊮ ◇ C 1
  rw [K4, forces_box] at hK4;
  have hwv0 : R w v₀ := R_trans hwv1 hv1v0;
  have hv0nC1 := hK4 v₀ hwv0 hv0C0;
  rw [forces_neg] at hv0nC1;
  refine ⟨t, u₀, u₁, v₀, v₁, hwt, htA0', htu1, hu1u0, htv1, hv1v0,
    hu1B1, hu0B0, hv1C1, hv0C0, ?_, ?_, ?_, ?_⟩;
  · -- ¬ R u₀ u₁ : else u₀ ⊩ ◇ B 1
    by_contra hcon;
    exact hu0nB1 ⟨u₁, hcon, hu1B1⟩;
  · -- ¬ R v₀ v₁
    by_contra hcon;
    exact hv0nC1 ⟨v₁, hcon, hv1C1⟩;
  · -- ¬ R u₁ v₀ : u₁ ⊩ ∼◇ C 0 but v₀ ⊩ C 0
    by_contra hcon;
    rw [forces_neg] at hu1nC0;
    exact hu1nC0 ⟨v₀, hcon, hv0C0⟩;
  · -- ¬ R v₁ u₀ : v₁ ⊩ ∼◇ B 0 but u₀ ⊩ B 0
    by_contra hcon;
    rw [forces_neg] at hv1nB0;
    exact hv1nB0 ⟨u₀, hcon, hu0B0⟩;

/-! ### Confinement of forced points to `d`-points -/

/-- `D`'s two guard conjuncts drive an infinite, strictly ascending chain of points forced
into the cone of `w`, alternating between `p0` and `p1`. -/
private lemma exists_p01_chain {w : World} (hD : w ⊩[⟨frame, ψ⟩] D) :
    ∃ u : ℕ → World, u 0 = w ∧
      ∀ i, R (u i) (u (i + 1)) ∧ ¬ R (u (i + 1)) (u i) ∧
        R w (u i) ∧ u i ⊩[⟨frame, ψ⟩] (p0 ⋎ p1) := by
  simp only [D, forces_and] at hD;
  obtain ⟨hp01, hbox1, hbox2, _hbox3⟩ := hD;
  rw [forces_box] at hbox1 hbox2;
  have step : ∀ (i : ℕ) (y : World), (R w y ∧ y ⊩[⟨frame, ψ⟩] (p0 ⋎ p1)) →
      ∃ v, y ≺ v ∧ ¬ (v ≺ y) ∧ (R w v ∧ v ⊩[⟨frame, ψ⟩] (p0 ⋎ p1)) := by
    intro i y ⟨hwy, hy01⟩;
    rcases forces_or.mp hy01 with hy0 | hy1;
    · have himp := hbox1 y hwy;
      rw [forces_imp] at himp;
      have hcon := himp.resolve_left (not_not.mpr hy0);
      obtain ⟨hny1, hdia1⟩ := forces_and.mp hcon;
      obtain ⟨z, hyz, hz1⟩ := forces_dia.mp hdia1;
      refine ⟨z, hyz, ?_, R_trans hwy hyz, forces_or.mpr (Or.inr hz1)⟩;
      by_contra hzy;
      have hyz' : y = z := R_antisymm hyz hzy;
      exact (forces_neg.mp hny1) (hyz' ▸ hz1);
    · have himp := hbox2 y hwy;
      rw [forces_imp] at himp;
      have hcon := himp.resolve_left (not_not.mpr hy1);
      obtain ⟨hny0, hdia0⟩ := forces_and.mp hcon;
      obtain ⟨z, hyz, hz0⟩ := forces_dia.mp hdia0;
      refine ⟨z, hyz, ?_, R_trans hwy hyz, forces_or.mpr (Or.inl hz0)⟩;
      by_contra hzy;
      have hyz' : y = z := R_antisymm hyz hzy;
      exact (forces_neg.mp hny0) (hyz' ▸ hz0);
  obtain ⟨u, hu0, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => R y v ∧ ¬R v y)
    (P := fun _ y => R w y ∧ y ⊩[⟨frame, ψ⟩] (p0 ⋎ p1)) ⟨R_refl w, hp01⟩ fun i y hy => by
      obtain ⟨v, hyv, hvy, hv⟩ := step i y hy;
      exact ⟨v, ⟨hyv, hvy⟩, hv⟩;
  exact ⟨u, hu0, fun i => ⟨(hu i).2.1, (hu i).2.2, (hu i).1⟩⟩

/-- Any point forcing `D` under an arbitrary valuation `ψ` is a `d`-point. -/
lemma exists_d_of_forces_D {w : World} (hD : w ⊩[⟨frame, ψ⟩] D) : ∃ m, w = World.d m := by
  obtain ⟨u, hu0, hu⟩ := exists_p01_chain hD;
  obtain ⟨m, hm⟩ := strict_chain_all_d (fun i => (hu i).1) (fun i => (hu i).2.1) 0;
  exact ⟨m, hu0 ▸ hm⟩

/-- Starting from a `d`-point forcing `D` under an arbitrary valuation `ψ`, there are
`d`-points forcing `p0 ⋎ p1` at arbitrarily large index. -/
lemma exists_ge_forces_p0_or_p1 {m : ℕ} (hD : (World.d m) ⊩[⟨frame, ψ⟩] D) (n : ℕ) :
    ∃ k, n ≤ k ∧ (World.d k) ⊩[⟨frame, ψ⟩] (p0 ⋎ p1) := by
  obtain ⟨u, hu0, hu⟩ := exists_p01_chain hD;
  have hd : ∀ i, ∃ k, u i = .d k :=
    fun i => strict_chain_all_d (fun j => (hu j).1) (fun j => (hu j).2.1) i;
  choose kf hkf using hd;
  have hkf0 : kf 0 = m := by
    have h := hkf 0; rw [hu0] at h; simp only [World.d.injEq] at h; exact h.symm;
  have hmono : ∀ i, kf i < kf (i + 1) := by
    intro i;
    have h := (hu i).2.1;
    rw [hkf i, hkf (i + 1)] at h;
    simpa [R] using h;
  have hgrow : ∀ i, kf 0 + i ≤ kf i := by
    intro i; induction i with
    | zero => simp
    | succ i ih => have := hmono i; omega
  refine ⟨kf n, ?_, ?_⟩;
  · have := hgrow n; omega;
  · rw [← hkf n]; exact (hu n).2.2.2

/-! ### Classification of the V-shape and atom-set pinning -/

/-- Any tuple `(u₁, u₀, v₁, v₀)` with `R u₁ u₀`, `R v₁ v₀` and the four
incomparability facts (`¬ R u₀ u₁`, `¬ R v₀ v₁`, `¬ R u₁ v₀`,
`¬ R v₁ u₀`) must, up to swapping the `b`- and `c`-branches, have the shape
`(b_{n+1}, b_n, c_{n+1}, c_n)`. -/
lemma v_shape_classify {t u₀ u₁ v₀ v₁ : World}
    (hRtu1 : R t u₁) (hRu1u0 : R u₁ u₀) (hRtv1 : R t v₁) (hRv1v0 : R v₁ v₀)
    (hnu0u1 : ¬ R u₀ u₁) (hnv0v1 : ¬ R v₀ v₁) (hnu1v0 : ¬ R u₁ v₀) (hnv1u0 : ¬ R v₁ u₀) :
    ∃ n : ℕ, (u₁ = .b (n + 1) ∧ u₀ = .b n ∧ v₁ = .c (n + 1) ∧ v₀ = .c n) ∨
             (u₁ = .c (n + 1) ∧ u₀ = .c n ∧ v₁ = .b (n + 1) ∧ v₀ = .b n) := by
  cases u₁ with
  | a i => exfalso; cases v₁ <;> cases u₀ <;> cases v₀ <;> grind [R]
  | d i => exfalso; cases v₁ <;> cases u₀ <;> cases v₀ <;> grind [R]
  | b i =>
    cases v₁ with
    | a j => exfalso; cases u₀ <;> cases v₀ <;> grind [R]
    | d j => exfalso; cases u₀ <;> cases v₀ <;> grind [R]
    | b j => exfalso; cases u₀ <;> cases v₀ <;> grind [R]
    | c j =>
      cases u₀ with
      | b l =>
        cases v₀ with
        | c m =>
          simp_all only [R, reduceCtorEq, World.b.injEq, World.c.injEq]
          exact ⟨l, by omega⟩
        | a m => exfalso; grind [R]
        | b m => exfalso; grind [R]
        | d m => exfalso; grind [R]
      | a l => exfalso; cases v₀ <;> grind [R]
      | c l => exfalso; cases v₀ <;> grind [R]
      | d l => exfalso; cases v₀ <;> grind [R]
  | c i =>
    cases v₁ with
    | a j => exfalso; cases u₀ <;> cases v₀ <;> grind [R]
    | d j => exfalso; cases u₀ <;> cases v₀ <;> grind [R]
    | c j => exfalso; cases u₀ <;> cases v₀ <;> grind [R]
    | b j =>
      cases u₀ with
      | c l =>
        cases v₀ with
        | b m =>
          simp_all only [R, reduceCtorEq, World.b.injEq, World.c.injEq]
          exact ⟨l, by omega⟩
        | a m => exfalso; grind [R]
        | c m => exfalso; grind [R]
        | d m => exfalso; grind [R]
      | a l => exfalso; cases v₀ <;> grind [R]
      | b l => exfalso; cases v₀ <;> grind [R]
      | d l => exfalso; cases v₀ <;> grind [R]

variable {n : ℕ} {z : World}

/-- The forcing data pinned down by the V-shape at the apex `a_n`: the `K`-block holds at `a_n`,
and the four reference points force `B 0`, `B 1`, `C 0`, `C 1`. -/
structure VShapeForces (n : ℕ) (ψ : World → ℕ → Prop) : Prop where
  hK0 : (World.a n) ⊩[⟨frame, ψ⟩] K 0
  hbnB0 : (World.b n) ⊩[⟨frame, ψ⟩] B 0
  hbn1B1 : (World.b (n + 1)) ⊩[⟨frame, ψ⟩] B 1
  hcnC0 : (World.c n) ⊩[⟨frame, ψ⟩] C 0
  hcn1C1 : (World.c (n + 1)) ⊩[⟨frame, ψ⟩] C 1

section

variable (hd : VShapeForces n ψ)

include hd

/-- On the cone of `a_n`, any point forcing `B 0` is `b_n`, `c_{n+2}`, or an `a`-point below
`n` (the `c_{n+2}` case is vacuous inside the cone). -/
lemma forces_B0_of_vshape (hRz : R (.a n) z) (hB0 : z ⊩[⟨frame, ψ⟩] B 0) :
    z = .b n ∨ z = .c (n + 2) ∨ ∃ j < n, z = .a j := by
  obtain ⟨hK0, hbnB0, hbn1B1, hcnC0, hcn1C1⟩ := hd
  simp only [K, forces_and] at hK0
  obtain ⟨_hK1, hK2, hK3, _hK4⟩ := hK0
  rw [K3, forces_box] at hK3
  rw [K2, forces_box] at hK2
  have hcn1 := forces_and.mp
    (hK2 (World.c (n + 1)) (by simp only [R]; omega : R (World.a n) (World.c (n + 1))) hcn1C1)
  have hcn1_nB0 : (World.c (n + 1)) ⊮ ◇(B 0) := forces_neg.mp hcn1.2
  cases z with
  | a k =>
    simp only [R] at hRz; subst hRz
    exfalso
    have h := hK3 (World.a k) (by simp only [R] : R (World.a k) (World.a k)) hB0
    rw [forces_neg] at h
    exact h ⟨World.b (k + 1), (by simp only [R]; omega : R (World.a k) (World.b (k + 1))), hbn1B1⟩
  | b k =>
    simp only [R] at hRz
    rcases Nat.lt_trichotomy k n with h | h | h
    · exact absurd ⟨World.b k, (by simp only [R]; omega : R (World.c (n + 1)) (World.b k)),
        hB0⟩ hcn1_nB0
    · exact Or.inl (by rw [h])
    · have hk : k = n + 1 := by omega
      subst hk
      exfalso
      have h' := hK3 (World.b (n + 1)) (by simp only [R]; omega : R (World.a n) (World.b (n + 1)))
          hB0
      rw [forces_neg] at h'
      exact h' ⟨World.b (n + 1), (by simp only [R]; omega : R (World.b (n + 1)) (World.b (n + 1))),
          hbn1B1⟩
  | c k =>
    simp only [R] at hRz
    exact absurd ⟨World.c k, (by simp only [R]; omega : R (World.c (n + 1)) (World.c k)),
        hB0⟩ hcn1_nB0
  | d k =>
    simp only [R] at hRz

/-- On the cone of `a_n`, any point forcing `C 0` is `c_n`, `b_{n+2}`, or an `a`-point below
`n` (the `b_{n+2}` case is vacuous inside the cone). -/
lemma forces_C0_of_vshape (hRz : R (.a n) z) (hC0 : z ⊩[⟨frame, ψ⟩] C 0) :
    z = .c n ∨ z = .b (n + 2) ∨ ∃ j < n, z = .a j := by
  obtain ⟨hK0, hbnB0, hbn1B1, hcnC0, hcn1C1⟩ := hd
  simp only [K, forces_and] at hK0
  obtain ⟨hK1, _hK2, _hK3, hK4⟩ := hK0
  rw [K1, forces_box] at hK1
  rw [K4, forces_box] at hK4
  have hbn1 := forces_and.mp
    (hK1 (World.b (n + 1)) (by simp only [R]; omega : R (World.a n) (World.b (n + 1))) hbn1B1)
  have hbn1_nC0 : (World.b (n + 1)) ⊮ ◇(C 0) := forces_neg.mp hbn1.2
  cases z with
  | a k =>
    simp only [R] at hRz; subst hRz
    exfalso
    have h := hK4 (World.a k) (by simp only [R] : R (World.a k) (World.a k)) hC0
    rw [forces_neg] at h
    exact h ⟨World.c (k + 1), (by simp only [R]; omega : R (World.a k) (World.c (k + 1))), hcn1C1⟩
  | b k =>
    simp only [R] at hRz
    exact absurd ⟨World.b k, (by simp only [R]; omega : R (World.b (n + 1)) (World.b k)),
        hC0⟩ hbn1_nC0
  | c k =>
    simp only [R] at hRz
    rcases Nat.lt_trichotomy k n with h | h | h
    · exact absurd ⟨World.c k, (by simp only [R]; omega : R (World.b (n + 1)) (World.c k)),
        hC0⟩ hbn1_nC0
    · exact Or.inl (by rw [h])
    · have hk : k = n + 1 := by omega
      subst hk
      exfalso
      have h' := hK4 (World.c (n + 1)) (by simp only [R]; omega : R (World.a n) (World.c (n + 1)))
          hC0
      rw [forces_neg] at h'
      exact h' ⟨World.c (n + 1), (by simp only [R]; omega : R (World.c (n + 1)) (World.c (n + 1))),
          hcn1C1⟩
  | d k =>
    simp only [R] at hRz

/-- On the cone of `a_n`, `B 1` is forced exactly at `b_{n+1}`. -/
lemma forces_B1_iff_of_vshape (hRz : R (.a n) z) :
    z ⊩[⟨frame, ψ⟩] B 1 ↔ z = .b (n + 1) := by
  constructor
  · intro hB1
    have hK0 := hd.hK0
    simp only [K, forces_and] at hK0
    obtain ⟨hK1, _hK2, hK3, _hK4⟩ := hK0
    rw [K1, forces_box] at hK1
    rw [K3, forces_box] at hK3
    cases z with
    | a k =>
      simp only [R] at hRz; subst hRz
      exfalso
      have h := forces_and.mp (hK1 (World.a k) (by simp only [R] : R (World.a k) (World.a k)) hB1)
      exact (forces_neg.mp h.2) ⟨World.c k, (by simp only [R]; omega : R (World.a k) (World.c k)),
          hd.hcnC0⟩
    | b k =>
      simp only [R] at hRz
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · exfalso
        have hbn := forces_neg.mp
          (hK3 (World.b n) (by simp only [R]; omega : R (World.a n) (World.b n)) hd.hbnB0)
        exact hbn ⟨World.b k, (by simp only [R]; omega : R (World.b n) (World.b k)), hB1⟩
      · rw [show k = n + 1 by omega]
    | c k =>
      simp only [R] at hRz
      exfalso
      have h := forces_and.mp (hK1 (World.c k) (by simp only [R]; omega : R (World.a n) (World.c
          k)) hB1)
      rcases Nat.lt_or_ge k n with hk | hk
      · obtain ⟨w, hcw, hwB0⟩ := forces_dia.mp h.1
        have hcwR : R (World.c k) w := hcw
        have hRaw : R (World.a n) w :=
            R_trans (by simp only [R]; omega : R (World.a n) (World.c k)) hcwR
        rcases forces_B0_of_vshape hd hRaw hwB0 with hb | hc | ⟨j, _, ha⟩
        · rw [hb] at hcwR; simp only [R] at hcwR; omega
        · rw [hc] at hcwR; simp only [R] at hcwR; omega
        · rw [ha] at hcwR; simp only [R] at hcwR
      · exact (forces_neg.mp h.2) ⟨World.c n, (by simp only [R]; omega : R (World.c k) (World.c n)),
          hd.hcnC0⟩
    | d k =>
      simp only [R] at hRz
  · intro h; subst h; exact hd.hbn1B1

/-- On the cone of `a_n`, `C 1` is forced exactly at `c_{n+1}`. -/
lemma forces_C1_iff_of_vshape (hRz : R (.a n) z) :
    z ⊩[⟨frame, ψ⟩] C 1 ↔ z = .c (n + 1) := by
  constructor
  · intro hC1
    have hK0 := hd.hK0
    simp only [K, forces_and] at hK0
    obtain ⟨_hK1, hK2, _hK3, hK4⟩ := hK0
    rw [K2, forces_box] at hK2
    rw [K4, forces_box] at hK4
    cases z with
    | a k =>
      simp only [R] at hRz; subst hRz
      exfalso
      have h := forces_and.mp (hK2 (World.a k) (by simp only [R] : R (World.a k) (World.a k)) hC1)
      exact (forces_neg.mp h.2) ⟨World.b k, (by simp only [R]; omega : R (World.a k) (World.b k)),
          hd.hbnB0⟩
    | b k =>
      simp only [R] at hRz
      exfalso
      have h := forces_and.mp (hK2 (World.b k) (by simp only [R]; omega : R (World.a n) (World.b
          k)) hC1)
      rcases Nat.lt_or_ge k n with hk | hk
      · obtain ⟨w, hbw, hwC0⟩ := forces_dia.mp h.1
        have hbwR : R (World.b k) w := hbw
        have hRaw : R (World.a n) w :=
            R_trans (by simp only [R]; omega : R (World.a n) (World.b k)) hbwR
        rcases forces_C0_of_vshape hd hRaw hwC0 with hc | hb | ⟨j, _, ha⟩
        · rw [hc] at hbwR; simp only [R] at hbwR; omega
        · rw [hb] at hbwR; simp only [R] at hbwR; omega
        · rw [ha] at hbwR; simp only [R] at hbwR
      · exact (forces_neg.mp h.2) ⟨World.b n, (by simp only [R]; omega : R (World.b k) (World.b n)),
          hd.hbnB0⟩
    | c k =>
      simp only [R] at hRz
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · exfalso
        have hcn := forces_neg.mp
          (hK4 (World.c n) (by simp only [R]; omega : R (World.a n) (World.c n)) hd.hcnC0)
        exact hcn ⟨World.c k, (by simp only [R]; omega : R (World.c n) (World.c k)), hC1⟩
      · rw [show k = n + 1 by omega]
    | d k =>
      simp only [R] at hRz
  · intro h; subst h; exact hd.hcn1C1

end

/-! ### Derived truth-set facts on the cone of `d_m` -/

variable {m : ℕ}

private lemma B2_def : (B 2 : Formula ℕ) = ◇(B 1) ⋏ ◇(C 0) ⋏ ∼◇(C 1) := B_add_two 0
private lemma C2_def : (C 2 : Formula ℕ) = ◇(C 1) ⋏ ◇(B 0) ⋏ ∼◇(B 1) := C_add_two 0
private lemma B3_def : (B 3 : Formula ℕ) = ◇(B 2) ⋏ ◇(C 1) ⋏ ∼◇(C 2) := B_add_two 1
private lemma C3_def : (C 3 : Formula ℕ) = ◇(C 2) ⋏ ◇(B 1) ⋏ ∼◇(B 2) := C_add_two 1
private lemma A0_def : (A 0 : Formula ℕ) = ◇(B 1) ⋏ ◇(C 1) ⋏ ∼◇(B 2) ⋏ ∼◇(C 2) := rfl
private lemma A1_def : (A 1 : Formula ℕ) = ◇(B 2) ⋏ ◇(C 2) ⋏ ∼◇(B 3) ⋏ ∼◇(C 3) := rfl

/-- The forcing data available after extracting the V-shape from `w = d_m ⊩ E` and pinning it
(via `v_shape_classify`) to the upright configuration `(b_{n+1}, b_n, c_{n+1}, c_n)`: the guard
formula `D` and the `K`-block hold at `w`, and the four reference points force the atomic Litak
formulas. Unlike `VShapeForces`, the `K`-block is recorded at `w = d_m` itself (so it is
available before the bound `m ≤ n` is known). -/
structure ShapeData (m n : ℕ) (ψ : World → ℕ → Prop) : Prop where
  hwD : (World.d m) ⊩[⟨frame, ψ⟩] D
  hwK0 : (World.d m) ⊩[⟨frame, ψ⟩] K 0
  hbnB0 : (World.b n) ⊩[⟨frame, ψ⟩] B 0
  hbn1B1 : (World.b (n + 1)) ⊩[⟨frame, ψ⟩] B 1
  hcnC0 : (World.c n) ⊩[⟨frame, ψ⟩] C 0
  hcn1C1 : (World.c (n + 1)) ⊩[⟨frame, ψ⟩] C 1

section

variable (hs : ShapeData m n ψ)

include hs

/-- `K1 0` applied at a reachable point. -/
lemma ShapeData.K1_at (y : World) (hy : R (World.d m) y) (hB1 : y ⊩[⟨frame, ψ⟩] B 1) :
    y ⊩[⟨frame, ψ⟩] (◇(B 0) ⋏ ∼◇(C 0)) := by
  have hK := hs.hwK0
  simp only [K, forces_and] at hK
  have h1 := hK.1
  rw [K1, forces_box] at h1
  exact h1 y hy hB1

/-- `K2 0` applied at a reachable point. -/
lemma ShapeData.K2_at (y : World) (hy : R (World.d m) y) (hC1 : y ⊩[⟨frame, ψ⟩] C 1) :
    y ⊩[⟨frame, ψ⟩] (◇(C 0) ⋏ ∼◇(B 0)) := by
  have hK := hs.hwK0
  simp only [K, forces_and] at hK
  have h2 := hK.2.1
  rw [K2, forces_box] at h2
  exact h2 y hy hC1

/-- `K3 0` applied at a reachable point. -/
lemma ShapeData.K3_at (y : World) (hy : R (World.d m) y) (hB0 : y ⊩[⟨frame, ψ⟩] B 0) :
    y ⊩[⟨frame, ψ⟩] ∼◇(B 1) := by
  have hK := hs.hwK0
  simp only [K, forces_and] at hK
  have h3 := hK.2.2.1
  rw [K3, forces_box] at h3
  exact h3 y hy hB0

/-- `K4 0` applied at a reachable point. -/
lemma ShapeData.K4_at (y : World) (hy : R (World.d m) y) (hC0 : y ⊩[⟨frame, ψ⟩] C 0) :
    y ⊩[⟨frame, ψ⟩] ∼◇(C 1) := by
  have hK := hs.hwK0
  simp only [K, forces_and] at hK
  have h4 := hK.2.2.2
  rw [K4, forces_box] at h4
  exact h4 y hy hC0

/-- Given the bound `m ≤ n`, the `K`-block persists from `w = d_m` to `a_n`, giving the
`VShapeForces` bundle. -/
lemma ShapeData.toVShape (hmn : m ≤ n) : VShapeForces n ψ where
  hK0 := by
    have hR : R (World.d m) (World.a n) := by simp only [R]; omega
    have hK := hs.hwK0
    simp only [K, K1, K2, K3, K4, forces_and] at hK ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hK
    exact ⟨forces_box_of_rel h1 hR, forces_box_of_rel h2 hR, forces_box_of_rel h3 hR,
      forces_box_of_rel h4 hR⟩
  hbnB0 := hs.hbnB0
  hbn1B1 := hs.hbn1B1
  hcnC0 := hs.hcnC0
  hcn1C1 := hs.hcn1C1

/-- `b_{n+2}` forces `B 2` (existence direction). Uses only the `K`-block at `w = d_m` and the
four reference forcings, so it holds for any `m` (no bound `m ≤ n` needed). -/
lemma forces_B2_at : (World.b (n + 2)) ⊩[⟨frame, ψ⟩] B 2 := by
  have hbn1_nC0 : (World.b (n + 1)) ⊩[⟨frame, ψ⟩] ∼◇(C 0) :=
    (forces_and.mp (hs.K1_at (World.b (n + 1)) (by simp only [R]) hs.hbn1B1)).2
  have hcn_nC1 : (World.c n) ⊩[⟨frame, ψ⟩] ∼◇(C 1) :=
      hs.K4_at (World.c n) (by simp only [R]) hs.hcnC0
  rw [B2_def, forces_and, forces_and]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨World.b (n + 1), (by simp only [R]; omega : R (World.b (n + 2)) (World.b (n + 1))),
      hs.hbn1B1⟩
  · exact ⟨World.c n, (by simp only [R]; omega : R (World.b (n + 2)) (World.c n)), hs.hcnC0⟩
  · rw [forces_neg, not_forces_dia]
    intro q hq hqC1
    replace hq : R (World.b (n + 2)) q := hq
    cases q with
    | a k => simp only [R] at hq
    | d k => simp only [R] at hq
    | c k =>
      simp only [R] at hq
      exact (forces_neg.mp hcn_nC1) ⟨World.c k,
          (by simp only [R]; omega : R (World.c n) (World.c k)), hqC1⟩
    | b k =>
      simp only [R] at hq
      obtain ⟨hkC0, hkB0⟩ := forces_and.mp (hs.K2_at (World.b k) (by simp only [R]) hqC1)
      rcases Nat.lt_or_ge k (n + 2) with hlt | hge
      · obtain ⟨r, hbkr, hrC0⟩ := forces_dia.mp hkC0
        exact (forces_neg.mp hbn1_nC0)
          ⟨r, R_trans (by simp only [R]; omega : R (World.b (n + 1)) (World.b k)) hbkr, hrC0⟩
      · have hkeq : k = n + 2 := by omega
        subst hkeq
        exact (forces_neg.mp hkB0) ⟨World.b n,
            (by simp only [R]; omega : R (World.b (n + 2)) (World.b n)),
          hs.hbnB0⟩

/-- `c_{n+2}` forces `C 2` (existence direction), the mirror of `forces_B2_at`. -/
lemma forces_C2_at : (World.c (n + 2)) ⊩[⟨frame, ψ⟩] C 2 := by
  have hcn1_nB0 : (World.c (n + 1)) ⊩[⟨frame, ψ⟩] ∼◇(B 0) :=
    (forces_and.mp (hs.K2_at (World.c (n + 1)) (by simp only [R]) hs.hcn1C1)).2
  have hbn_nB1 : (World.b n) ⊩[⟨frame, ψ⟩] ∼◇(B 1) :=
      hs.K3_at (World.b n) (by simp only [R]) hs.hbnB0
  rw [C2_def, forces_and, forces_and]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨World.c (n + 1), (by simp only [R]; omega : R (World.c (n + 2)) (World.c (n + 1))),
      hs.hcn1C1⟩
  · exact ⟨World.b n, (by simp only [R]; omega : R (World.c (n + 2)) (World.b n)), hs.hbnB0⟩
  · rw [forces_neg, not_forces_dia]
    intro q hq hqB1
    replace hq : R (World.c (n + 2)) q := hq
    cases q with
    | a k => simp only [R] at hq
    | d k => simp only [R] at hq
    | b k =>
      simp only [R] at hq
      exact (forces_neg.mp hbn_nB1) ⟨World.b k,
          (by simp only [R]; omega : R (World.b n) (World.b k)), hqB1⟩
    | c k =>
      simp only [R] at hq
      obtain ⟨hkB0, hkC0⟩ := forces_and.mp (hs.K1_at (World.c k) (by simp only [R]) hqB1)
      rcases Nat.lt_or_ge k (n + 2) with hlt | hge
      · obtain ⟨r, hckr, hrB0⟩ := forces_dia.mp hkB0
        exact (forces_neg.mp hcn1_nB0)
          ⟨r, R_trans (by simp only [R]; omega : R (World.c (n + 1)) (World.c k)) hckr, hrB0⟩
      · have hkeq : k = n + 2 := by omega
        subst hkeq
        exact (forces_neg.mp hkC0) ⟨World.c n,
            (by simp only [R]; omega : R (World.c (n + 2)) (World.c n)),
          hs.hcnC0⟩

/-- On the cone of `d_{n+1}`, `B 1` is forced exactly at `b_{n+1}`. -/
lemma eq_bn1_of_forces_B1 (hmn : m ≤ n) (hRz : R (World.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] B 1) :
    z = World.b (n + 1) := by
  have hd := hs.toVShape hmn
  have hRdm : R (World.d m) z :=
    R_trans (by simp only [R]; omega : R (World.d m) (World.d (n + 1))) hRz
  have hnC0 : z ⊩[⟨frame, ψ⟩] ∼◇(C 0) := (forces_and.mp (hs.K1_at z hRdm h)).2
  cases z with
  | d k =>
    exact absurd
      (show (World.d k) ⊩[⟨frame, ψ⟩] ◇(C 0) from
        ⟨World.c n, (by simp only [R] : R (World.d k) (World.c n)), hs.hcnC0⟩)
      (forces_neg.mp hnC0)
  | a k =>
    simp only [R] at hRz
    exact absurd
      (show (World.a k) ⊩[⟨frame, ψ⟩] ◇(C 0) from
        ⟨World.c n, (by simp only [R]; omega : R (World.a k) (World.c n)), hs.hcnC0⟩)
      (forces_neg.mp hnC0)
  | c k =>
    rcases Nat.lt_or_ge k n with hlt | hge
    · have := (forces_B1_iff_of_vshape hd (by simp only [R]; omega : R (World.a n) (World.c k))).mp
        h
      simp only [reduceCtorEq] at this
    · exact absurd
        (show (World.c k) ⊩[⟨frame, ψ⟩] ◇(C 0) from
          ⟨World.c n, (by simp only [R]; omega : R (World.c k) (World.c n)), hs.hcnC0⟩)
        (forces_neg.mp hnC0)
  | b k =>
    rcases Nat.lt_or_ge k (n + 2) with hlt | hge
    · exact (forces_B1_iff_of_vshape hd (by simp only [R]; omega : R (World.a n) (World.b k))).mp h
    · exact absurd
        (show (World.b k) ⊩[⟨frame, ψ⟩] ◇(C 0) from
          ⟨World.c n, (by simp only [R]; omega : R (World.b k) (World.c n)), hs.hcnC0⟩)
        (forces_neg.mp hnC0)

/-- On the cone of `d_{n+1}`, `C 1` is forced exactly at `c_{n+1}`. -/
lemma eq_cn1_of_forces_C1 (hmn : m ≤ n) (hRz : R (World.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] C 1) :
    z = World.c (n + 1) := by
  have hd := hs.toVShape hmn
  have hRdm : R (World.d m) z :=
    R_trans (by simp only [R]; omega : R (World.d m) (World.d (n + 1))) hRz
  have hnB0 : z ⊩[⟨frame, ψ⟩] ∼◇(B 0) := (forces_and.mp (hs.K2_at z hRdm h)).2
  cases z with
  | d k =>
    exact absurd
      (show (World.d k) ⊩[⟨frame, ψ⟩] ◇(B 0) from
        ⟨World.b n, (by simp only [R] : R (World.d k) (World.b n)), hs.hbnB0⟩)
      (forces_neg.mp hnB0)
  | a k =>
    simp only [R] at hRz
    exact absurd
      (show (World.a k) ⊩[⟨frame, ψ⟩] ◇(B 0) from
        ⟨World.b n, (by simp only [R]; omega : R (World.a k) (World.b n)), hs.hbnB0⟩)
      (forces_neg.mp hnB0)
  | b k =>
    rcases Nat.lt_or_ge k n with hlt | hge
    · have := (forces_C1_iff_of_vshape hd (by simp only [R]; omega : R (World.a n) (World.b k))).mp
        h
      simp only [reduceCtorEq] at this
    · exact absurd
        (show (World.b k) ⊩[⟨frame, ψ⟩] ◇(B 0) from
          ⟨World.b n, (by simp only [R]; omega : R (World.b k) (World.b n)), hs.hbnB0⟩)
        (forces_neg.mp hnB0)
  | c k =>
    rcases Nat.lt_or_ge k (n + 2) with hlt | hge
    · exact (forces_C1_iff_of_vshape hd (by simp only [R]; omega : R (World.a n) (World.c k))).mp h
    · exact absurd
        (show (World.c k) ⊩[⟨frame, ψ⟩] ◇(B 0) from
          ⟨World.b n, (by simp only [R]; omega : R (World.c k) (World.b n)), hs.hbnB0⟩)
        (forces_neg.mp hnB0)

/-- On the cone of `d_{n+1}`, `B 2` is forced exactly at `b_{n+2}`. -/
lemma eq_bn2_of_forces_B2 (hmn : m ≤ n) (hRz : R (World.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] B 2) :
    z = World.b (n + 2) := by
  rw [B2_def, forces_and, forces_and] at h
  obtain ⟨hB1dia, hC0dia, hnC1⟩ := h
  obtain ⟨y1, hzy1, hy1B1⟩ := forces_dia.mp hB1dia
  have hy1 := eq_bn1_of_forces_B1 hs hmn (R_trans hRz hzy1) hy1B1
  subst hy1
  replace hzy1 : R z (World.b (n + 1)) := hzy1
  cases z with
  | a k =>
    simp only [R] at hRz
    exact absurd
      (show (World.a k) ⊩[⟨frame, ψ⟩] ◇(C 1) from
        ⟨World.c (n + 1), (by simp only [R]; omega : R (World.a k) (World.c (n + 1))), hs.hcn1C1⟩)
      (forces_neg.mp hnC1)
  | d k =>
    exact absurd
      (show (World.d k) ⊩[⟨frame, ψ⟩] ◇(C 1) from
        ⟨World.c (n + 1), (by simp only [R] : R (World.d k) (World.c (n + 1))), hs.hcn1C1⟩)
      (forces_neg.mp hnC1)
  | c k =>
    simp only [R] at hzy1
    exact absurd
      (show (World.c k) ⊩[⟨frame, ψ⟩] ◇(C 1) from
        ⟨World.c (n + 1), (by simp only [R]; omega : R (World.c k) (World.c (n + 1))), hs.hcn1C1⟩)
      (forces_neg.mp hnC1)
  | b k =>
    simp only [R] at hzy1
    have h2 : k ≤ n + 2 := by
      by_contra hc
      push Not at hc
      exact (forces_neg.mp hnC1)
        ⟨World.c (n + 1), (by simp only [R]; omega : R (World.b k) (World.c (n + 1))), hs.hcn1C1⟩
    have hk : k = n + 1 ∨ k = n + 2 := by omega
    rcases hk with rfl | rfl
    · exfalso
      have hnC0 := (forces_and.mp (hs.K1_at (World.b (n + 1)) (by simp only [R]) hs.hbn1B1)).2
      exact (forces_neg.mp hnC0) hC0dia
    · rfl

/-- On the cone of `d_{n+1}`, `C 2` is forced exactly at `c_{n+2}`. -/
lemma eq_cn2_of_forces_C2 (hmn : m ≤ n) (hRz : R (World.d (n + 1)) z) (h : z ⊩[⟨frame, ψ⟩] C 2) :
    z = World.c (n + 2) := by
  rw [C2_def, forces_and, forces_and] at h
  obtain ⟨hC1dia, hB0dia, hnB1⟩ := h
  obtain ⟨y1, hzy1, hy1C1⟩ := forces_dia.mp hC1dia
  have hy1 := eq_cn1_of_forces_C1 hs hmn (R_trans hRz hzy1) hy1C1
  subst hy1
  replace hzy1 : R z (World.c (n + 1)) := hzy1
  cases z with
  | a k =>
    simp only [R] at hRz
    exact absurd
      (show (World.a k) ⊩[⟨frame, ψ⟩] ◇(B 1) from
        ⟨World.b (n + 1), (by simp only [R]; omega : R (World.a k) (World.b (n + 1))), hs.hbn1B1⟩)
      (forces_neg.mp hnB1)
  | d k =>
    exact absurd
      (show (World.d k) ⊩[⟨frame, ψ⟩] ◇(B 1) from
        ⟨World.b (n + 1), (by simp only [R] : R (World.d k) (World.b (n + 1))), hs.hbn1B1⟩)
      (forces_neg.mp hnB1)
  | b k =>
    simp only [R] at hzy1
    exact absurd
      (show (World.b k) ⊩[⟨frame, ψ⟩] ◇(B 1) from
        ⟨World.b (n + 1), (by simp only [R]; omega : R (World.b k) (World.b (n + 1))), hs.hbn1B1⟩)
      (forces_neg.mp hnB1)
  | c k =>
    simp only [R] at hzy1
    have h2 : k ≤ n + 2 := by
      by_contra hc
      push Not at hc
      exact (forces_neg.mp hnB1)
        ⟨World.b (n + 1), (by simp only [R]; omega : R (World.c k) (World.b (n + 1))), hs.hbn1B1⟩
    have hk : k = n + 1 ∨ k = n + 2 := by omega
    rcases hk with rfl | rfl
    · exfalso
      have hnB0 := (forces_and.mp (hs.K2_at (World.c (n + 1)) (by simp only [R]) hs.hcn1C1)).2
      exact (forces_neg.mp hnB0) hB0dia
    · rfl

/-- No point in the cone of `d_{n+1}` forces `A 0`: the unique `A 0`-point `a_n` is not
reachable from `d_{n+1}`. -/
lemma not_dia_A0_at (hmn : m ≤ n) : (World.d (n + 1)) ⊩[⟨frame, ψ⟩] ∼◇(A 0) := by
  rw [forces_neg, not_forces_dia]
  intro z hz hzA0
  rw [A0_def, forces_and, forces_and, forces_and] at hzA0
  obtain ⟨hB1dia, hC1dia, hnB2, hnC2⟩ := hzA0
  obtain ⟨y1, hzy1, hy1B1⟩ := forces_dia.mp hB1dia
  have hey1 := eq_bn1_of_forces_B1 hs hmn (R_trans hz hzy1) hy1B1
  subst hey1
  obtain ⟨y2, hzy2, hy2C1⟩ := forces_dia.mp hC1dia
  have hey2 := eq_cn1_of_forces_C1 hs hmn (R_trans hz hzy2) hy2C1
  subst hey2
  have hB2 := forces_B2_at hs
  have hC2 := forces_C2_at hs
  replace hz : R (World.d (n + 1)) z := hz
  replace hzy1 : R z (World.b (n + 1)) := hzy1
  replace hzy2 : R z (World.c (n + 1)) := hzy2
  cases z with
  | d k =>
    exact (forces_neg.mp hnB2) ⟨World.b (n + 2),
        (by simp only [R] : R (World.d k) (World.b (n + 2))), hB2⟩
  | a k =>
    simp only [R] at hz
    exact (forces_neg.mp hnB2)
      ⟨World.b (n + 2), (by simp only [R]; omega : R (World.a k) (World.b (n + 2))), hB2⟩
  | b k =>
    simp only [R] at hzy2
    exact (forces_neg.mp hnB2)
      ⟨World.b (n + 2), (by simp only [R]; omega : R (World.b k) (World.b (n + 2))), hB2⟩
  | c k =>
    simp only [R] at hzy1
    exact (forces_neg.mp hnC2)
      ⟨World.c (n + 2), (by simp only [R]; omega : R (World.c k) (World.c (n + 2))), hC2⟩

/-- `a_{n+1}` forces `A 1`. -/
lemma forces_A1_at (hmn : m ≤ n) : (World.a (n + 1)) ⊩[⟨frame, ψ⟩] A 1 := by
  rw [A1_def, forces_and, forces_and, forces_and]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨World.b (n + 2), (by simp only [R]; omega : R (World.a (n + 1)) (World.b (n + 2))),
      forces_B2_at hs⟩
  · exact ⟨World.c (n + 2), (by simp only [R]; omega : R (World.a (n + 1)) (World.c (n + 2))),
      forces_C2_at hs⟩
  · rw [forces_neg, not_forces_dia]
    intro p hp hpB3
    rw [B3_def, forces_and, forces_and] at hpB3
    obtain ⟨hB2dia, hC1dia, hnC2⟩ := hpB3
    obtain ⟨q2, hpq2, hq2B2⟩ := forces_dia.mp hB2dia
    have heq2 := eq_bn2_of_forces_B2 hs hmn
      (R_trans (by simp only [R]; omega : R (World.d (n + 1)) (World.a (n + 1))) (R_trans hp hpq2))
          hq2B2
    subst heq2
    obtain ⟨q1, hpq1, hq1C1⟩ := forces_dia.mp hC1dia
    have heq1 := eq_cn1_of_forces_C1 hs hmn
      (R_trans (by simp only [R]; omega : R (World.d (n + 1)) (World.a (n + 1))) (R_trans hp hpq1))
          hq1C1
    subst heq1
    replace hp : R (World.a (n + 1)) p := hp
    replace hpq1 : R p (World.c (n + 1)) := hpq1
    replace hpq2 : R p (World.b (n + 2)) := hpq2
    cases p with
    | d j => simp only [R] at hp
    | a j =>
      simp only [R] at hp
      subst hp
      exact (forces_neg.mp hnC2)
        ⟨World.c (n + 2), (by simp only [R]; omega : R (World.a (n + 1)) (World.c (n + 2))),
            forces_C2_at hs⟩
    | b j =>
      simp only [R] at hp hpq1
      omega
    | c j =>
      simp only [R] at hp hpq2
      omega
  · rw [forces_neg, not_forces_dia]
    intro p hp hpC3
    rw [C3_def, forces_and, forces_and] at hpC3
    obtain ⟨hC2dia, hB1dia, hnB2⟩ := hpC3
    obtain ⟨q2, hpq2, hq2C2⟩ := forces_dia.mp hC2dia
    have heq2 := eq_cn2_of_forces_C2 hs hmn
      (R_trans (by simp only [R]; omega : R (World.d (n + 1)) (World.a (n + 1))) (R_trans hp hpq2))
          hq2C2
    subst heq2
    obtain ⟨q1, hpq1, hq1B1⟩ := forces_dia.mp hB1dia
    have heq1 := eq_bn1_of_forces_B1 hs hmn
      (R_trans (by simp only [R]; omega : R (World.d (n + 1)) (World.a (n + 1))) (R_trans hp hpq1))
          hq1B1
    subst heq1
    replace hp : R (World.a (n + 1)) p := hp
    replace hpq1 : R p (World.b (n + 1)) := hpq1
    replace hpq2 : R p (World.c (n + 2)) := hpq2
    cases p with
    | d j => simp only [R] at hp
    | a j =>
      simp only [R] at hp
      subst hp
      exact (forces_neg.mp hnB2)
        ⟨World.b (n + 2), (by simp only [R]; omega : R (World.a (n + 1)) (World.b (n + 2))),
            forces_B2_at hs⟩
    | b j =>
      simp only [R] at hp hpq2
      omega
    | c j =>
      simp only [R] at hp hpq1
      omega

/-- Any point of the cone of `w = d_m` forcing `A 0` and seeing the `B 1`-point `b_{n+1}` and
the `C 1`-point `c_{n+1}` is the apex `a_n`. Combined with `w ≺ z` this pins the V-shape apex,
and (via `w = d_m ≺ a_n`) forces the bound `m ≤ n`. -/
lemma apex_eq {z : World} (hzA0 : z ⊩[⟨frame, ψ⟩] A 0)
    (hRzb : R z (World.b (n + 1))) (hRzc : R z (World.c (n + 1))) : z = World.a n := by
  rw [A0_def, forces_and, forces_and, forces_and] at hzA0
  obtain ⟨_, _, hnB2, hnC2⟩ := hzA0
  have hB2 := forces_B2_at hs
  have hC2 := forces_C2_at hs
  cases z with
  | d k =>
    exact absurd (show (World.d k) ⊩[⟨frame, ψ⟩] ◇(B 2) from
      ⟨World.b (n + 2), (by simp only [R] : R (World.d k) (World.b (n + 2))),
          hB2⟩) (forces_neg.mp hnB2)
  | b k =>
    simp only [R] at hRzb hRzc
    exact absurd (show (World.b k) ⊩[⟨frame, ψ⟩] ◇(B 2) from
      ⟨World.b (n + 2), (by simp only [R]; omega : R (World.b k) (World.b (n + 2))),
          hB2⟩) (forces_neg.mp hnB2)
  | c k =>
    simp only [R] at hRzb hRzc
    exact absurd (show (World.c k) ⊩[⟨frame, ψ⟩] ◇(C 2) from
      ⟨World.c (n + 2), (by simp only [R]; omega : R (World.c k) (World.c (n + 2))),
          hC2⟩) (forces_neg.mp hnC2)
  | a k =>
    simp only [R] at hRzb hRzc
    have hkn : k ≤ n := by
      by_contra hc
      push Not at hc
      exact (forces_neg.mp hnB2)
        ⟨World.b (n + 2), (by simp only [R]; omega : R (World.a k) (World.b (n + 2))), hB2⟩
    rw [show k = n by omega]

end

/-! ### Assembly: frame validates `G` -/

/-- From `d_m ⊩ D`, every `d`-point at index `≥ m` forces `p0 ⋎ p1`: the fourth conjunct of `D`
makes `∼(p0 ⋎ p1)` upward-closed, so `p0 ⋎ p1` is inherited downward from the arbitrarily large
chain points supplied by `exists_ge_forces_p0_or_p1`. -/
lemma forces_p01_at (hD : (World.d m) ⊩[⟨frame, ψ⟩] D) (k : ℕ) (hk : m ≤ k) :
    (World.d k) ⊩[⟨frame, ψ⟩] (p0 ⋎ p1) := by
  obtain ⟨k', hkk', hk'01⟩ := exists_ge_forces_p0_or_p1 hD k
  by_contra hcon
  simp only [D, forces_and] at hD
  obtain ⟨_, _, _, hbox3⟩ := hD
  rw [forces_box] at hbox3
  have himp := hbox3 (World.d k) (by simp only [R]; omega : R (World.d m) (World.d k))
  have hbox := himp (forces_neg.mpr hcon)
  rw [forces_box] at hbox
  exact (forces_neg.mp (hbox (World.d k') (by simp only [R]; omega : R (World.d k) (World.d k'))))
      hk'01

/-- The upright core of `validates_G`: from the V-shape data (with reference forcings in the
`(b_{n+1}, b_n, c_{n+1}, c_n)` configuration) and the apex `t` forcing `A 0` and seeing
`b_{n+1}`/`c_{n+1}`, the point `w = d_m` forces `F`. The witness is `d_{n+1}`. -/
lemma forces_F_of_shapeAndApex (hs : ShapeData m n ψ) {t : World}
    (hwt : R (World.d m) t) (htA0 : t ⊩[⟨frame, ψ⟩] A 0)
    (hRtb : R t (World.b (n + 1))) (hRtc : R t (World.c (n + 1))) :
    (World.d m) ⊩[⟨frame, ψ⟩] F := by
  have hta : t = World.a n := apex_eq hs htA0 hRtb hRtc
  subst hta
  have hmn : m ≤ n := by simpa only [R] using hwt
  rw [F]
  refine ⟨World.d (n + 1), (by simp only [R]; omega : R (World.d m) (World.d (n + 1))), ?_⟩
  rw [forces_and, forces_and]
  refine ⟨?_, ?_, ?_⟩
  · exact forces_p01_at hs.hwD (n + 1) (by omega)
  · exact not_dia_A0_at hs hmn
  · exact ⟨World.a (n + 1), (by simp only [R]; omega : R (World.d (n + 1)) (World.a (n + 1))),
      forces_A1_at hs hmn⟩

/-- Fine's frame validates `G`: for every valuation and every point, `E → F` holds.

- [Fin74a, Lemma 2]
- [Lit04, p. 332] -/
theorem validates_G : frame ⊧ G := by
  intro ψ w
  rw [G]
  intro hE
  obtain ⟨t, u₀, u₁, v₀, v₁, hwt, htA0, htu1, hu1u0, htv1, hv1v0,
    hu1B1, hu0B0, hv1C1, hv0C0, hnu0u1, hnv0v1, hnu1v0, hnv1u0⟩ := exists_V_shape hE
  obtain ⟨hD, _, hK0⟩ := forces_E_iff.mp hE
  obtain ⟨m, rfl⟩ := exists_d_of_forces_D hD
  obtain ⟨n, hcase⟩ := v_shape_classify htu1 hu1u0 htv1 hv1v0 hnu0u1 hnv0v1 hnu1v0 hnv1u0
  rcases hcase with ⟨e1, e0, f1, f0⟩ | ⟨e1, e0, f1, f0⟩
  · subst e1; subst e0; subst f1; subst f0
    exact forces_F_of_shapeAndApex ⟨hD, hK0, hu0B0, hu1B1, hv0C0, hv1C1⟩ hwt htA0 htu1 htv1
  · subst e1; subst e0; subst f1; subst f0
    -- mirror case: transport to the `ψ ∘ swap` valuation, where the roles of `b`/`c` are
    -- exchanged, run the upright core, and transport `F` back (`w = d_m` is fixed by `swap`).
    have hswapD : (swap (World.d m)) = World.d m := rfl
    have hsD : (World.d m) ⊩[⟨frame, ψ ∘ swap⟩] D := by
      have := forces_swap_iff.mp hD; rwa [hswapD] at this
    have hsK0 : (World.d m) ⊩[⟨frame, ψ ∘ swap⟩] K 0 := by
      have := forces_swap_iff.mp hK0; rwa [hswapD] at this
    have hsbnB0 : (World.b n) ⊩[⟨frame, ψ ∘ swap⟩] B 0 := by
      have := forces_swap_iff.mp hu0B0; simpa only [swap] using this
    have hsbn1B1 : (World.b (n + 1)) ⊩[⟨frame, ψ ∘ swap⟩] B 1 := by
      have := forces_swap_iff.mp hu1B1; simpa only [swap] using this
    have hscnC0 : (World.c n) ⊩[⟨frame, ψ ∘ swap⟩] C 0 := by
      have := forces_swap_iff.mp hv0C0; simpa only [swap] using this
    have hscn1C1 : (World.c (n + 1)) ⊩[⟨frame, ψ ∘ swap⟩] C 1 := by
      have := forces_swap_iff.mp hv1C1; simpa only [swap] using this
    have hstA0 : (swap t) ⊩[⟨frame, ψ ∘ swap⟩] A 0 := forces_swap_iff.mp htA0
    have hswt : R (World.d m) (swap t) := by
      have : R (swap (World.d m)) (swap t) := R_swap.mpr hwt; rwa [hswapD] at this
    have hRtb : R (swap t) (World.b (n + 1)) := by
      have : R (swap t) (swap (World.c (n + 1))) := R_swap.mpr htu1; simpa only [swap] using this
    have hRtc : R (swap t) (World.c (n + 1)) := by
      have : R (swap t) (swap (World.b (n + 1))) := R_swap.mpr htv1; simpa only [swap] using this
    have hF : (World.d m) ⊩[⟨frame, ψ ∘ swap⟩] F :=
      forces_F_of_shapeAndApex ⟨hsD, hsK0, hsbnB0, hsbn1B1, hscnC0, hscn1C1⟩ hswt hstA0 hRtb hRtc
    have : (swap (World.d m)) ⊩[⟨frame, ψ ∘ swap⟩] F := by rwa [hswapD]
    exact forces_swap_iff.mpr this

end Fine

end
