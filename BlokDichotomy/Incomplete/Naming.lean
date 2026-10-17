module

public import BlokDichotomy.Incomplete.Transfer
public import BlokDichotomy.Incomplete.Companion

/-!
# Naming the points of the hooked frames

The formulas `delta`, `pi`, `alpha`, `theta`, `gamma` name points of the hooked frame, and
`gammaLöb` is valid in it.

## References

- [CZ98, Example 10.57, Example 10.58, p. 365]
-/

@[expose] public section

universe u

namespace HookData

open World Naming Formula Model.World

variable {κ : Type u} {D : HookData κ} {I : Set ℕ} {N : ℕ} {V : D.World I → ℕ → Prop}

section Rel

variable {x y : (D.hookFrame I).World}

lemma not_isUnwound_of_rel (hx : ¬x.IsUnwound) (hxd : x ≠ .d 0 (Nat.zero_le _)) (Rxy : x ≺ y) :
    ¬y.IsUnwound := by
  cases x <;> cases y <;> simp_all [Rel, IsUnwound];

lemma ne_dBot_of_rel (hx : x ≠ .dBot) (hxd : x ≠ .d 0 (Nat.zero_le _)) (Rxy : x ≺ y) :
    y ≠ .dBot := by
  rintro rfl;
  rcases rel_to_dBot_iff.mp Rxy with h | ⟨rfl, -⟩;
  · exact hxd h;
  · exact hx rfl;

lemma two_le_m : 2 ≤ D.m := by
  have := D.card_add_len_lt;
  omega;

end Rel


section Naming

def Reaches (D : HookData κ) (I : Set ℕ) (N : ℕ) : Prop :=
  ∀ x : (D.hookFrame I).World, ¬x.IsUnwound → x ≠ .dBot → ∀ y, ∃ n ≤ N, x ≺^[n] y

variable (hreach : D.Reaches I N) (h₁ : ∃ w, V w 0) (h₂ : ∃ w, ¬V w 0)

local notation "𝓜" => GeneralFrame.model (HookData.hooked D I) V

lemma forces_tau_dBot : (.dBot : D.World I) ⊩[𝓜] tau N := by
  rw [forces_tau];
  by_cases h : V .dBot 0;
  · exact Or.inl fun _ _ y hy => (eq_dBot_of_dBot_relItr hy) ▸ h;
  · exact Or.inr fun _ _ y hy => (eq_dBot_of_dBot_relItr hy) ▸ h;

include hreach h₁ h₂

lemma not_forces_tau_of_ne_dBot {x : D.World I} (hx : ¬x.IsUnwound) (hxd : x ≠ .dBot) :
    x ⊮[𝓜] tau N :=
  not_forces_tau_of_reach (hreach x hx hxd) h₁ h₂

lemma forces_delta_zero_iff {x : D.World I} (hx : ¬x.IsUnwound) :
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
lemma forces_delta_iff {j : ℕ} (hj : j ≤ D.m) {x : D.World I} (hx : ¬x.IsUnwound) :
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

lemma forces_pi_d : ∀ j (hj : j ≤ D.m), (.d j hj : D.World I) ⊩[𝓜] pi N j
  | 0, _ => (forces_delta_zero_iff hreach h₁ h₂ (by simp [IsUnwound])).mpr rfl
  | j + 1, hj => forces_pi_succ.mpr
      ⟨(forces_delta_iff hreach h₁ h₂ hj (by simp [IsUnwound])).mpr rfl, World.d j (by omega), rfl,
        forces_pi_d j (by omega)⟩

lemma exists_isUnwound_forces_delta {j : ℕ} (hj : j ≤ D.m) {x : D.World I} (hx : x.IsUnwound)
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
lemma forces_pi_iff [Finite D.F.World] {x : D.World I} :
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
lemma forces_dia_alpha_iff_of {φ : Formula ℕ} {i : ℕ}
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
lemma forces_alpha_iff (i : ℕ) {x : D.World I} :
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
lemma forces_theta_iff {x : D.World I} :
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
lemma forces_löb_b (hV : (D.hooked I).IsAdmissible V) : (.b : D.World I) ⊩[𝓜] löb N D.m := by
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

end HookData

end
