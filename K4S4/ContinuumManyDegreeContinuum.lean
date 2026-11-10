module

public import BlokDichotomy.Modal.Blok
public import K4S4.Construction.Logic
public import K4S4.Kripke.Degree

/-!
# Continuum many complete logics from independent membership patterns

The even indices distinguish frame companions, and the odd indices distinguish
Kripke-complete normal extensions of `S4`.
-/

@[expose] public section

namespace Modal.K4S4

open NormalLogic

section Construction

variable {L : NormalLogic ℕ} {H C : Set ℕ → NormalLogic ℕ} {χ : ℕ → Formula ℕ}
  (hL : L.KripkeComplete.{0} fun _ _ => True)
  (hH₀ : ∀ I, (H I).IsNExt 𝐒𝟒)
  (hC₀ : ∀ J, (C J).IsNExt 𝐒𝟒)
  (hH : ∀ I, FrameEquiv.{0} (fun _ _ => True) (H I) L)
  (hC : ∀ J, (C J).KripkeComplete.{0} fun _ _ => True)
  (hχL : ∀ n, χ n ∈ L)
  (hχH : ∀ I n, χ n ∈ H I ↔ n ∉ I)
  (hχC : ∀ J n, χ n ∈ C J ↔ n ∉ J)

private lemma injective_of_membership_pattern (f : Set ℕ → NormalLogic ℕ)
    (ψ : ℕ → Formula ℕ) (h : ∀ I n, ψ n ∈ f I ↔ n ∉ I) : Function.Injective f := by
  intro I J hIJ;
  ext n;
  apply not_iff_not.mp;
  rw [← h I n, ← h J n, hIJ];

include hχL hχC in
private lemma complete_family_injective :
    Function.Injective fun J => L ∩ C ((fun n => 2 * n + 1) '' J) := by
  apply injective_of_membership_pattern _ (fun n => χ (2 * n + 1));
  intro J n;
  change (χ (2 * n + 1) ∈ L ∧ χ (2 * n + 1) ∈ C ((fun n => 2 * n + 1) '' J)) ↔ _;
  simp [hχL, hχC];

include hχH hχC in
private lemma companion_family_injective (J : Set ℕ) :
    Function.Injective fun I => H ((fun n => 2 * n) '' I) ∩ C ((fun n => 2 * n + 1) '' J) := by
  apply injective_of_membership_pattern _ (fun n => χ (2 * n));
  intro I n;
  have hn : 2 * n ∉ ((fun n => 2 * n + 1) '' J) := by
    rintro ⟨m, _, h⟩;
    change 2 * m + 1 = 2 * n at h;
    omega;
  change (χ (2 * n) ∈ H ((fun n => 2 * n) '' I) ∧
    χ (2 * n) ∈ C ((fun n => 2 * n + 1) '' J)) ↔ _;
  simp [hχH, hχC, hn];

variable [L.IsNExt 𝐒𝟒]

include hH₀ hC₀ hH hχH hχC in
private theorem complete_family_degree (J : Set ℕ) :
    (L ∩ C ((fun n => 2 * n + 1) '' J)).degree.{0} 𝐒𝟒 (fun _ _ => True) = Cardinal.continuum := by
  let := hH₀;
  let := hC₀;
  let f : Set ℕ → (L ∩ C ((fun n => 2 * n + 1) '' J)).Companion 𝐒𝟒 (fun _ _ => True) := fun I =>
    ⟨H ((fun n => 2 * n) '' I) ∩ C ((fun n => 2 * n + 1) '' J),
      inferInstance, ((hH _).inter .refl).symm⟩;
  apply le_antisymm degree_le_continuum;
  rw [← Cardinal.mk_set_nat];
  apply Cardinal.mk_le_of_injective (f := f);
  intro I I' h;
  exact companion_family_injective hχH hχC J <| congrArg Subtype.val h;

include hL hH₀ hC₀ hH hC hχL hχH hχC in
/-- Independent membership patterns yield continuum many pairwise frame-inequivalent
Kripke-complete normal extensions of `S4`, each of continuum degree in `NExt S4`. -/
theorem exists_complete_continuum_degree_family_of_patterns :
    ∃ Q : Set ℕ → NormalLogic ℕ,
      (∀ J, (Q J).IsNExt 𝐒𝟒 ∧ (Q J).KripkeComplete.{0} (fun _ _ => True) ∧
        (Q J).degree.{0} 𝐒𝟒 (fun _ _ => True) = Cardinal.continuum) ∧
      (∀ I J, FrameEquiv.{0} (fun _ _ => True) (Q I) (Q J) → I = J) := by
  let := hC₀;
  use fun J => L ∩ C ((fun n => 2 * n + 1) '' J);
  constructor;
  · intro J;
    exact ⟨inferInstance, hL.inter (hC _), complete_family_degree hH₀ hC₀ hH hχH hχC J⟩;
  · intro I J h;
    apply complete_family_injective hχL hχC;
    exact (kripkeComplete_iff_frameLogic_eq.mp <| hL.inter (hC _)).symm.trans <|
      h.frameLogic_eq.trans <| kripkeComplete_iff_frameLogic_eq.mp <| hL.inter (hC _);

end Construction

open Construction

/-- There are continuum many pairwise frame-inequivalent Kripke-complete normal
extensions of `S4`, each of continuum degree in `NExt S4`. -/
theorem exists_complete_continuum_degree_family :
    ∃ Q : Set ℕ → NormalLogic ℕ,
      (∀ J, (Q J).IsNExt 𝐒𝟒 ∧ (Q J).KripkeComplete.{0} (fun _ _ => True) ∧
        (Q J).degree.{0} 𝐒𝟒 (fun _ _ => True) = Cardinal.continuum) ∧
      (∀ I J, FrameEquiv.{0} (fun _ _ => True) (Q I) (Q J) → I = J) := by
  apply exists_complete_continuum_degree_family_of_patterns
    (L := baseLogic.frameLogic.{0} (fun _ _ => True)) (H := sourceLogic)
    (C := fun I => (frame I).logic) (χ := chi);
  · exact kripkeComplete_frameLogic;
  · exact fun _ => inferInstance;
  · exact fun _ => inferInstance;
  · exact sourceLogic_frameEquiv;
  · exact fun I => (frame I).kripkeComplete_logic trivial;
  · exact chi_mem_frameLogic;
  · exact fun _ => chi_mem_sourceLogic_iff;
  · exact fun _ _ => frame_validates_chi;

/-- Exactly continuum many Kripke-complete normal extensions of `S4` have continuum
degree in `NExt S4`, with frame equivalence tested on all Kripke frames in `Type`. -/
theorem mk_complete_continuum_degree_eq_continuum :
    Cardinal.mk {A : NormalLogic ℕ // A.IsNExt 𝐒𝟒 ∧
      A.KripkeComplete.{0} (fun _ _ => True) ∧
      A.degree.{0} 𝐒𝟒 (fun _ _ => True) = Cardinal.continuum} = Cardinal.continuum := by
  obtain ⟨Q, hQ, hQ'⟩ := exists_complete_continuum_degree_family;
  apply le_antisymm;
  · calc
      _ ≤ Cardinal.mk (Set (Formula ℕ)) :=
        Cardinal.mk_le_of_injective
          (f := fun A : {A : NormalLogic ℕ // A.IsNExt 𝐒𝟒 ∧
            A.KripkeComplete.{0} (fun _ _ => True) ∧
            A.degree.{0} 𝐒𝟒 (fun _ _ => True) = Cardinal.continuum} =>
              (A.1 : Set (Formula ℕ)))
          fun _ _ h => Subtype.ext <| SetLike.coe_injective h
      _ = 2 ^ Cardinal.mk (Formula ℕ) := Cardinal.mk_set
      _ ≤ 2 ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left two_ne_zero Cardinal.mk_le_aleph0
      _ = Cardinal.continuum := Cardinal.two_power_aleph0
  · calc
      Cardinal.continuum = Cardinal.mk (Set ℕ) := Cardinal.mk_set_nat.symm
      _ ≤ _ := Cardinal.mk_le_of_injective
        (f := fun J => ⟨Q J, hQ J⟩) fun I J h => hQ' I J <| by
          have h' : Q I = Q J := congrArg Subtype.val h;
          rw [h'];

end Modal.K4S4
