module

public import BlokDichotomy.Modal.Kripke.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Continuum many consistent normal logics

`logicMaks 𝔸` is `𝐊` extended by the axioms `axiomMaks n` for `n ∈ 𝔸`. The map `logicMaks` is
injective with consistent values, so there are exactly `𝔠` consistent normal logics over `ℕ`.
-/

@[expose]
public section

namespace Modal

universe u v

variable {κ : Type u} {α : Type v}

/-- `□(farthest n 🡒 #0) ⋎ □(farthest n 🡒 ∼#0)`. -/
abbrev axiomMaks (n : ℕ) : Formula ℕ := □((farthest n) 🡒 #0) ⋎ □((farthest n) 🡒 ∼#0)

namespace Frame

open Model.World

lemma iff_validate_axiomMaks {F : Frame κ} {n : ℕ} : F ⊧ (axiomMaks n) ↔
  (∀ x : F.World, ∀ y z, x ≺ y → x ≺ z → ∀ V,
    y ⊩[(⟨F, V⟩ : Model _ ℕ)] ◇^[n]⊤ ⋏ ∼◇^[(n + 1)]⊤ →
    z ⊩[⟨F, V⟩] ◇^[n]⊤ ⋏ ∼◇^[(n + 1)]⊤ →
    y = z
  ) := by
  constructor;
  · contrapose!;
    rintro ⟨x, y, z, Rxy, Rxz, V, hy, hz, nyz⟩;
    rw [forces_and, forces_multidia_top, forces_neg_multidia_top] at hy hz;
    obtain ⟨⟨y', Ryy'⟩, hy⟩ := hy;
    obtain ⟨⟨z', Rzz'⟩, hz⟩ := hz;
    unfold axiomMaks Frame.Validates Model.Validates;
    push Not;
    use fun x a => x ≠ y, x;
    grind;
  · grind;

end Frame



abbrev logicMaks (𝔸 : Set ℕ) : NormalLogic ℕ := 𝐊 + 𝔸.image axiomMaks

abbrev logicVer : NormalLogic α := 𝐊 + ({ □φ | φ } : FormulaSet α)


section Ver


namespace Frame

lemma validates_box_deadEnd {φ : Formula α} : deadEnd ⊧ (□φ) := by
  intro V x;
  apply Model.World.forces_box.mpr;
  grind;

lemma validates_logicVer_deadEnd : deadEnd ⊧ (logicVer : NormalLogic α) := by
  apply validates_add validates_logicK;
  rintro φ ⟨ψ, rfl⟩;
  exact validates_box_deadEnd;

end Frame


lemma not_mem_bot_logicVer : (⊥ : Formula α) ∉ logicVer :=
  Frame.not_mem_bot_of_validates Frame.validates_logicVer_deadEnd

lemma consistent_logicVer : (logicVer : NormalLogic α).Consistent :=
  Frame.consistent_of_validates Frame.validates_logicVer_deadEnd

end Ver


section Maks

variable {𝔸 𝔹 : Set ℕ}

lemma logicMaks_le_logicVer : logicMaks 𝔸 ≤ logicVer := by
  apply NormalLogic.add_le NormalLogic.le_add;
  rintro φ ⟨n, -, rfl⟩;
  have h₁ : □(farthest n 🡒 ∼#0) ∈ logicVer := NormalLogic.mem_add ⟨_, rfl⟩;
  have h₂ : □(farthest n 🡒 ∼#0) 🡒 ∼□(farthest n 🡒 #0) 🡒 □(farthest n 🡒 ∼#0) ∈ logicVer :=
    NormalLogic.mem_add_of_mem <| NormalLogic.mem_ofSet <| FormulaSet.axiomsK.imply₁;
  exact NormalLogic.mem_mdp h₁ h₂;

lemma not_mem_bot_logicMaks : ⊥ ∉ logicMaks 𝔸 :=
  fun h => not_mem_bot_logicVer <| logicMaks_le_logicVer h

lemma consistent_logicMaks : (logicMaks 𝔸).Consistent :=
  NormalLogic.Consistent.of_le logicMaks_le_logicVer consistent_logicVer

@[gcongr]
lemma logicMaks_mono (h : 𝔸 ⊆ 𝔹) : logicMaks 𝔸 ≤ logicMaks 𝔹 :=
  NormalLogic.add_mono le_rfl <| Set.image_mono h

open Model.World


private abbrev frameMaks (n : ℕ) : Frame (Unit ⊕ (Fin 2 × ℕ)) := ⟨fun x y =>
  match x, y with
  | .inl (),     .inr (_, l) => l = 0
  | .inr (i, k), .inr (j, l) => i = j ∧ l = k + 1 ∧ l ≤ n
  | _, _ => False
⟩

namespace frameMaks

variable {n m j k : ℕ} {i : Fin 2}

private lemma iff_relItr_inr {x : (frameMaks n).World} (hk : k ≤ n) :
  ((.inr (i, k)) ≺^[j] x) ↔ (k + j ≤ n ∧ x = .inr (i, k + j)) := by
  induction j generalizing k with
  | zero => simp_all [eq_comm];
  | succ j ih =>
    rw [Frame.iff_relItr_succ];
    constructor;
    · rintro ⟨(⟨⟩ | ⟨i', k'⟩), Rkk', Rk'x⟩;
      · contradiction;
      · obtain ⟨rfl, rfl, hk'⟩ := Rkk';
        grind;
    · rintro ⟨h₁, rfl⟩;
      use .inr (i, k + 1);
      grind;

private lemma forces_farthest {V} :
    (Sum.inr (i, 0)) ⊩[(⟨frameMaks n, V⟩ : Model _ ℕ)] farthest n := by
  apply iff_forces_farthest.mpr;
  constructor;
  · refine ⟨.inr (i, n), ?_⟩;
    rw [iff_relItr_inr (by omega)];
    simp;
  · intro y R0y;
    rw [iff_relItr_inr (by omega)] at R0y;
    obtain ⟨h, -⟩ := R0y;
    omega;

private lemma not_validates_axiomMaks : (frameMaks n) ⊭ axiomMaks n := by
  apply Frame.iff_validate_axiomMaks.not.mpr;
  push Not;
  use .inl (), .inr (0, 0), .inr (1, 0);
  and_intros;
  · tauto;
  · tauto;
  · use fun _ _ => False;
    and_intros;
    · exact forces_farthest;
    · exact forces_farthest;
    · simp;

private lemma validates_axiomMaks_of_ne (hmn : m ≠ n) : (frameMaks n) ⊧ axiomMaks m := by
  apply Frame.iff_validate_axiomMaks.mpr;
  rintro (⟨⟩ | ⟨i, k⟩) y z Rxy Rxz V hy hz;
  · match y, z, Rxy, Rxz with
    | .inr (i, l), .inr (j, l'), Rxy, Rxz =>
      have hl : l = 0 := Rxy;
      have hl' : l' = 0 := Rxz;
      subst hl hl';
      exact absurd hy <| not_forces_farthest_of_ne (by omega) forces_farthest;
  · match y, z, Rxy, Rxz with
    | .inr (i', l), .inr (j', l'), Rxy, Rxz =>
      grind;

private lemma validates_logicMaks (hn : n ∉ 𝔹) : (frameMaks n) ⊧ logicMaks 𝔹 := by
  apply Frame.validates_add Frame.validates_logicK;
  rintro φ ⟨m, hm, rfl⟩;
  exact validates_axiomMaks_of_ne <| by rintro rfl; exact hn hm;

end frameMaks


lemma of_logicMaks_le (h : logicMaks 𝔸 ≤ logicMaks 𝔹) : 𝔸 ⊆ 𝔹 := by
  contrapose! h;
  obtain ⟨n, hn𝔸, hn𝔹⟩ := Set.not_subset.mp h;
  apply NormalLogic.le_iff.not.mpr;
  push Not;
  use axiomMaks n;
  and_intros;
  · exact NormalLogic.mem_add (by grind);
  · intro hmem;
    exact frameMaks.not_validates_axiomMaks <| frameMaks.validates_logicMaks hn𝔹 _ hmem;

theorem injective_logicMaks : Function.Injective logicMaks := by
  intro 𝔸 𝔹 h;
  exact Set.Subset.antisymm (of_logicMaks_le (by grind)) (of_logicMaks_le (by grind));


open Cardinal in
/--
There are exactly continuum many consistent normal logics over `ℕ`.
- [CZ98, §10.5]
-/
theorem mk_consistent_normalLogic_eq_continuum
  : Cardinal.mk { L : NormalLogic ℕ // L.Consistent } = 𝔠 := by
  apply le_antisymm
  · calc
      _ ≤ Cardinal.mk (Set (Formula ℕ)) :=
          mk_le_of_injective
            (f := fun L : { L : NormalLogic ℕ // L.Consistent } => (L.1 : Set (Formula ℕ)))
            fun _ _ h => Subtype.ext <| SetLike.coe_injective h
      _ = 2 ^ Cardinal.mk (Formula ℕ) := mk_set
      _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero mk_le_aleph0
      _ = _ := two_power_aleph0
  · calc
      𝔠 = Cardinal.mk (Set ℕ) := by simp
      _ ≤ _ := mk_le_of_injective (f := fun 𝔸 => ⟨logicMaks 𝔸, consistent_logicMaks⟩)
          fun 𝔸 𝔹 h => injective_logicMaks <| by simpa using h

end Maks

end Modal

end
