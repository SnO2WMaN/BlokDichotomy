module

public import BlokDichotomy.Modal.Logic.Fine
public import BlokDichotomy.Modal.Logic.Fine.Degree

/-!
# Fine's formulas with the pins

The formula `ε'` is `ε` with the conjunct `pin`, which fixes the atoms `q₀, q₁, r₀, r₁` at the base
of the criss-cross. Its shifted implications `θPin m` force a strictly ascending chain of points
forcing `εPin m`, as `θ` does for `ε`.

## References

- [Fin74a]
-/

@[expose] public section

namespace Modal

namespace Fine

open Formula Model.World

/-- The pins fixing the base of Fine's criss-cross.

- [Fin74a] -/
def pin : Formula ℕ :=
  □(#2 🡒 □#2) ⋏ □(#4 🡒 □#4) ⋏ □(∼(#2 ⋏ #4)) ⋏ □(∼(#2 ⋏ #3)) ⋏ □(∼(#4 ⋏ #5)) ⋏ □(∼(#2 ⋏ #5)) ⋏
    □(∼(#4 ⋏ #3))

/-- `ε⟦σ_m⟧` with `ι 0` and `pin` left unshifted.

- [Fin74a] -/
def εPin (m : ℕ) : Formula ℕ := δ ⋏ ◇(α m) ⋏ ι 0 ⋏ pin

/-- Fine's `ε` with the pins.

- [Fin74a] -/
def ε' : Formula ℕ := εPin 0

/-- The analogue of `θ` for `εPin`.

- [Fin74a] -/
def θPin (m : ℕ) : Formula ℕ := εPin m 🡒 ψ⟦shift m⟧

variable {κ : Type*} {M : Model κ ℕ} {x v : M.World} {m n : ℕ} {F : Frame κ}

lemma forces_pin_iff : x ⊩ pin ↔ x ⊩ □(#2 🡒 □#2) ∧ x ⊩ □(#4 🡒 □#4) ∧ x ⊩ □(∼(#2 ⋏ #4)) ∧
    x ⊩ □(∼(#2 ⋏ #3)) ∧ x ⊩ □(∼(#4 ⋏ #5)) ∧ x ⊩ □(∼(#2 ⋏ #5)) ∧ x ⊩ □(∼(#4 ⋏ #3)) := by
  simp only [pin, forces_and]

lemma forces_εPin_iff : x ⊩ εPin m ↔ x ⊩ δ ∧ x ⊩ ◇(α m) ∧ x ⊩ ι 0 ∧ x ⊩ pin := by
  simp only [εPin, forces_and]

lemma forces_ε'_iff : x ⊩ ε' ↔ x ⊩ ε ∧ x ⊩ pin := by
  simp only [ε', εPin, ε, forces_and, and_assoc]

section

variable [IsTrans _ M.Rel]

lemma forces_pin_of_rel (hx : x ⊩ pin) (Rxv : x ≺ v) : v ⊩ pin := by
  simp only [pin, forces_and] at hx ⊢;
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hx;
  exact ⟨forces_box_of_rel h₁ Rxv, forces_box_of_rel h₂ Rxv, forces_box_of_rel h₃ Rxv,
    forces_box_of_rel h₄ Rxv, forces_box_of_rel h₅ Rxv, forces_box_of_rel h₆ Rxv,
    forces_box_of_rel h₇ Rxv⟩

lemma forces_ι₀_of_rel (hx : x ⊩ ι 0) (Rxv : x ≺ v) : v ⊩ ι 0 := by
  simp only [ι, ι₁, ι₂, ι₃, ι₄, forces_and] at hx ⊢;
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hx;
  exact ⟨forces_box_of_rel h₁ Rxv, forces_box_of_rel h₂ Rxv, forces_box_of_rel h₃ Rxv,
    forces_box_of_rel h₄ Rxv⟩

/-- If `θPin m` holds everywhere and `x` forces `εPin m`, a strict successor of `x` forces
`εPin (m + 1)`.

- [Fin74a, (3)] -/
lemma chain_step_pin (hθ : ∀ y : M.World, y ⊩[M] θPin m) (hx : x ⊩ εPin m) :
    ∃ v : M.World, x ≺ v ∧ v ⊀ x ∧ v ⊩ εPin (m + 1) := by
  obtain ⟨v, Rxv, hv₁, hv₂, hv₃⟩ := forces_ψ_subst_shift.mp <| hθ x hx;
  obtain ⟨hD, hA, hK, hP⟩ := forces_εPin_iff.mp hx;
  have hstrict : v ⊀ x := by
    by_contra Rvx;
    exact hv₂ <| forces_dia_of_rel hA Rvx;
  exact ⟨v, Rxv, hstrict, forces_εPin_iff.mpr
    ⟨forces_δ_of_rel hD Rxv hv₁, hv₃, forces_ι₀_of_rel hK Rxv, forces_pin_of_rel hP Rxv⟩⟩

end

/-- In a transitive reflexive frame validating all `θPin m`, a point forcing `ε'` starts a strict
chain.

- [Fin74a, Lemma 1] -/
lemma exists_chain_of_validates_θPin [IsTrans _ F.Rel] [Std.Refl F.Rel] (hθ : ∀ m, F ⊧ θPin m)
    {V : F.World → ℕ → Prop} {x : F.World} (hx : x ⊩[⟨F, V⟩] ε') :
    ∃ u : ℕ → F.World, (∀ m, u m ≺ u (m + 1)) ∧ Function.Injective u := by
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => y ≺ v ∧ v ⊀ y)
    (P := fun m y => y ⊩[⟨F, V⟩] εPin m) hx fun m y hy => by
      obtain ⟨v, Ryv, Rvy, hv⟩ := chain_step_pin (fun y => hθ m V y) hy;
      exact ⟨v, ⟨Ryv, Rvy⟩, hv⟩;
  have hR : ∀ m, u m ≺ u (m + 1) := fun m => (hu m).2.1;
  exact ⟨u, hR, injective_of_forall_rel_succ hR fun m => (hu m).2.2⟩

/-- Every frame validating `𝐒𝟒`, all `θPin m` and `χ` validates `∼ε'`.

- [Fin74a, Lemma 1] -/
theorem validates_neg_ε'_of_validates_θPin (hS4 : F ⊧ (𝐒𝟒 : NormalLogic ℕ))
    (hθ : ∀ m, F ⊧ θPin m) (hχ : F ⊧ χ) : F ⊧ ∼ε' := by
  obtain ⟨_, _⟩ := Frame.validates_logicS4_iff.mp hS4;
  intro V x hx;
  obtain ⟨u, hR, hinj⟩ := exists_chain_of_validates_θPin hθ hx;
  exact chainVal_forces_neg_χ hR hinj <| hχ (chainVal u) (u 0)

/-- Every frame validating `𝐒𝟒`, all `θPin m` and `H n` for some `n ≥ 1` validates `∼ε'`.

- [Fin74a, Lemma 1] -/
theorem validates_neg_ε'_of_validates_θPin_H (hn : 1 ≤ n) (hS4 : F ⊧ (𝐒𝟒 : NormalLogic ℕ))
    (hθ : ∀ m, F ⊧ θPin m) (hH : F ⊧ H n) : F ⊧ ∼ε' := by
  obtain ⟨_, _⟩ := Frame.validates_logicS4_iff.mp hS4;
  intro V x hx;
  obtain ⟨u, hR, hinj⟩ := exists_chain_of_validates_θPin hθ hx;
  exact cycVal_forces_neg_H hn hR hinj <| hH (cycVal n u) (u 0)

/-- A normal extension of `𝐒𝟒` containing all `θPin m` and `χ` validates `∼ε'` on each of its
frames.

- [Fin74a, Lemma 1] -/
theorem validates_neg_ε'_of_validates {L : NormalLogic ℕ} (hS4 : 𝐒𝟒 ≤ L)
    (hθ : ∀ m, θPin m ∈ L) (hχ : χ ∈ L) (hL : F ⊧ L) : F ⊧ ∼ε' :=
  validates_neg_ε'_of_validates_θPin (fun A h => hL A <| hS4 h) (fun m => hL _ (hθ m)) (hL _ hχ)

/-- A normal extension of `𝐒𝟒` containing all `θPin m` and some `H n` with `n ≥ 1` validates
`∼ε'` on each of its frames.

- [Fin74a, Lemma 1] -/
theorem validates_neg_ε'_of_validates_H {L : NormalLogic ℕ} (hn : 1 ≤ n) (hS4 : 𝐒𝟒 ≤ L)
    (hθ : ∀ m, θPin m ∈ L) (hH : H n ∈ L) (hL : F ⊧ L) : F ⊧ ∼ε' :=
  validates_neg_ε'_of_validates_θPin_H hn (fun A h => hL A <| hS4 h) (fun m => hL _ (hθ m))
    (hL _ hH)

end Fine

end Modal

end
