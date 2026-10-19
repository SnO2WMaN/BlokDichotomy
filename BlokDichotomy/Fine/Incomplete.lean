module

public import BlokDichotomy.Fine.ValidatesG
public import BlokDichotomy.Kripke.Correspondence
public import BlokDichotomy.Kripke.Degree

/-!
# Fine's logic is Kripke-incomplete

Every frame validating Fine's logic validates `∼E`, yet `∼E` is not a theorem of Fine's logic:
Fine's model strongly verifies the logic and forces `E` at `d_0`. So there is a Kripke-incomplete
normal extension of `𝐒𝟒`, and hence of `𝐊𝟒`.

## References

- [Fin74a]
- [Lit04, p. 332]
-/

@[expose] public section

universe u

namespace Fine

open Model.World

section Chain

variable {κ : Type*} {M : Model κ ℕ} [IsTrans κ M.Rel'] {x y : M.World} {m : ℕ}

/-- `D` persists to any successor that still forces `p₀ ⋎ p₁`. -/
lemma forces_D_of_rel (hD : x ⊩ D) (Rxy : x ≺ y) (hp : y ⊩ p0 ⋎ p1) : y ⊩ D := by
  simp only [D, forces_and] at hD ⊢;
  obtain ⟨-, h₁, h₂, h₃⟩ := hD;
  exact ⟨hp, forces_box_of_rel h₁ Rxy, forces_box_of_rel h₂ Rxy, forces_box_of_rel h₃ Rxy⟩

/-- If `M` strongly verifies `G` and `x` forces `E⟦σ_m⟧`, then some strict successor of `x`
forces `E⟦σ_{m+1}⟧`.

- [Fin74a, (3)] -/
lemma chain_step (hG : G ∈ M.logic) (hx : x ⊩ E⟦shift m⟧) :
    ∃ y : M.World, x ≺ y ∧ y ⊀ x ∧ y ⊩ E⟦shift (m + 1)⟧ := by
  obtain ⟨y, Rxy, hy01, hyA, hyA'⟩ := forces_F_subst_shift.mp <| hG (shift m) x hx;
  obtain ⟨hD, hAm, hK⟩ := forces_E_subst_shift.mp hx;
  have hstrict : y ⊀ x := by
    by_contra Ryx;
    exact hyA <| forces_dia_of_rel hAm Ryx;
  exact ⟨y, Rxy, hstrict,
    forces_E_subst_shift.mpr ⟨forces_D_of_rel hD Rxy hy01, hyA', forces_K_succ hK Rxy⟩⟩

end Chain

section Psi

variable {κ : Type*} {F : Frame κ} {u : ℕ → F.World}

/-- The valuation along a chain `u`: `s` holds exactly at the points of index `3i`, `t` exactly at
those of index `3i+1`; all other atoms are false.

- [Fin74a] -/
def psiVal (u : ℕ → F.World) : F.World → ℕ → Prop
| v, 6 => ∃ i, v = u (3 * i)
| v, 7 => ∃ i, v = u (3 * i + 1)
| _, _ => False

lemma forces_s_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[⟨F, psiVal u⟩] s ↔ ∃ i, n = 3 * i := by
  constructor;
  · rintro ⟨i, hi⟩;
    exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩;
    use i;

lemma forces_t_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[⟨F, psiVal u⟩] t ↔ ∃ i, n = 3 * i + 1 := by
  constructor;
  · rintro ⟨i, hi⟩;
    exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩;
    use i;

/-- Along an injective ascending chain in a transitive frame, `psiVal` refutes `H` at the
chain's origin. -/
lemma psi_forces_neg_H [IsTrans κ F.Rel'] (hR : ∀ m, u m ≺ u (m + 1))
    (hinj : Function.Injective u) : u 0 ⊩[⟨F, psiVal u⟩] ∼H := by
  have hlt : ∀ {i j}, i < j → u i ≺ u j := fun h => Nat.rel_of_forall_rel_succ_of_lt F.Rel' hR h;
  unfold H;
  rw [forces_neg, not_forces_neg, forces_and];
  and_intros;
  · exact (forces_s_iff hinj 0).mpr ⟨0, rfl⟩;
  · rw [forces_box];
    rintro y - ⟨i, rfl⟩;
    use u (3 * i + 1);
    constructor;
    · exact hlt <| by omega;
    · simp only [forces_and];
      and_intros;
      · apply forces_s_iff hinj _ |>.not.mpr;
        omega;
      · exact (forces_t_iff hinj (3 * i + 1)).mpr ⟨i, rfl⟩;
      · use u (3 * i + 2);
        constructor;
        · exact hlt <| by omega;
        · simp only [forces_and];
          and_intros;
          · apply forces_s_iff hinj _ |>.not.mpr;
            omega;
          · apply forces_t_iff hinj _ |>.not.mpr;
            omega;
          · use u (3 * (i + 1));
            constructor;
            · exact hlt <| by omega;
            · exact (forces_s_iff hinj (3 * (i + 1))).mpr ⟨i + 1, rfl⟩;

end Psi

variable {κ : Type*} {F : Frame κ}

/-- Every frame validating Fine's logic validates `∼E`.

- [Fin74a, Lemma 1]
- [Lit04, p. 332] -/
theorem validates_neg_E_of_validates (hL : F ⊧ logic) : F ⊧ ∼E := by
  obtain ⟨_, _⟩ :=
    Frame.validates_logicS4_iff.mp fun φ h => hL φ <| NormalLogic.mem_add_of_mem h;
  intro V x hxE;
  have hG : G ∈ (Model.mk F V).logic :=
    Frame.logic_le_model_logic <| hL G <| NormalLogic.mem_add <| by simp;
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => y ≺ v ∧ v ⊀ y)
    (P := fun m y => y ⊩[⟨F, V⟩] E⟦shift m⟧)
    (forces_E_subst_shift.mpr <| forces_E_iff.mp hxE) fun m y hy => by
      obtain ⟨v, Ryv, Rvy, hv⟩ := chain_step hG hy;
      exact ⟨v, ⟨Ryv, Rvy⟩, hv⟩;
  have hR : ∀ m, u m ≺ u (m + 1) := fun m => (hu m).2.1;
  have hinj := injective_of_forall_rel_succ (r := F.Rel') hR fun m => (hu m).2.2;
  exact psi_forces_neg_H hR hinj <| hL H (NormalLogic.mem_add <| by simp) (psiVal u) (u 0)

/-- Fine's model strongly verifies every theorem of Fine's logic.

- [Fin74a, Lemma 2] -/
lemma logic_le_model_logic : logic ≤ model.logic :=
  NormalLogic.add_le (fun _ h => Frame.logic_le_model_logic <| Frame.validates_logicS4 _ h) <| by
    rintro _ (rfl | rfl);
    · exact Frame.logic_le_model_logic validates_G;
    · exact H_mem_model_logic

/-- `∼E` is not a theorem of Fine's logic.

- [Fin74a, Lemma 2] -/
lemma neg_E_not_mem : ∼E ∉ logic := by
  by_contra h;
  exact Model.validates_of_mem_logic (logic_le_model_logic h) (World.d 0) forces_E_d0

/-- `∼E` lies in the logic of the frames validating Fine's logic.

- [Fin74a, Lemma 1] -/
lemma neg_E_mem_frameLogic : ∼E ∈ logic.frameLogic.{u} fun _ _ => True :=
  fun _ _ _ hL => validates_neg_E_of_validates hL

/-- Fine's logic, a normal extension of `𝐒𝟒` and so of `𝐊𝟒`, is Kripke-incomplete: `∼E` is
valid in every frame validating the logic, yet `∼E` is not a theorem of it.

- [Fin74a]
- [Lit04, p. 332] -/
theorem not_kripkeComplete : ¬logic.KripkeComplete.{u} fun _ _ => True := by
  by_contra h;
  exact neg_E_not_mem <| h neg_E_mem_frameLogic

end Fine

end
