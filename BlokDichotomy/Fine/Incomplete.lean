module

public import BlokDichotomy.Fine.ValidatesG
public import BlokDichotomy.Kripke.Correspondence
public import BlokDichotomy.Kripke.Degree

/-!
# Fine's logic is Kripke-incomplete

Every frame validating Fine's logic validates `∼ε`, yet `∼ε` is not a theorem of Fine's logic:
every formula of the logic is strongly valid in Fine's model, which forces `ε` at `d_0`. So there
is a Kripke-incomplete normal extension of `𝐒𝟒`, and hence of `𝐊𝟒`. The model-independent
steps live in the namespace `Fine`; the results about `logicS4Fine` are in the root namespace.

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

/-- `δ` persists to any successor that still forces `p₀ ⋎ p₁`. -/
lemma forces_δ_of_rel (hD : x ⊩ δ) (Rxy : x ≺ y) (hp : y ⊩ #0 ⋎ #1) : y ⊩ δ := by
  obtain ⟨-, h₁, h₂, h₃⟩ := forces_δ_iff.mp hD;
  rw [forces_δ_iff];
  and_intros;
  · exact hp;
  · exact forces_box_of_rel h₁ Rxy;
  · exact forces_box_of_rel h₂ Rxy;
  · exact forces_box_of_rel h₃ Rxy

/-- If `θ` is strongly valid in `M` and `x` forces `ε⟦σ_m⟧`, then some strict successor of `x`
forces `ε⟦σ_{m+1}⟧`.

- [Fin74a, (3)] -/
lemma chain_step (hG : θ ∈ M.logic) (hx : x ⊩ ε⟦shift m⟧) :
    ∃ y : M.World, x ≺ y ∧ y ⊀ x ∧ y ⊩ ε⟦shift (m + 1)⟧ := by
  obtain ⟨y, Rxy, hy01, hyA, hyA'⟩ := forces_ψ_subst_shift.mp <| hG (shift m) x hx;
  obtain ⟨hD, hAm, hK⟩ := forces_ε_subst_shift.mp hx;
  have hstrict : y ⊀ x := by
    by_contra Ryx;
    exact hyA <| forces_dia_of_rel hAm Ryx;
  exact ⟨y, Rxy, hstrict,
    forces_ε_subst_shift.mpr ⟨forces_δ_of_rel hD Rxy hy01, hyA', forces_ι_succ hK Rxy⟩⟩

end Chain

section Psi

variable {κ : Type*} {F : Frame κ} {u : ℕ → F.World}

/-- The valuation along a chain `u`: `#6` holds exactly at the points of index `3i`, `#7` exactly at
those of index `3i+1`; all other atoms are false.

- [Fin74a] -/
def chainVal (u : ℕ → F.World) : F.World → ℕ → Prop
| v, 6 => ∃ i, v = u (3 * i)
| v, 7 => ∃ i, v = u (3 * i + 1)
| _, _ => False

lemma forces_chainVal_6_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[⟨F, chainVal u⟩] #6 ↔ ∃ i, n = 3 * i := by
  constructor;
  · rintro ⟨i, hi⟩;
    exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩;
    use i;

lemma forces_chainVal_7_iff (hinj : Function.Injective u) (n : ℕ) :
    u n ⊩[⟨F, chainVal u⟩] #7 ↔ ∃ i, n = 3 * i + 1 := by
  constructor;
  · rintro ⟨i, hi⟩;
    exact ⟨i, hinj hi⟩;
  · rintro ⟨i, rfl⟩;
    use i;

/-- Along an injective ascending chain in a transitive frame, `chainVal` refutes `χ` at the
chain's origin. -/
lemma chainVal_forces_neg_χ [IsTrans κ F.Rel'] (hR : ∀ m, u m ≺ u (m + 1))
    (hinj : Function.Injective u) : u 0 ⊩[⟨F, chainVal u⟩] ∼χ := by
  have hlt : ∀ {i j}, i < j → u i ≺ u j := fun h => Nat.rel_of_forall_rel_succ_of_lt F.Rel' hR h;
  unfold χ;
  rw [forces_neg, not_forces_neg, forces_and];
  and_intros;
  · exact (forces_chainVal_6_iff hinj 0).mpr ⟨0, rfl⟩;
  · rw [forces_box];
    rintro y - ⟨i, rfl⟩;
    use u (3 * i + 1);
    constructor;
    · exact hlt <| by omega;
    · simp only [forces_and];
      and_intros;
      · apply forces_chainVal_6_iff hinj _ |>.not.mpr;
        omega;
      · exact (forces_chainVal_7_iff hinj (3 * i + 1)).mpr ⟨i, rfl⟩;
      · use u (3 * i + 2);
        constructor;
        · exact hlt <| by omega;
        · simp only [forces_and];
          and_intros;
          · apply forces_chainVal_6_iff hinj _ |>.not.mpr;
            omega;
          · apply forces_chainVal_7_iff hinj _ |>.not.mpr;
            omega;
          · use u (3 * (i + 1));
            constructor;
            · exact hlt <| by omega;
            · exact (forces_chainVal_6_iff hinj (3 * (i + 1))).mpr ⟨i + 1, rfl⟩;

end Psi

end Fine

open Fine

variable {κ : Type*} {F : Frame κ}

/-- Every frame validating Fine's logic validates `∼ε`.

- [Fin74a, Lemma 1]
- [Lit04, p. 332] -/
theorem validates_neg_ε_of_validates_logicS4Fine (hL : F ⊧ logicS4Fine) : F ⊧ ∼ε := by
  obtain ⟨_, _⟩ :=
    Frame.validates_logicS4_iff.mp fun A h => hL A <| NormalLogic.mem_add_of_mem h;
  intro V x hxE;
  have hG : θ ∈ (Model.mk F V).logic :=
    Frame.logic_le_model_logic <| hL θ <| NormalLogic.mem_add <| by simp;
  obtain ⟨u, -, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => y ≺ v ∧ v ⊀ y)
    (P := fun m y => y ⊩[⟨F, V⟩] ε⟦shift m⟧)
    (forces_ε_subst_shift.mpr <| forces_ε_iff.mp hxE) fun m y hy => by
      obtain ⟨v, Ryv, Rvy, hv⟩ := chain_step hG hy;
      exact ⟨v, ⟨Ryv, Rvy⟩, hv⟩;
  have hR : ∀ m, u m ≺ u (m + 1) := fun m => (hu m).2.1;
  have hinj := injective_of_forall_rel_succ (r := F.Rel') hR fun m => (hu m).2.2;
  exact chainVal_forces_neg_χ hR hinj <| hL χ (NormalLogic.mem_add <| by simp) (chainVal u) (u 0)

/-- Every theorem of Fine's logic is strongly valid in Fine's model.

- [Fin74a, Lemma 2] -/
lemma logicS4Fine_le_model_logic : logicS4Fine ≤ FineFrame.model.logic :=
  NormalLogic.add_le (fun _ h => Frame.logic_le_model_logic <| Frame.validates_logicS4 _ h) <| by
    rintro _ (rfl | rfl);
    · exact Frame.logic_le_model_logic FineFrame.validates_θ;
    · exact FineFrame.χ_mem_model_logic

/-- `∼ε` is not a theorem of Fine's logic.

- [Fin74a, Lemma 2] -/
lemma neg_ε_not_mem_logicS4Fine : ∼ε ∉ logicS4Fine := by
  by_contra h;
  exact Model.validates_of_mem_logic (logicS4Fine_le_model_logic h) (FineFrame.World.d 0)
    FineFrame.forces_ε_d0

/-- `∼ε` lies in the logic of the frames validating Fine's logic.

- [Fin74a, Lemma 1] -/
lemma neg_ε_mem_frameLogic_logicS4Fine : ∼ε ∈ logicS4Fine.frameLogic.{u} fun _ _ => True :=
  fun _ _ _ hL => validates_neg_ε_of_validates_logicS4Fine hL

/-- Fine's logic, a normal extension of `𝐒𝟒` and so of `𝐊𝟒`, is Kripke-incomplete: `∼ε` is
valid in every frame validating the logic, yet `∼ε` is not a theorem of it.

- [Fin74a]
- [Lit04, p. 332] -/
theorem not_kripkeComplete_logicS4Fine : ¬logicS4Fine.KripkeComplete.{u} fun _ _ => True := by
  by_contra h;
  exact neg_ε_not_mem_logicS4Fine <| h neg_ε_mem_frameLogic_logicS4Fine

end
