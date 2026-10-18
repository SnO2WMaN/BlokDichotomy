module

public import BlokDichotomy.Kripke.Completeness

/-!
# Makinson's theorem

A consistent normal logic is validated by `deadEnd` or by `reflPoint`.

## References

- [CZ98, Theorem 8.67]
-/

@[expose] public section

universe u v

namespace NormalLogic

open Formula Model.World

variable {α : Type v} {a : α} {L : NormalLogic α} [L.IsNExt 𝐊]
         {κ : Type u} {M : Model κ α} {x : M.World} {U : Fin 1 → α → Prop}

noncomputable def pointSubst (U : Fin 1 → α → Prop) : Substitution α α := by
  classical
  exact fun a => if U 0 a then ⊤ else ⊥

lemma forces_pointSubst (w : Fin 1) : x ⊩ pointSubst U a ↔ U w a := by
  rw [Subsingleton.elim w 0];
  unfold pointSubst;
  split_ifs with h <;> simp [h];

/-- If `◇⊤ ∉ L`, then the irreflexive point validates `L`.
- [CZ98, Theorem 8.67]
-/
theorem deadEnd_validates_of_not_mem (h : ◇⊤ ∉ L) : deadEnd ⊧ L := by
  obtain ⟨x, hx⟩ := exists_world_not_forces h;
  intro φ hA U w;
  have h₁ := canonicalModel_validates_of_mem (L.subst (s := pointSubst U) hA) x;
  rw [forces_subst] at h₁;
  apply (forces_iff_of_no_succ _ _ _ _).mp h₁;
  · exact fun x' Rxx' => hx <| forces_dia.mpr ⟨x', Rxx', forces_top⟩;
  · exact fun _ => id;
  · exact fun a => forces_pointSubst w;

/-- If `L` is consistent and `◇⊤ ∈ L`, then the reflexive point validates `L`.
- [CZ98, Theorem 8.67]
-/
theorem reflPoint_validates_of_mem (hc : L.Consistent) (h : ◇⊤ ∈ L) : reflPoint ⊧ L := by
  obtain ⟨x⟩ := hc.nonempty_maximalConsistentSet;
  intro φ hA U w;
  have h₁ := canonicalModel_validates_of_mem (L.subst (s := pointSubst U) hA) x;
  rw [forces_subst] at h₁;
  apply (forces_iff_of_serial _ _ _ x w _).mp h₁;
  · intro y;
    obtain ⟨y', Ryy', -⟩ := forces_dia.mp <| canonicalModel_validates_of_mem h y;
    exact ⟨y', Ryy'⟩;
  · exact fun _ => ⟨0, trivial⟩;
  · exact fun _ w' a => forces_pointSubst w';

/-- A consistent `L` is validated by `deadEnd` or by `reflPoint`.
- [CZ98, Theorem 8.67]
-/
theorem makinson (hc : L.Consistent) : deadEnd ⊧ L ∨ reflPoint ⊧ L := by
  by_cases h : ◇⊤ ∈ L;
  · exact Or.inr <| reflPoint_validates_of_mem hc h;
  · exact Or.inl <| deadEnd_validates_of_not_mem h;

/-- A consistent `L` is validated by some frame on `Fin 1`.
- [CZ98, Theorem 8.67]
-/
theorem Consistent.exists_frame_validates (hc : L.Consistent) : ∃ F : Frame (Fin 1), F ⊧ L :=
  (makinson hc).elim (fun h => ⟨_, h⟩) fun h => ⟨_, h⟩

omit [L.IsNExt 𝐊] in
lemma not_mem_of_deadEnd_validates (h : deadEnd ⊧ L) : ◇⊤ ∉ L := by
  by_contra! hmem;
  obtain ⟨_, R0y, -⟩ := forces_dia.mp <| h _ hmem (fun _ _ => True) 0;
  exact R0y;

lemma deadEnd_validates_iff : deadEnd ⊧ L ↔ ◇⊤ ∉ L :=
  ⟨not_mem_of_deadEnd_validates, deadEnd_validates_of_not_mem⟩

end NormalLogic

end
