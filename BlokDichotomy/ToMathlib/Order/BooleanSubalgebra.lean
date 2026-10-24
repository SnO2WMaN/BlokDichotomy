module

public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite intersections and unions in Boolean subalgebras of sets
-/

@[expose] public section

namespace BooleanSubalgebra

variable {β γ : Type*} (L : BooleanSubalgebra (Set β)) (s : Finset γ) {P : γ → Set β}

/-- A Boolean subalgebra of sets contains the intersection of finitely many of its members. -/
lemma setOf_forall_mem (h : ∀ i ∈ s, P i ∈ L) : {x | ∀ i ∈ s, x ∈ P i} ∈ L := by
  have h₁ := Finset.inf_mem (L : Set (Set β)) L.top_mem (fun _ hx _ hy => L.inf_mem hx hy) s P h;
  have h₂ : s.inf P = {x | ∀ i ∈ s, x ∈ P i} := by
    ext x;
    simp [Finset.inf_set_eq_iInter];
  rw [h₂] at h₁;
  exact h₁

/-- A Boolean subalgebra of sets contains the union of finitely many of its members. -/
lemma setOf_exists_mem (h : ∀ i ∈ s, P i ∈ L) : {x | ∃ i ∈ s, x ∈ P i} ∈ L := by
  have h₁ := Finset.sup_mem (L : Set (Set β)) L.bot_mem (fun _ hx _ hy => L.sup_mem hx hy) s P h;
  have h₂ : s.sup P = {x | ∃ i ∈ s, x ∈ P i} := by
    ext x;
    simp [Finset.sup_set_eq_biUnion];
  rw [h₂] at h₁;
  exact h₁

end BooleanSubalgebra

end
