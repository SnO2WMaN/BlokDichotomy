module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Fin

/-!
# Injections of finite sets into infinite types
-/

@[expose] public section

namespace Infinite

variable {α β : Type*} [Infinite α]

/-- A finite set of elements of any type injects into an infinite type. -/
lemma exists_injOn (t : Finset β) : ∃ f : β → α, Set.InjOn f t := by
  classical
  use fun b => if h : b ∈ t then Infinite.natEmbedding α (t.equivFin ⟨b, h⟩) else
    Infinite.natEmbedding α 0;
  intro a ha b hb hab;
  simp only [Finset.mem_coe] at ha hb;
  simp only [ha, hb, dite_true] at hab;
  have h₁ := t.equivFin.injective (Fin.val_injective ((Infinite.natEmbedding α).injective hab));
  exact congrArg Subtype.val h₁

end Infinite

end
