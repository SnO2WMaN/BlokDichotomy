module

public import BlokDichotomy.Modal.Logic.Basic

/-!
# Splittings of the lattice of normal extensions

Splitting pairs `IsSplittingPair L₀ L₁ L₂` of the lattice of normal extensions of `L₀`, logics
`L₁` that split it, and the uniqueness of each component of a splitting pair given the other.

## References

- [CZ98, §10.5]
-/

@[expose] public section

namespace Modal

namespace NormalLogic

variable {α : Type*} {L L₀ L₁ L₂ L₃ : NormalLogic α}

/-- `(L₁, L₂)` is a splitting pair of the normal extensions of `L₀`: `L₂ ≰ L₁`, and every normal
extension `L` of `L₀` has `L ≤ L₁` or `L₂ ≤ L`. Then `L₂` is the splitting of the normal
extensions of `L₀` by `L₁`.
- [CZ98, §10.5]
-/
structure IsSplittingPair (L₀ L₁ L₂ : NormalLogic α) : Prop where
  isNExt_left : L₁.IsNExt L₀
  isNExt_right : L₂.IsNExt L₀
  not_le : ¬L₂ ≤ L₁
  le_or_le : ∀ (L : NormalLogic α) [L.IsNExt L₀], L ≤ L₁ ∨ L₂ ≤ L

/-- `L₁` splits the normal extensions of `L₀`: `IsSplittingPair L₀ L₁ L₂` for some `L₂`.
- [CZ98, §10.5]
-/
def Splits (L₀ L₁ : NormalLogic α) : Prop := ∃ L₂, IsSplittingPair L₀ L₁ L₂

namespace IsSplittingPair

lemma not_le_of_le (h : IsSplittingPair L₀ L₁ L₂) (hL : L ≤ L₁) : ¬L₂ ≤ L := by
  by_contra hL₂;
  exact h.not_le <| hL₂.trans hL;

/-- Every normal extension `L` of `L₀` has exactly one of `L ≤ L₁` and `L₂ ≤ L`.
- [CZ98, §10.5]
-/
lemma le_iff_not_le (h : IsSplittingPair L₀ L₁ L₂) [L.IsNExt L₀] : L₂ ≤ L ↔ ¬L ≤ L₁ := by
  constructor;
  · intro hL₂;
    by_contra hL;
    exact h.not_le_of_le hL hL₂;
  · exact (h.le_or_le L).resolve_left;

/-- `L₂` is determined by `L₁`.
- [CZ98, §10.5]
-/
lemma right_unique (h : IsSplittingPair L₀ L₁ L₂) (h' : IsSplittingPair L₀ L₁ L₃) : L₂ = L₃ :=
  have := h.isNExt_right;
  have := h'.isNExt_right;
  le_antisymm (h.le_iff_not_le.mpr h'.not_le) (h'.le_iff_not_le.mpr h.not_le)

/-- `L₁` is determined by `L₂`.
- [CZ98, §10.5]
-/
lemma left_unique (h : IsSplittingPair L₀ L₁ L₂) (h' : IsSplittingPair L₀ L₃ L₂) : L₁ = L₃ :=
  have := h.isNExt_left;
  have := h'.isNExt_left;
  le_antisymm ((h'.le_or_le L₁).resolve_right h.not_le) ((h.le_or_le L₃).resolve_right h'.not_le)

end IsSplittingPair

end NormalLogic

end Modal

end
