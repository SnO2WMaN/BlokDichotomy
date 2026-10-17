module

public import BlokDichotomy.Kripke.Cycle
public import BlokDichotomy.Formula

/-!
# Finest filtrations through a map

The finest filtration `M.filtration c` of a model `M` through a map `c`, and the filtration lemma.

## References

- [CZ98, §5.3]
-/

@[expose] public section

universe u u' v

variable {κ : Type u} {ι : Type u'} {α : Type v}

namespace Model

/-- The finest filtration of `M` through `c`.
- [CZ98, §5.3]
-/
def filtration (M : Model κ α) (c : κ → ι) : Model ι α where
  Rel' a b := ∃ x y : M.World, c x = a ∧ c y = b ∧ x ≺ y
  Val' a p := ∃ x, c x = a ∧ M.Val' x p

variable {M : Model κ α} {c : κ → ι}

lemma filtration_rel {x y : M.World} (Rxy : x ≺ y) : (M.filtration c).Rel (c x) (c y) :=
  ⟨x, y, rfl, rfl, Rxy⟩

lemma filtration_relItr {x y : M.World} {n : ℕ} (Rxy : x ≺^[n] y) :
    Frame.RelItr (F := (M.filtration c).toFrame) n (c x) (c y) :=
  Frame.relItr_map c filtration_rel Rxy

end Model


namespace Model.World

variable [DecidableEq α] {M : Model κ α} {c : κ → ι} {φ : Formula α}

/-- If `c` identifies only points that agree on the subformulas of `φ`, then
`x ⊩ φ ↔ c x ⊩[M.filtration c] φ`.
- [CZ98, Theorem 5.23]
-/
theorem forces_filtration
    (hc : ∀ x y : M.World, c x = c y → ∀ ψ ∈ φ.subformulas, x ⊩ ψ ↔ y ⊩ ψ) {x : M.World} :
    x ⊩ φ ↔ c x ⊩[M.filtration c] φ := by
  induction φ generalizing x with
  | falsum => exact Iff.rfl;
  | atom a =>
    constructor;
    · exact fun h => ⟨x, rfl, h⟩;
    · rintro ⟨x', hx', h⟩;
      exact (hc x' x hx' (#a) Formula.mem_subformulas_self).mp h;
  | imp φ ψ ihφ ihψ =>
    rw [forces_imp, forces_imp, NotForces, NotForces,
      ihφ fun x y h χ hC => hc x y h χ <| Formula.mem_subformulas_imp_left hC,
      ihψ fun x y h χ hC => hc x y h χ <| Formula.mem_subformulas_imp_right hC];
  | dia φ ih =>
    have ih' := fun {x : M.World} => ih (x := x) fun x y h χ hC =>
      hc x y h χ <| Formula.mem_subformulas_dia hC;
    rw [forces_dia, forces_dia];
    constructor;
    · rintro ⟨y, Rxy, hy⟩;
      exact ⟨c y, Model.filtration_rel Rxy, ih'.mp hy⟩;
    · rintro ⟨_, ⟨x', y', hx', rfl, Rx'y'⟩, hy⟩;
      exact (hc x' x hx' (◇φ) Formula.mem_subformulas_self).mp ⟨y', Rx'y', ih'.mpr hy⟩;

end Model.World

end
