module

public import BlokDichotomy.Kripke.Completeness
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Powerset

/-!
# Points of finite type in the canonical model

Finiteness of the points of the canonical model from which no path of length `k` starts, and
their characteristic formulas.

## References

- [CZ98, Lemma 10.55]
-/

@[expose] public section

universe v

namespace NormalLogic

open Formula Model.World

variable {α : Type v} {L : NormalLogic α} [L.IsNExt 𝐊]

namespace canonicalModel

variable [Finite α]

/-- There are finitely many points of the canonical model satisfying `∼◇^[k]⊤`.
- [CZ98, Lemma 10.55]
-/
theorem finite_neg_multidia_top (k : ℕ) :
    { x : (canonicalModel L).World | x ⊩ ∼◇^[k]⊤ }.Finite := by
  induction k with
  | zero =>
    apply Set.finite_empty.subset;
    grind;
  | succ k ih =>
    set S := { x : (canonicalModel L).World | x ⊩ ∼◇^[k]⊤ };
    let f : (canonicalModel L).World → Set α × Set (canonicalModel L).World :=
      fun x => ({ a | #a ∈ x }, { y | x ≺ y });
    apply Set.Finite.of_finite_image (f := f);
    · apply (Set.finite_univ.prod ih.powerset).subset;
      rintro _ ⟨x, hx, rfl⟩;
      exact ⟨Set.mem_univ _, fun y Rxy => forces_neg_multidia_top_of_rel hx Rxy⟩;
    · intro x _ y _ hxy;
      simp only [f, Prod.mk.injEq, Set.ext_iff, Set.mem_ofPred_eq] at hxy;
      apply SetLike.ext;
      intro φ;
      rw [← truthlemma, ← truthlemma];
      exact forces_iff_of_same_succ hxy.1 hxy.2;

/-- There are finitely many points of the canonical model satisfying `farthest k`.
- [CZ98, Lemma 10.55]
-/
theorem finite_farthest (k : ℕ) : { x : (canonicalModel L).World | x ⊩ farthest k }.Finite :=
  (finite_neg_multidia_top (k + 1)).subset <| by
    intro _ hx;
    grind;

/-- A point of the canonical model satisfying `∼◇^[k]⊤` is the unique point satisfying some
formula.
- [CZ98, Lemma 10.55]
-/
theorem exists_characteristic {k : ℕ} {x : (canonicalModel L).World} (hx : x ⊩ ∼◇^[k]⊤) :
    ∃ θ : Formula α, ∀ y : (canonicalModel L).World, y ⊩ θ ↔ y = x := by
  classical
  have hd : ∀ y : (canonicalModel L).World, y ≠ x → ∃ φ ∈ x, φ ∉ y := fun y hy =>
    MaximalConsistentSet.exists_mem_not_mem_of_ne hy.symm;
  let d : (canonicalModel L).World → Formula α := fun y =>
    if h : y = x then ⊤ else (hd y h).choose;
  let l := (finite_neg_multidia_top (L := L) k).toFinset.toList;
  use ∼◇^[k]⊤ ⋏ ⋀(l.map d);
  intro y;
  rw [forces_and, forces_conj];
  constructor;
  · rintro ⟨hy, hl⟩;
    by_contra hyx;
    have h₁ : y ⊩ d y := hl _ <| List.mem_map_of_mem <| by simpa [l] using hy;
    simp only [d, hyx, dite_false] at h₁;
    exact (hd y hyx).choose_spec.2 <| truthlemma.mp h₁;
  · rintro rfl;
    constructor;
    · exact hx;
    · simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
      intro z _;
      by_cases hz : z = y;
      · simp [d, hz];
      · simp only [d, hz, dite_false];
        exact truthlemma.mpr (hd z hz).choose_spec.1;

/-- A point of the canonical model satisfying `farthest k` is the unique point satisfying some
formula.
- [CZ98, Lemma 10.55]
-/
theorem exists_characteristic_of_farthest {k : ℕ} {x : (canonicalModel L).World}
    (hx : x ⊩ farthest k) : ∃ θ : Formula α, ∀ y : (canonicalModel L).World, y ⊩ θ ↔ y = x :=
  exists_characteristic (forces_and.mp hx).2

end canonicalModel

end NormalLogic

end
