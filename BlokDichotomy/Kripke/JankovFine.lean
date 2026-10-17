module

public import BlokDichotomy.Kripke.Completeness
public import BlokDichotomy.Kripke.Cycle
public import BlokDichotomy.Formula
public import Mathlib.Data.Fintype.Basic

/-!
# Jankov–Fine formulas

The Jankov–Fine formula `F.jfFormula` of a finite frame `F : FinFrame`.

## References

- [CZ98, p. 362]
-/

@[expose] public section

abbrev FinFrame := Σ n, Frame (Fin n)

structure FinFrame.RootedCycleFree (F : FinFrame) : Prop where
  isRooted : F.2.IsRooted
  cycleFree : F.2.CycleFree

namespace Frame

lemma validates_map_finVal_iff {κ : Type*} {F : Frame κ} {m : ℕ} {φ : Formula (Fin m)} :
    F ⊧ φ.map Fin.val ↔ F ⊧ φ := by
  constructor;
  · intro h V x;
    have := h (fun w a => ∃ h : a < m, V w ⟨a, h⟩) x;
    rw [Model.World.forces_map] at this;
    convert this using 2;
    funext w a;
    simp [Model.Val];
  · intro h V x;
    rw [Model.World.forces_map];
    exact h _ x;

end Frame

namespace FinFrame

open Formula Model.World Frame

variable (F : FinFrame)

open Classical in
noncomputable def jfEdge (i j : F.2.World) : Formula (Fin F.1) :=
  if i ≺ j then #i 🡒 ◇#j else #i 🡒 ∼◇#j

open Classical in
noncomputable def jfDistinct (i j : F.2.World) : Formula (Fin F.1) :=
  if i = j then ⊤ else ∼(#i ⋏ #j)

/-- The diagram `δ(F)` of `F`.
- [CZ98, p. 362]
-/
noncomputable def jfDiagram : Formula (Fin F.1) :=
  ⋀((Finset.univ : Finset (Fin F.1 × Fin F.1)).toList.map fun p => F.jfEdge p.1 p.2) ⋏
  ⋀((Finset.univ : Finset (Fin F.1 × Fin F.1)).toList.map fun p => F.jfDistinct p.1 p.2) ⋏
  ⋁((Finset.univ : Finset (Fin F.1)).toList.map fun i => #i)

open Classical in
noncomputable def jfRoot : Formula (Fin F.1) :=
  ⋁((Finset.univ : Finset F.2.Root).toList.map fun i => #i.1)

/-- The Jankov–Fine formula `χ(F)` of `F`.
- [CZ98, p. 362]
-/
noncomputable def jfFormula : Formula (Fin F.1) :=
  ◇^[F.1]⊤ ⋎ ⋁((List.range F.1).map fun k => ◇^[k](∼F.jfDiagram)) ⋎ ∼F.jfRoot

variable {κ : Type*} {M : Model κ (Fin F.1)} {x : M.World}

lemma forces_jfDiagram : x ⊩ F.jfDiagram ↔
    (∀ i j : F.2.World, x ⊩ #i → (x ⊩ ◇#j ↔ i ≺ j)) ∧
      (∀ i j, i ≠ j → x ⊩ #i → x ⊮ #j) ∧ ∃ i, x ⊩ #i := by
  have h₁ : ∀ i j : F.2.World, x ⊩ F.jfEdge i j ↔
      (x ⊩ #i → (x ⊩ ◇#j ↔ i ≺ j)) := by
    intro i j;
    unfold jfEdge;
    split_ifs with Rij <;> simp [forces_imp, Rij] <;> tauto;
  have h₂ : ∀ i j, x ⊩ F.jfDistinct i j ↔ (i ≠ j → x ⊩ #i → x ⊮ #j) := by
    intro i j;
    unfold jfDistinct;
    split_ifs with h;
    · simp [h];
    · simp only [forces_neg, not_forces_and, ne_eq, h, not_false_eq_true, true_imp_iff];
      tauto;
  simp only [jfDiagram, forces_and, forces_conj_map, forces_disj_map, Finset.mem_toList,
    Finset.mem_univ, true_imp_iff, true_and, Prod.forall, h₁, h₂];

lemma forces_jfRoot : x ⊩ F.jfRoot ↔ ∃ i : F.2.Root, x ⊩ #i.1 := by
  classical
  simp [jfRoot];

lemma not_forces_jfFormula_iff : x ⊮ F.jfFormula ↔
    (∀ y, x ⊀^[F.1] y) ∧
      (∀ k < F.1, ∀ y, (x ≺^[k] y) → y ⊩ F.jfDiagram) ∧
      ∃ i : F.2.Root, x ⊩ #i.1 := by
  simp only [jfFormula, not_forces_or, forces_jfRoot, NotForces, forces_disj_map,
    List.mem_range, forces_multidia, forces_neg, forces_top, not_true_eq_false, imp_false,
    not_exists, not_and, not_not, not_forall];

/-- If `F` is rooted and cycle-free, then `F.2 ⊭ F.jfFormula`.
- [CZ98, p. 362]
-/
theorem not_validates_jfFormula (hF : F.RootedCycleFree) : F.2 ⊭ F.jfFormula := by
  obtain ⟨⟨r, hr⟩⟩ := hF.isRooted;
  by_contra h;
  apply not_forces_jfFormula_iff (M := ⟨F.2, fun w a => w = a⟩) |>.mpr _ (h _ r);
  and_intros;
  · intro y Rry;
    obtain ⟨z, -, k, hk, Rzz⟩ := Frame.exists_cycle_of_relItr_card (F := F.2) (by simpa using Rry);
    exact hF.cycleFree ⟨z, k, hk, Rzz⟩;
  · intro k _ y _;
    apply (forces_jfDiagram F).mpr;
    and_intros;
    · rintro i j rfl;
      constructor;
      · rintro ⟨z, Ryz, rfl⟩;
        assumption;
      · intro Rij;
        use j;
        tauto;
    · intro i j hij hi hj;
      exact hij (hi.symm.trans hj);
    · use y;
      tauto;
  · exact ⟨⟨r, hr⟩, rfl⟩;

lemma exists_forces_of_forces_jfDiagram (hx : x ⊩ F.jfDiagram) : ∃ i, x ⊩ #i :=
  ((forces_jfDiagram F).mp hx).2.2

lemma eq_of_forces_of_forces_jfDiagram (hx : x ⊩ F.jfDiagram) {i j : Fin F.1}
    (hi : x ⊩ #i) (hj : x ⊩ #j) : i = j := by
  by_contra hij;
  exact ((forces_jfDiagram F).mp hx).2.1 i j hij hi hj;

variable {u₀ : M.World}

/-- The p-morphism `M.toFrame⥜u₀ →ₚ F.2` sending `u` to the `i` with `u.1 ⊩[M] #i`, given
`F.jfDiagram` at every point of `M.toFrame.Reach u₀`.
- [CZ98, p. 362]
-/
noncomputable def jfPMorphism (hδ : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] F.jfDiagram) :
    M.toFrame⥜u₀ →ₚ F.2 where
  toFun u := (exists_forces_of_forces_jfDiagram F (hδ u)).choose
  forth := by
    intro u v Ruv;
    have hu := (exists_forces_of_forces_jfDiagram F (hδ u)).choose_spec;
    have hv := (exists_forces_of_forces_jfDiagram F (hδ v)).choose_spec;
    exact (((forces_jfDiagram F).mp <| hδ u).1 _ _ hu).mp (forces_dia.mpr ⟨v.1, Ruv, hv⟩);
  back := by
    intro u j Ruj;
    have hu := (exists_forces_of_forces_jfDiagram F (hδ u)).choose_spec;
    obtain ⟨v, Ruv, hv⟩ := forces_dia.mp <| (((forces_jfDiagram F).mp <| hδ u).1 _ _ hu).mpr Ruj;
    refine ⟨⟨v, reach_of_rel u.2 Ruv⟩, Ruv, ?_⟩;
    exact eq_of_forces_of_forces_jfDiagram F (hδ _)
      (exists_forces_of_forces_jfDiagram F (hδ ⟨v, reach_of_rel u.2 Ruv⟩)).choose_spec hv;

lemma jfPMorphism_eq_iff (hδ : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] F.jfDiagram)
    (u : (M.toFrame⥜u₀).World) (i : Fin F.1) :
    jfPMorphism F hδ u = i ↔ u.1 ⊩[M] #i := by
  constructor;
  · rintro rfl;
    exact (exists_forces_of_forces_jfDiagram F (hδ u)).choose_spec;
  · exact fun hi => eq_of_forces_of_forces_jfDiagram F (hδ u)
      (exists_forces_of_forces_jfDiagram F (hδ u)).choose_spec hi;

lemma jfPMorphism_surjective (hδ : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] F.jfDiagram)
    (r : F.2.Root) (hr₀ : u₀ ⊩[M] #r.1) :
    Function.Surjective (jfPMorphism F hδ) := by
  have hf₀ : jfPMorphism F hδ (pointGenerate.root M.toFrame u₀) = r.1 :=
    (jfPMorphism_eq_iff F hδ _ _).mpr hr₀;
  intro j;
  obtain ⟨k, Rrj⟩ := r.2 j;
  rw [← hf₀] at Rrj;
  obtain ⟨u, -, hu⟩ := (jfPMorphism F hδ).back_relItr Rrj;
  exact ⟨u, hu⟩;

/-- If `u₀ ⊮[M] F.jfFormula`, there is a surjective p-morphism `f : M.toFrame⥜u₀ →ₚ F.2` with
`f u = i ↔ u.1 ⊩[M] #i`.
- [CZ98, p. 362]
-/
theorem jfFormula_spec (h : u₀ ⊮[M] F.jfFormula) :
    ∃ f : M.toFrame⥜u₀ →ₚ F.2, Function.Surjective f ∧
      ∀ u i, f u = i ↔ u.1 ⊩[M] #i := by
  obtain ⟨hn, hδ, r, hr₀⟩ := (not_forces_jfFormula_iff (F := F)).mp h;
  have hδ' : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] F.jfDiagram := by
    rintro ⟨u, k, Ru₀u⟩;
    apply hδ k _ u Ru₀u;
    by_contra! hkn;
    obtain ⟨y, Ru₀y⟩ := exists_relItr_of_le Ru₀u hkn;
    exact hn y Ru₀y;
  exact ⟨jfPMorphism F hδ', jfPMorphism_surjective F hδ' r hr₀, jfPMorphism_eq_iff F hδ'⟩;

end FinFrame

end
