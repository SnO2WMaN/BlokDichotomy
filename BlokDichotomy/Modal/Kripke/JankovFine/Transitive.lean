module

public import BlokDichotomy.Modal.Kripke.PMorphism
public import BlokDichotomy.Modal.Formula
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod

/-!
# Jankov–Fine formulas for transitive logics

The Jankov–Fine formula `G.jfFormulaT` of a rooted finite frame `G : RootedFinFrame`, used over
`NExt K4`, and its characterisation on transitive frames: `F ⊭ G.jfFormulaT` iff `G.frame` is a
p-morphic image of a point-generated subframe of `F`.

## References

- [CZ98, §9.4, p. 362]
-/

@[expose] public section

namespace Modal

/-- A rooted frame on `Fin n`.
- [CZ98, p. 362]
-/
structure RootedFinFrame where
  n : ℕ
  frame : Frame (Fin n)
  isRooted : frame.IsRooted

namespace Frame

variable {κ : Type*} {F : Frame κ} {x y : F.World}

lemma reflTransRel_iff_of_trans [IsTrans _ F.Rel] : (x ≺^* y) ↔ y = x ∨ x ≺ y := by
  constructor;
  · rintro ⟨n, Rxy⟩;
    induction n generalizing x with
    | zero => exact Or.inl (iff_relItr_zero.mp Rxy).symm;
    | succ n ih =>
      obtain ⟨z, Rxz, Rzy⟩ := Rxy;
      rcases ih Rzy with rfl | Rzy;
      · exact Or.inr Rxz;
      · exact Or.inr (rel_trans Rxz Rzy);
  · rintro (rfl | Rxy);
    · exact reflTransRel_refl _;
    · exact reflTransRel_of_rel Rxy;

lemma PMorphism.isRootedBy_of_surjective {κ' : Type*} {F' : Frame κ'} {r : F'.World}
    (hr : F'.IsRootedBy r) (f : F' →ₚ F) (hf : Function.Surjective f) : F.IsRootedBy (f r) := by
  intro y;
  obtain ⟨z, rfl⟩ := hf y;
  exact f.forth_reflTransRel (hr z);

end Frame

namespace RootedFinFrame

open Formula Model.World Frame

variable (G : RootedFinFrame)

open Classical in
noncomputable def jfEdge (i j : G.frame.World) : Formula (Fin G.n) :=
  if i ≺ j then #i 🡒 ◇#j else #i 🡒 ∼◇#j

open Classical in
noncomputable def jfDistinct (i j : G.frame.World) : Formula (Fin G.n) :=
  if i = j then ⊤ else ∼(#i ⋏ #j)

/-- The diagram `δ(G)` of `G`.
- [CZ98, p. 362]
-/
noncomputable def jfDiagram : Formula (Fin G.n) :=
  ⋀((Finset.univ : Finset (Fin G.n × Fin G.n)).toList.map fun p => G.jfEdge p.1 p.2) ⋏
  ⋀((Finset.univ : Finset (Fin G.n × Fin G.n)).toList.map fun p => G.jfDistinct p.1 p.2) ⋏
  ⋁((Finset.univ : Finset (Fin G.n)).toList.map fun i => #i)

open Classical in
noncomputable def jfRoot : Formula (Fin G.n) :=
  ⋁((Finset.univ : Finset G.frame.Root).toList.map fun i => #i.1)

/-- The Jankov–Fine formula `χ(G) = ∼(#r ⋏ □⁺δ(G))` of `G` for transitive logics, where
`□⁺A = A ⋏ □A`.
- [CZ98, p. 362]
-/
noncomputable def jfFormulaT : Formula (Fin G.n) :=
  ∼(G.jfRoot ⋏ (G.jfDiagram ⋏ □G.jfDiagram))

variable {κ : Type*} {M : Model κ (Fin G.n)} {x : M.World}

lemma forces_jfDiagram : x ⊩ G.jfDiagram ↔
    (∀ i j : G.frame.World, x ⊩ #i → (x ⊩ ◇#j ↔ i ≺ j)) ∧
      (∀ i j, i ≠ j → x ⊩ #i → x ⊮ #j) ∧ ∃ i, x ⊩ #i := by
  have h₁ : ∀ i j : G.frame.World, x ⊩ G.jfEdge i j ↔
      (x ⊩ #i → (x ⊩ ◇#j ↔ i ≺ j)) := by
    intro i j;
    unfold jfEdge;
    split_ifs with Rij <;> simp [forces_imp, Rij] <;> tauto;
  have h₂ : ∀ i j, x ⊩ G.jfDistinct i j ↔ (i ≠ j → x ⊩ #i → x ⊮ #j) := by
    intro i j;
    unfold jfDistinct;
    split_ifs with h;
    · simp [h];
    · simp only [forces_neg, not_forces_and, ne_eq, h, not_false_eq_true, true_imp_iff];
      tauto;
  simp only [jfDiagram, forces_and, forces_conj_map, forces_disj_map, Finset.mem_toList,
    Finset.mem_univ, true_imp_iff, true_and, Prod.forall, h₁, h₂];

lemma forces_jfRoot : x ⊩ G.jfRoot ↔ ∃ i : G.frame.Root, x ⊩ #i.1 := by
  classical
  simp [jfRoot];

lemma not_forces_jfFormulaT_iff : x ⊮ G.jfFormulaT ↔
    (∃ i : G.frame.Root, x ⊩ #i.1) ∧ x ⊩ G.jfDiagram ∧ ∀ y, x ≺ y → y ⊩ G.jfDiagram := by
  rw [jfFormulaT, NotForces, forces_neg, not_not, forces_and, forces_and, forces_jfRoot,
    forces_box];

lemma exists_forces_of_forces_jfDiagram (hx : x ⊩ G.jfDiagram) : ∃ i, x ⊩ #i :=
  ((forces_jfDiagram G).mp hx).2.2

lemma eq_of_forces_of_forces_jfDiagram (hx : x ⊩ G.jfDiagram) {i j : Fin G.n}
    (hi : x ⊩ #i) (hj : x ⊩ #j) : i = j := by
  by_contra hij;
  exact ((forces_jfDiagram G).mp hx).2.1 i j hij hi hj;

variable {u₀ : M.World}

/-- The p-morphism `M.toFrame⥜u₀ →ₚ G.frame` sending `u` to the `i` with `u.1 ⊩[M] #i`, given
`G.jfDiagram` at every point of `M.toFrame.Reach u₀`.
- [CZ98, p. 362]
-/
noncomputable def jfPMorphism (hδ : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] G.jfDiagram) :
    M.toFrame⥜u₀ →ₚ G.frame where
  toFun u := (exists_forces_of_forces_jfDiagram G (hδ u)).choose
  forth := by
    intro u v Ruv;
    have hu := (exists_forces_of_forces_jfDiagram G (hδ u)).choose_spec;
    have hv := (exists_forces_of_forces_jfDiagram G (hδ v)).choose_spec;
    exact (((forces_jfDiagram G).mp <| hδ u).1 _ _ hu).mp (forces_dia.mpr ⟨v.1, Ruv, hv⟩);
  back := by
    intro u j Ruj;
    have hu := (exists_forces_of_forces_jfDiagram G (hδ u)).choose_spec;
    obtain ⟨v, Ruv, hv⟩ := forces_dia.mp <| (((forces_jfDiagram G).mp <| hδ u).1 _ _ hu).mpr Ruj;
    refine ⟨⟨v, ReflTransRel.tail u.2 Ruv⟩, Ruv, ?_⟩;
    exact eq_of_forces_of_forces_jfDiagram G (hδ _)
      (exists_forces_of_forces_jfDiagram G (hδ ⟨v, ReflTransRel.tail u.2 Ruv⟩)).choose_spec hv;

lemma jfPMorphism_eq_iff (hδ : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] G.jfDiagram)
    (u : (M.toFrame⥜u₀).World) (i : Fin G.n) :
    jfPMorphism G hδ u = i ↔ u.1 ⊩[M] #i := by
  constructor;
  · rintro rfl;
    exact (exists_forces_of_forces_jfDiagram G (hδ u)).choose_spec;
  · exact fun hi => eq_of_forces_of_forces_jfDiagram G (hδ u)
      (exists_forces_of_forces_jfDiagram G (hδ u)).choose_spec hi;

lemma jfPMorphism_surjective (hδ : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] G.jfDiagram)
    (r : G.frame.Root) (hr₀ : u₀ ⊩[M] #r.1) :
    Function.Surjective (jfPMorphism G hδ) := by
  have hf₀ : jfPMorphism G hδ (pointGenerate.root M.toFrame u₀) = r.1 :=
    (jfPMorphism_eq_iff G hδ _ _).mpr hr₀;
  intro j;
  obtain ⟨k, Rrj⟩ := r.2 j;
  rw [← hf₀] at Rrj;
  obtain ⟨u, -, hu⟩ := (jfPMorphism G hδ).back_relItr Rrj;
  exact ⟨u, hu⟩;

/-- If `u₀ ⊮[M] G.jfFormulaT` on a transitive `M`, there is a surjective p-morphism
`f : M.toFrame⥜u₀ →ₚ G.frame` with `f u = i ↔ u.1 ⊩[M] #i`.
- [CZ98, p. 362]
-/
theorem jfFormulaT_spec [IsTrans _ M.Rel] (h : u₀ ⊮[M] G.jfFormulaT) :
    ∃ f : M.toFrame⥜u₀ →ₚ G.frame, Function.Surjective f ∧
      ∀ u i, f u = i ↔ u.1 ⊩[M] #i := by
  obtain ⟨⟨r, hr₀⟩, hδ₀, hδ⟩ := (not_forces_jfFormulaT_iff G).mp h;
  have hδ' : ∀ u : M.toFrame.Reach u₀, u.1 ⊩[M] G.jfDiagram := by
    rintro ⟨u, hu⟩;
    rcases reflTransRel_iff_of_trans.mp hu with rfl | Ru₀u;
    · exact hδ₀;
    · exact hδ u Ru₀u;
  exact ⟨jfPMorphism G hδ', jfPMorphism_surjective G hδ' r hr₀, jfPMorphism_eq_iff G hδ'⟩;

section Converse

variable {κ : Type*} {F : Frame κ} {u₀ : F.World} (f : F⥜u₀ →ₚ G.frame)

/-- The valuation transported along `f`. -/
def pMorphismVal (w : F.World) (i : Fin G.n) : Prop := ∃ h : w ∈ F.Reach u₀, f ⟨w, h⟩ = i

lemma forces_pMorphismVal_iff {w : F.World} (hw : w ∈ F.Reach u₀) (i : Fin G.n) :
    w ⊩[⟨F, pMorphismVal G f⟩] #i ↔ f ⟨w, hw⟩ = i :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hw, h⟩⟩

lemma forces_jfDiagram_pMorphismVal {w : F.World} (hw : w ∈ F.Reach u₀) :
    w ⊩[⟨F, pMorphismVal G f⟩] G.jfDiagram := by
  rw [forces_jfDiagram];
  and_intros;
  · rintro i j hi;
    rw [forces_pMorphismVal_iff G f hw] at hi;
    subst hi;
    rw [forces_dia];
    constructor;
    · rintro ⟨y, Rwy, hy⟩;
      rw [forces_pMorphismVal_iff G f (ReflTransRel.tail hw Rwy)] at hy;
      exact hy ▸ f.forth (x := ⟨w, hw⟩) (y := ⟨y, _⟩) Rwy;
    · intro Rij;
      obtain ⟨y, Rwy, rfl⟩ := f.back (x := ⟨w, hw⟩) Rij;
      exact ⟨y.1, Rwy, (forces_pMorphismVal_iff G f y.2 _).mpr rfl⟩;
  · intro i j hij hi hj;
    rw [forces_pMorphismVal_iff G f hw] at hi hj;
    exact hij (hi.symm.trans hj);
  · exact ⟨f ⟨w, hw⟩, (forces_pMorphismVal_iff G f hw _).mpr rfl⟩;

/-- If `f : F⥜u₀ →ₚ G.frame` is surjective, then `G.jfFormulaT` is refuted at `u₀` in the model
with valuation `pMorphismVal G f`.
- [CZ98, p. 362]
-/
theorem not_forces_jfFormulaT_of_pMorphism (hf : Function.Surjective f) :
    u₀ ⊮[⟨F, pMorphismVal G f⟩] G.jfFormulaT := by
  rw [not_forces_jfFormulaT_iff];
  and_intros;
  · have hr := f.isRootedBy_of_surjective (pointGenerate.root F u₀).2 hf;
    exact ⟨⟨_, hr⟩, (forces_pMorphismVal_iff G f (reflTransRel_refl _) _).mpr rfl⟩;
  · exact forces_jfDiagram_pMorphismVal G f (reflTransRel_refl _);
  · exact fun y Ruy =>
      forces_jfDiagram_pMorphismVal G f (ReflTransRel.tail (reflTransRel_refl _) Ruy);

end Converse

/-- `G.frame ⊭ G.jfFormulaT`.
- [CZ98, p. 362]
-/
theorem not_validates_jfFormulaT : G.frame ⊭ G.jfFormulaT := by
  obtain ⟨⟨r, hr⟩⟩ := G.isRooted;
  intro h;
  have hf : Function.Surjective (PMorphism.ofPointGenerate G.frame r) :=
    fun y => ⟨⟨y, hr y⟩, rfl⟩;
  exact not_forces_jfFormulaT_of_pMorphism G _ hf (h _ r);

/-- For transitive `F`, `F ⊧ G.jfFormulaT` iff no generated subframe of `F` has `G.frame` as a
p-morphic image.
- [CZ98, p. 362]
-/
theorem validates_jfFormulaT_iff {κ : Type*} {F : Frame κ} [IsTrans _ F.Rel] :
    F ⊧ G.jfFormulaT ↔ ∀ x : F.World, ¬∃ f : F⥜x →ₚ G.frame, Function.Surjective f := by
  constructor;
  · rintro h x ⟨f, hf⟩;
    exact not_forces_jfFormulaT_of_pMorphism G f hf (h _ x);
  · intro h V x;
    by_contra hx;
    obtain ⟨f, hf, -⟩ := jfFormulaT_spec G (M := ⟨F, V⟩) hx;
    exact h x ⟨f, hf⟩;

end RootedFinFrame

end Modal

end
