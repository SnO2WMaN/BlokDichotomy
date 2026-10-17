module

public import BlokDichotomy.Kripke.Filtration
public import BlokDichotomy.Kripke.JankovFine
public import BlokDichotomy.Kripke.Transport
public import BlokDichotomy.Kripke.Types
public import BlokDichotomy.Logic.Restrict
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Splittings by finite rooted cycle-free frames, and their finite model property

Union-splittings `unionSplitting 𝔉` of `K` by sets of finite rooted cycle-free frames, the core of
a normal logic, and the finite model property of union-splittings.

## References

- [CZ98, Theorem 10.53, Theorem 10.54, Proposition 10.50, Lemma 10.55, p. 361]
-/

@[expose] public section

namespace Frame

open Formula Model.World

/-- Let `M` validate `L.restrict m`, and let `f : M.toFrame⥜x →ₚ F` be surjective such that every
valuation `U` on `F` is given by a substitution `s`. Then `F ⊧ L`.
- [CZ98, Theorem 10.53]
-/
theorem validateLogic_of_definable_pMorphism {L : NormalLogic ℕ} {m : ℕ} {κ ι : Type*}
    {M : Model κ (Fin m)} (hM : ∀ φ ∈ L.restrict m, M ⊧ φ) {x : M.World} {F : Frame ι}
    (f : M.toFrame⥜x →ₚ F) (hf : Function.Surjective f)
    (hdef : ∀ U : F.World → ℕ → Prop, ∃ s : Substitution ℕ (Fin m),
      ∀ (y : M.toFrame.Reach x) q, y.1 ⊩[M] s q ↔ U (f y) q) :
    F ⊧ L := by
  intro φ hA U w;
  obtain ⟨s, hs⟩ := hdef U;
  let M' : Model _ ℕ := ⟨M.toFrame, fun y a => y ⊩[M] s a⟩;
  have h₁ : ∀ y : (M'⥜x).World, y ⊩ φ := fun y =>
    forces_pointGenerate.mpr <| (forces_subst s).mp <|
      hM _ (NormalLogic.subst_mem_restrict hA s) y.1;
  obtain ⟨y, rfl⟩ := hf w;
  exact Model.PMorphism.forces_iff (M := M'⥜x) (N := ⟨F, U⟩)
    { f with val_iff := hs _ _ } |>.mp <| h₁ y;

/-- For a rooted cycle-free `F`, `F.2 ⊧ L` iff `F.jfFormula.map Fin.val ∉ L`.
- [CZ98, Theorem 10.53]
-/
theorem splitting_of_cycleFree {F : FinFrame} (hF : F.RootedCycleFree) {L : NormalLogic ℕ}
    [L.IsNExt 𝐊] : F.2 ⊧ L ↔ F.jfFormula.map Fin.val ∉ L := by
  classical
  constructor;
  · intro hFL hχ;
    exact FinFrame.not_validates_jfFormula F hF <| validates_map_finVal_iff.mp <| hFL _ hχ;
  · intro hχ;
    obtain ⟨x, hx⟩ :=
      NormalLogic.exists_world_not_forces (L := L.restrict F.1) (φ := F.jfFormula) hχ;
    obtain ⟨f, hf, hfi⟩ := FinFrame.jfFormula_spec F hx;
    apply validateLogic_of_definable_pMorphism
      (fun _ hA => NormalLogic.canonicalModel_validates_of_mem hA) f hf;
    intro U;
    use fun q => ⋁((Finset.univ.filter (U · q)).toList.map (#·));
    intro y q;
    simp only [forces_disj_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
      ← hfi];
    exact ⟨fun ⟨_, hi, he⟩ => he ▸ hi, fun h => ⟨_, h, rfl⟩⟩;

end Frame

/-- The extension of `K` by the formulas `F.jfFormula.map Fin.val` for `F ∈ 𝔉`.
- [CZ98, p. 361]
-/
noncomputable def unionSplitting (𝔉 : Set FinFrame) : NormalLogic ℕ :=
  (𝐊 : NormalLogic ℕ) + ((fun F : FinFrame => F.jfFormula.map Fin.val) '' 𝔉)

namespace NormalLogic

open Frame

variable {𝔉 𝔊 : Set FinFrame} {L L₁ : NormalLogic ℕ}

instance : (unionSplitting 𝔉).IsNExt 𝐊 := by
  unfold unionSplitting;
  infer_instance;

lemma jfFormula_mem_unionSplitting {F : FinFrame} (h : F ∈ 𝔉) :
    F.jfFormula.map Fin.val ∈ unionSplitting 𝔉 :=
  NormalLogic.mem_add ⟨F, h, rfl⟩

@[gcongr]
lemma unionSplitting_mono (h : 𝔉 ⊆ 𝔊) : unionSplitting 𝔉 ≤ unionSplitting 𝔊 :=
  NormalLogic.add_mono le_rfl <| Set.image_mono h

/-- `unionSplitting 𝔉 ≤ L` iff `F.2 ⊭ L` for every `F ∈ 𝔉`.
- [CZ98, Proposition 10.50]
-/
theorem unionSplitting_le_iff (h𝔉 : ∀ F ∈ 𝔉, FinFrame.RootedCycleFree F) [L.IsNExt 𝐊] :
    unionSplitting 𝔉 ≤ L ↔ ∀ F ∈ 𝔉, F.2 ⊭ L := by
  constructor;
  · intro hle F hF hFL;
    exact (splitting_of_cycleFree (h𝔉 F hF)).mp hFL <|
      hle <| jfFormula_mem_unionSplitting hF;
  · intro h;
    apply NormalLogic.add_le IsNExt.logic_le;
    rintro _ ⟨F, hF, rfl⟩;
    by_contra hχ;
    exact h F hF <| (splitting_of_cycleFree (h𝔉 F hF)).mpr hχ;

/-- `F.2 ⊭ unionSplitting 𝔉` for every `F ∈ 𝔉`.
- [CZ98, Proposition 10.50]
-/
lemma not_validates_unionSplitting (h𝔉 : ∀ F ∈ 𝔉, F.RootedCycleFree)
    {F : FinFrame} (hF : F ∈ 𝔉) : F.2 ⊭ unionSplitting 𝔉 :=
  (unionSplitting_le_iff h𝔉).mp le_rfl F hF

/-- `L = unionSplitting 𝔉` for some set `𝔉` of rooted cycle-free frames.
- [CZ98, p. 361]
-/
def IsUnionSplitting (L : NormalLogic ℕ) : Prop :=
  ∃ 𝔉 : Set FinFrame, (∀ F ∈ 𝔉, F.RootedCycleFree) ∧ L = unionSplitting 𝔉

def coreFrames (L : NormalLogic ℕ) : Set FinFrame :=
  {F | FinFrame.RootedCycleFree F ∧ F.2 ⊭ L}

lemma rootedCycleFree_of_mem_coreFrames {F : FinFrame} (h : F ∈ coreFrames L) :
    F.RootedCycleFree :=
  h.1

noncomputable def coreUnionSplitting (L : NormalLogic ℕ) : NormalLogic ℕ :=
  unionSplitting (coreFrames L)

lemma isUnionSplitting_coreUnionSplitting : (coreUnionSplitting L).IsUnionSplitting :=
  ⟨coreFrames L, fun _ hF => hF.1, rfl⟩

lemma coreUnionSplitting_le [L.IsNExt 𝐊] : coreUnionSplitting L ≤ L :=
  (unionSplitting_le_iff fun _ hF => hF.1).mpr fun _ hF => hF.2

lemma le_coreUnionSplitting (h : L₁.IsUnionSplitting) (hle : L₁ ≤ L) :
    L₁ ≤ coreUnionSplitting L := by
  obtain ⟨𝔉, h𝔉, rfl⟩ := h;
  apply unionSplitting_mono;
  intro F hF;
  exact ⟨h𝔉 F hF, fun hFL => not_validates_unionSplitting h𝔉 hF fun φ hA => hFL φ <| hle hA⟩;

theorem isGreatest_coreUnionSplitting [L.IsNExt 𝐊] :
    IsGreatest {L₁ | L₁.IsUnionSplitting ∧ L₁ ≤ L} (coreUnionSplitting L) :=
  ⟨⟨isUnionSplitting_coreUnionSplitting, coreUnionSplitting_le⟩,
    fun _ hL₁ => le_coreUnionSplitting hL₁.1 hL₁.2⟩

/-- `L.IsUnionSplitting` iff `L = coreUnionSplitting L`.
- [CZ98, p. 361]
-/
theorem isUnionSplitting_iff_eq_core [L.IsNExt 𝐊] :
    L.IsUnionSplitting ↔ L = coreUnionSplitting L :=
  ⟨fun h => le_antisymm (le_coreUnionSplitting h le_rfl) coreUnionSplitting_le,
    fun h => h ▸ isUnionSplitting_coreUnionSplitting⟩

end NormalLogic




namespace PartialFiltration

open Formula Model.World Frame NormalLogic

variable {m : ℕ} {L : NormalLogic (Fin m)} (φ : Formula (Fin m)) (k : ℕ)

open Classical in
noncomputable def profile (x : (canonicalModel L).World) : Finset (Formula (Fin m)) :=
  φ.subformulas.filter (x ⊩ ·)

variable {φ k}

lemma mem_profile {x : (canonicalModel L).World} {ψ : Formula (Fin m)} :
    ψ ∈ profile φ x ↔ ψ ∈ φ.subformulas ∧ x ⊩ ψ := by
  classical
  simp [profile];

lemma profile_subset {x : (canonicalModel L).World} : profile φ x ⊆ φ.subformulas := by
  classical
  exact Finset.filter_subset _ _;

variable (L φ k) in
/-- For every `x` with `x ⊩ ◇^[k]⊤` and every `j`, some `y` has `profile φ y = profile φ x` and
`y ⊩ ◇^[j]⊤`.
- [CZ98, Theorem 10.54]
-/
def IsDepth : Prop :=
  ∀ x : (canonicalModel L).World, x ⊩[canonicalModel L] ◇^[k]⊤ →
    ∀ j, ∃ y : (canonicalModel L).World, profile φ y = profile φ x ∧ y ⊩[canonicalModel L] ◇^[j]⊤

variable (L φ) in
/-- `IsDepth L φ k` holds for some `k`.
- [CZ98, Theorem 10.54]
-/
lemma exists_isDepth : ∃ k, IsDepth L φ k := by
  classical
  let g : Finset (Formula (Fin m)) → ℕ := fun P =>
    if h : ∃ j, ∀ y : (canonicalModel L).World, profile φ y = P → y ⊩ ∼◇^[j]⊤ then h.choose
    else 0;
  use φ.subformulas.powerset.sup g;
  intro x hx j;
  by_contra! hc;
  have hb : ∃ j, ∀ y : (canonicalModel L).World, profile φ y = profile φ x → y ⊩ ∼◇^[j]⊤ :=
    ⟨j, hc⟩;
  have h₁ : x ⊩ ∼◇^[g (profile φ x)]⊤ := by
    simp only [g, hb, dite_true];
    exact hb.choose_spec x rfl;
  have h₂ : g (profile φ x) ≤ φ.subformulas.powerset.sup g :=
    Finset.le_sup <| Finset.mem_powerset.mpr profile_subset;
  obtain ⟨y, Rxy⟩ := forces_multidia_top.mp hx;
  obtain ⟨z, Rxz⟩ := exists_relItr_of_le Rxy h₂;
  exact forces_neg_multidia_top.mp h₁ z Rxz;

variable (φ k) in
open Classical in
noncomputable def cls (x : (canonicalModel L).World) :
    (canonicalModel L).World ⊕ Finset (Formula (Fin m)) :=
  if x ⊩ ∼◇^[k]⊤ then .inl x else .inr (profile φ x)

variable (L φ k) in
abbrev Point := Set.range (cls (L := L) φ k)

variable (φ k) in
noncomputable def proj (x : (canonicalModel L).World) : Point L φ k := ⟨cls φ k x, x, rfl⟩

variable (L φ k) in
/-- The filtration of `canonicalModel L` through `proj φ k`.
- [CZ98, Theorem 10.54]
-/
noncomputable def model : Model (Point L φ k) (Fin m) := (canonicalModel L).filtration (proj φ k)

variable {x y : (canonicalModel L).World}

lemma cls_of_forces (hx : x ⊩ ∼◇^[k]⊤) : cls φ k x = .inl x := by
  classical
  simp [cls, hx];

lemma cls_of_not_forces (hx : x ⊮ ∼◇^[k]⊤) : cls φ k x = .inr (profile φ x) := by
  classical
  simp only [cls, ite_eq_right_iff];
  exact fun h => absurd h hx;

lemma proj_eq_iff_cls_eq : proj φ k x = proj φ k y ↔ cls φ k x = cls φ k y := Subtype.ext_iff

lemma proj_eq_iff_of_forces (hx : x ⊩ ∼◇^[k]⊤) : proj φ k y = proj φ k x ↔ y = x := by
  rw [proj_eq_iff_cls_eq, cls_of_forces hx];
  by_cases hy : y ⊩ ∼◇^[k]⊤;
  · rw [cls_of_forces hy, Sum.inl.injEq];
  · rw [cls_of_not_forces hy];
    exact iff_of_false Sum.inr_ne_inl fun h => hy (h ▸ hx);

lemma proj_eq_of_not_forces (hx : x ⊮ ∼◇^[k]⊤) (hy : y ⊮ ∼◇^[k]⊤)
    (h : profile φ y = profile φ x) : proj φ k y = proj φ k x := by
  rw [proj_eq_iff_cls_eq, cls_of_not_forces hx, cls_of_not_forces hy, h];

lemma forces_iff_of_proj_eq (h : proj φ k x = proj φ k y) :
    ∀ ψ ∈ φ.subformulas, x ⊩ ψ ↔ y ⊩ ψ := by
  intro ψ hB;
  by_cases hx : x ⊩ ∼◇^[k]⊤;
  · rw [(proj_eq_iff_of_forces hx).mp h.symm];
  · by_cases hy : y ⊩ ∼◇^[k]⊤;
    · rw [(proj_eq_iff_of_forces hy).mp h];
    · rw [proj_eq_iff_cls_eq, cls_of_not_forces hx, cls_of_not_forces hy, Sum.inr.injEq] at h;
      have h' := Finset.ext_iff.mp h ψ;
      simpa only [mem_profile, hB, true_and] using h';

instance [L.IsNExt 𝐊] : Finite (Point L φ k) := by
  classical
  apply Set.Finite.to_subtype;
  apply ((((canonicalModel.finite_neg_multidia_top (L := L) k).image Sum.inl).union
    ((φ.subformulas.powerset.finite_toSet).image Sum.inr))).subset;
  rintro _ ⟨x, rfl⟩;
  by_cases hx : x ⊩ ∼◇^[k]⊤;
  · exact Or.inl ⟨x, hx, (cls_of_forces hx).symm⟩;
  · exact Or.inr ⟨profile φ x, Finset.mem_coe.mpr <| Finset.mem_powerset.mpr profile_subset,
      (cls_of_not_forces hx).symm⟩;

/-- `x ⊩ φ` iff `proj φ k x ⊩[model L φ k] φ`.
- [CZ98, Theorem 10.54]
-/
lemma forces_model_iff : x ⊩ φ ↔ proj φ k x ⊩[model L φ k] φ :=
  forces_filtration fun _ _ h => forces_iff_of_proj_eq h

lemma forces_of_mem_reach (hx : x ⊩ ∼◇^[k]⊤) (hy : y ∈ (canonicalModel L).Reach x) :
    y ⊩ ∼◇^[k]⊤ := by
  obtain ⟨j, Rxy⟩ := hy;
  rw [forces_neg_multidia_top] at hx ⊢;
  intro z Ryz;
  obtain ⟨w, Rxw⟩ := exists_relItr_of_le (relItr_trans Rxy Ryz) (Nat.le_add_left k j);
  exact hx w Rxw;

lemma proj_mem_reach (hy : y ∈ (canonicalModel L).Reach x) :
    proj φ k y ∈ (model L φ k).Reach (proj φ k x) := by
  obtain ⟨j, Rxy⟩ := hy;
  exact ⟨j, Model.filtration_relItr Rxy⟩;

/-- For `x ⊩ ∼◇^[k]⊤`, the p-morphism from the subframe of `canonicalModel L` generated by `x` to
the subframe of `model L φ k` generated by `proj φ k x`. -/
noncomputable def embed (hx : x ⊩ ∼◇^[k]⊤) :
    (canonicalModel L).toFrame⥜x →ₚ (model L φ k).toFrame⥜(proj φ k x) where
  toFun y := ⟨proj φ k y.1, proj_mem_reach y.2⟩
  forth Rxy := Model.filtration_rel Rxy
  back {y b} Ryb := by
    obtain ⟨y₁, y₂, h₁, h₂, Ry₁y₂⟩ := Ryb;
    obtain rfl := (proj_eq_iff_of_forces (forces_of_mem_reach hx y.2)).mp h₁;
    exact ⟨⟨y₂, reach_of_rel y.2 Ry₁y₂⟩, Ry₁y₂, Subtype.ext h₂⟩;

lemma embed_surjective (hx : x ⊩ ∼◇^[k]⊤) : Function.Surjective (embed (φ := φ) hx) := by
  rintro ⟨b, j, Rxb⟩;
  obtain ⟨y, -, hy⟩ := (embed (φ := φ) hx).back_relItr
    (x := (pointGenerate.root _ x).1) (z := ⟨b, j, Rxb⟩) <| pointGenerate_relItr.mpr Rxb;
  exact ⟨y, hy⟩;

lemma exists_relItr_proj (hk : IsDepth L φ k) (hx : x ⊮ ∼◇^[k]⊤) (j : ℕ) :
    ∃ w, Frame.RelItr (F := (model L φ k).toFrame) j (proj φ k x) w := by
  have hx' : x ⊩ ◇^[k]⊤ := by simpa [NotForces, forces_neg] using hx;
  obtain ⟨y, hy, hyj⟩ := hk x hx' (j + k);
  obtain ⟨w, Ryw⟩ := forces_multidia_top.mp hyj;
  obtain ⟨w₁, Ryw₁⟩ := exists_relItr_of_le Ryw (Nat.le_add_right j k);
  have hy' : y ⊮ ∼◇^[k]⊤ := by
    obtain ⟨w₂, Ryw₂⟩ := exists_relItr_of_le Ryw (Nat.le_add_left k j);
    exact fun h => forces_neg_multidia_top.mp h w₂ Ryw₂;
  rw [← proj_eq_of_not_forces hx hy' hy];
  exact ⟨_, Model.filtration_relItr Ryw₁⟩;

/-- For `x ⊩ ∼◇^[k]⊤`, `f : (canonicalModel L).Reach x → ι` and `U : ι → ℕ → Prop`, some
substitution `s` satisfies `y.1 ⊩ s q ↔ U (f y) q`. -/
lemma exists_definable [L.IsNExt 𝐊] {ι : Type*} (hx : x ⊩ ∼◇^[k]⊤)
    (f : (canonicalModel L).Reach x → ι) (U : ι → ℕ → Prop) :
    ∃ s : Substitution ℕ (Fin m), ∀ (y : (canonicalModel L).Reach x) q,
      y.1 ⊩ s q ↔ U (f y) q := by
  classical
  have hfin : ((canonicalModel L).Reach x).Finite :=
    (canonicalModel.finite_neg_multidia_top k).subset fun _ hy => forces_of_mem_reach hx hy;
  let θ : (canonicalModel L).World → Formula (Fin m) := fun y =>
    if hy : y ⊩ ∼◇^[k]⊤ then (canonicalModel.exists_characteristic hy).choose else ⊥;
  have hθ : ∀ y, y ∈ (canonicalModel L).Reach x → ∀ y', y' ⊩ θ y ↔ y' = y := by
    intro y hy;
    have hy' := forces_of_mem_reach hx hy;
    simp only [θ, hy', dite_true];
    exact (canonicalModel.exists_characteristic hy').choose_spec;
  use fun q => ⋁((hfin.toFinset.filter fun y => ∃ hy : y ∈ (canonicalModel L).Reach x,
    U (f ⟨y, hy⟩) q).toList.map θ);
  intro y q;
  simp only [forces_disj_map, Finset.mem_toList, Finset.mem_filter, Set.Finite.mem_toFinset];
  constructor;
  · rintro ⟨y', ⟨hy', hy'', hU⟩, hθy⟩;
    obtain rfl := (hθ y' hy' y.1).mp hθy;
    exact hU;
  · intro h;
    exact ⟨y.1, ⟨y.2, y.2, h⟩, (hθ _ y.2 _).mpr rfl⟩;

end PartialFiltration


namespace NormalLogic

open Formula Model.World Frame PartialFiltration

variable {𝔉 : Set FinFrame}

/-- If `IsDepth ((unionSplitting 𝔉).restrict m) φ k`, then
`model ((unionSplitting 𝔉).restrict m) φ k` validates `unionSplitting 𝔉`.
- [CZ98, Theorem 10.54]
-/
lemma validates_partialFiltration (h𝔉 : ∀ F ∈ 𝔉, FinFrame.RootedCycleFree F) {m k : ℕ}
    {φ : Formula (Fin m)} (hk : IsDepth ((unionSplitting 𝔉).restrict m) φ k) :
    (model ((unionSplitting 𝔉).restrict m) φ k).toFrame ⊧ unionSplitting 𝔉 := by
  set G := (model ((unionSplitting 𝔉).restrict m) φ k).toFrame;
  by_contra hG;
  have : ∃ F ∈ 𝔉, G ⊭ F.jfFormula.map Fin.val := by
    by_contra! h;
    apply hG <| validates_add validates_logicK _;
    rintro _ ⟨F, hF, rfl⟩;
    exact h F hF;
  obtain ⟨F, hF, hχ⟩ := this;
  replace hχ : G ⊭ F.jfFormula := fun h => hχ <| validates_map_finVal_iff.mpr h;
  obtain ⟨V, z, hz⟩ := Frame.not_validates_iff'.mp hχ;
  obtain ⟨g, hg, -⟩ := FinFrame.jfFormula_spec F (M := ⟨G, V⟩) hz;
  rcases exists_forces_farthest_or_reach_cycle (M := ⟨G, V⟩) (x := z) with
    ⟨t, ht⟩ | ⟨y, hy, j, hj, Ryy⟩;
  · obtain ⟨_, x, rfl⟩ := z;
    by_cases hx : x ⊩ ∼◇^[k]⊤;
    · apply not_validates_unionSplitting h𝔉 hF;
      exact validateLogic_of_definable_pMorphism
        (fun _ hA => canonicalModel_validates_of_mem hA) (g.comp (embed hx))
        (hg.comp (embed_surjective hx)) (exists_definable hx _);
    · obtain ⟨w, Rxw⟩ := exists_relItr_proj hk hx (t + 1);
      exact (iff_forces_farthest.mp ht).2 w Rxw;
  · exact (h𝔉 F hF).cycleFree <|
      HasCycle.of_pMorphism g ⟨⟨y, hy⟩, j, hj, pointGenerate_relItr.mpr Ryy⟩;

/-- If `φ ∉ unionSplitting 𝔉`, some finite frame `G` has `G ⊧ unionSplitting 𝔉` and `G ⊭ φ`.
- [CZ98, Theorem 10.54]
-/
theorem exists_finite_frame_of_not_mem_unionSplitting
    (h𝔉 : ∀ F ∈ 𝔉, FinFrame.RootedCycleFree F) {φ : Formula ℕ} (hφ : φ ∉ unionSplitting 𝔉) :
    ∃ (ι : Type) (_ : Finite ι) (G : Frame ι), G ⊧ unionSplitting 𝔉 ∧ G ⊭ φ := by
  obtain ⟨m, φ', rfl⟩ := φ.exists_map_finVal;
  obtain ⟨k, hk⟩ := exists_isDepth ((unionSplitting 𝔉).restrict m) φ';
  use Point ((unionSplitting 𝔉).restrict m) φ' k, inferInstance,
    (model ((unionSplitting 𝔉).restrict m) φ' k).toFrame;
  constructor;
  · exact validates_partialFiltration h𝔉 hk;
  · rw [Frame.NotValidates, validates_map_finVal_iff];
    intro h;
    obtain ⟨x, hx⟩ := exists_world_not_forces (L := (unionSplitting 𝔉).restrict m) hφ;
    exact hx <| forces_model_iff.mpr <|
      h (model ((unionSplitting 𝔉).restrict m) φ' k).Val' (proj φ' k x);

/-- If `φ ∉ unionSplitting 𝔉`, some frame `G` on `Fin m` has `G ⊧ unionSplitting 𝔉` and
`G ⊭ φ`.
- [CZ98, Theorem 10.54]
-/
theorem unionSplitting_fmp (h𝔉 : ∀ F ∈ 𝔉, FinFrame.RootedCycleFree F) {φ : Formula ℕ}
    (hφ : φ ∉ unionSplitting 𝔉) :
    ∃ (m : ℕ) (G : Frame (Fin m)), G ⊧ unionSplitting 𝔉 ∧ G ⊭ φ := by
  obtain ⟨ι, _, G, hG, hφ⟩ := exists_finite_frame_of_not_mem_unionSplitting h𝔉 hφ;
  let e := Finite.equivFin ι;
  exact ⟨Nat.card ι, G.transport e, validateLogic_transport_iff.mpr hG,
    fun h => hφ <| validates_transport_iff.mp h⟩;

end NormalLogic


end
