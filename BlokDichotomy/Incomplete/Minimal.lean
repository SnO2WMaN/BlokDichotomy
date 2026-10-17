module

public import BlokDichotomy.Incomplete.Hooked
public import BlokDichotomy.Formula
public import BlokDichotomy.Kripke.Splitting
public import BlokDichotomy.Kripke.Transport

/-!
# The minimal counterexample

A normal logic `L` that is not a union-splitting has a minimal finite counterexample, which gives
`HookData`.

## References

- [CZ98, p. 366]
-/

@[expose] public section

namespace Frame

variable {κ : Type*} {F : Frame κ} {x y : F.World} {α : Type*} {L : NormalLogic α}

lemma HasCycle.exists_path (h : F.HasCycle) : ∃ p : ℕ → F.World, ∀ t, p t ≺ p (t + 1) := by
  obtain ⟨x, k, hk, hx⟩ := h;
  obtain ⟨p, hp₀, hpk, hp⟩ := Frame.exists_path hx;
  use fun t => p (t % k);
  intro t;
  have hdm := Nat.div_add_mod t k;
  have hlt := Nat.mod_lt t hk;
  rcases Nat.lt_or_ge (t % k + 1) k with h | h;
  · have he : (t + 1) % k = t % k + 1 := by
      rw [show t + 1 = (t % k + 1) + k * (t / k) by omega, Nat.add_mul_mod_self_left];
      exact Nat.mod_eq_of_lt h;
    simpa only [he] using hp _ hlt;
  · have he : (t + 1) % k = 0 := by
      rw [show t + 1 = k * (t / k + 1) by rw [Nat.mul_succ]; omega, Nat.mul_mod_right];
    have h' := hp (k - 1) (by omega);
    rw [show k - 1 + 1 = k by omega, hpk, ← hp₀] at h';
    simpa only [he, show t % k = k - 1 by omega] using h';

lemma eq_of_mem_reach_of_forall_not_rel (hx : ∀ z, x ⊀ z) (h : y ∈ F.Reach x) : y = x := by
  obtain ⟨n, hn⟩ := h;
  cases n with
  | zero => exact hn.symm;
  | succ n =>
    obtain ⟨z, hz, -⟩ := hn;
    exact absurd hz (hx z);

lemma deadEnd_validates_of_forall_not_rel (hx : ∀ z, x ⊀ z) (h : F⥜x ⊧ L)
  : deadEnd ⊧ L := by
  let f : F⥜x →ₚ deadEnd :=
    { toFun := fun _ => 0
      forth := fun {y z} Ryz => by
        have Ryz' : y.1 ≺ z.1 := Ryz;
        rw [eq_of_mem_reach_of_forall_not_rel hx y.2] at Ryz';
        exact hx z.1 Ryz'
      back := fun h => h.elim };
  exact ValidateLogic.of_surjective_pMorphism f (fun i => ⟨(pointGenerate.root F x).1,
    Subsingleton.elim _ _⟩) h

lemma not_isRootedBy_of_forall_not_rel (hc : F.HasCycle) (hx : ∀ z, x ⊀ z) :
    ¬F.IsRootedBy x := by
  intro hr;
  obtain ⟨y, k, hk, hy⟩ := hc;
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne';
  obtain ⟨z, hz, -⟩ := hy;
  exact hx z <| eq_of_mem_reach_of_forall_not_rel hx (hr y) ▸ hz;

end Frame


namespace NormalLogic

open Frame Model.World

variable {L : NormalLogic ℕ} [L.IsNExt 𝐊]

private def IsCounter (L : NormalLogic ℕ) (n : ℕ) : Prop :=
  ∃ F : Frame (Fin n), F ⊧ coreUnionSplitting L ∧ F ⊭ L

omit [L.IsNExt 𝐊] in
private lemma isCounter_card {ι : Type*} {G : Frame ι} [Finite G.World]
    (h₁ : G ⊧ coreUnionSplitting L) (h₂ : G ⊭ L) : IsCounter L (Nat.card G.World) :=
  ⟨G.transport (Finite.equivFin G.World), validateLogic_transport_iff.mpr h₁,
    fun h => h₂ <| validateLogic_transport_iff.mp h⟩

private lemma exists_isCounter (hL : ¬L.IsUnionSplitting) : ∃ n, IsCounter L n := by
  obtain ⟨φ, hφ, hφc⟩ : ∃ φ ∈ L, φ ∉ coreUnionSplitting L := by
    by_contra! h;
    exact hL <| isUnionSplitting_iff_eq_core.mpr <| le_antisymm h coreUnionSplitting_le;
  obtain ⟨n, G, hG, hGφ⟩ := unionSplitting_fmp (𝔉 := coreFrames L) (fun _ hF => hF.1) hφc;
  exact ⟨n, G, hG, fun h => hGφ <| h φ hφ⟩;

private lemma card_reach_lt {n : ℕ} {F : Frame (Fin n)} {u : Fin n} (hu : ¬F.IsRootedBy u) :
    Nat.card (F.Reach u) < n := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, y ∉ F.Reach u := by simpa [IsRootedBy] using hu;
  calc Nat.card (F.Reach u) = Fintype.card {x // x ∈ F.Reach u} := Nat.card_eq_fintype_card
    _ < Fintype.card (Fin n) := Fintype.card_subtype_lt hy
    _ = n := Fintype.card_fin n;

/-- If `¬L.IsUnionSplitting`, there are a finite frame `F` with root `r`, validating
`coreUnionSplitting L` but not `L`, with `F⥜u ⊧ L` for every non-root `u`, refuting some `φ ∈ L`
at `r`, and with `F.HasCycle`.
- [CZ98, p. 366]
-/
theorem exists_minimal_counterexample (hL : ¬L.IsUnionSplitting) :
    ∃ (n : ℕ) (F : Frame (Fin n)) (r : F.Root),
      F ⊧ coreUnionSplitting L ∧ F ⊭ L ∧
      (∀ u : Fin n, ¬F.IsRootedBy u → F⥜u ⊧ L) ∧
      (∃ φ ∈ L, ∃ V : Fin n → ℕ → Prop, ¬r.1 ⊩[⟨F, V⟩] φ) ∧ F.HasCycle := by
  classical
  have hex := exists_isCounter hL;
  obtain ⟨F, hcore, hnL⟩ := Nat.find_spec hex;
  have hmin (u : Fin (Nat.find hex)) (hu : F⥜u ⊭ L) : F.IsRootedBy u := by
    by_contra hr;
    have h₁ := Nat.find_min' hex <| isCounter_card (ValidateLogic.pointGenerate hcore) hu;
    have h₂ : Nat.card (F⥜u).World < Nat.find hex := card_reach_lt hr;
    omega;
  obtain ⟨φ, hφ, hF⟩ : ∃ φ ∈ L, F ⊭ φ := by
    by_contra! h;
    exact hnL h;
  obtain ⟨V, r, hr⟩ : ∃ V r, ¬r ⊩[⟨F, V⟩] φ := by
    by_contra! h;
    exact hF h;
  have hroot : F.IsRootedBy r := hmin r fun h => hr <| forces_pointGenerate_root.mp <|
    h φ hφ (fun y a => V y.1 a) (pointGenerate.root F r).1;
  use Nat.find hex, F, ⟨r, hroot⟩, hcore, hnL;
  and_intros;
  · intro u hu;
    by_contra h;
    exact hu <| hmin u h;
  · exact ⟨φ, hφ, V, hr⟩;
  · by_contra hc;
    have hmem : (⟨_, F⟩ : FinFrame) ∈ coreFrames L := ⟨⟨⟨r, hroot⟩, hc⟩, hnL⟩;
    exact FinFrame.not_validates_jfFormula (F := ⟨_, F⟩) ⟨⟨r, hroot⟩, hc⟩ <|
      validates_map_finVal_iff.mp <| hcore _ <| jfFormula_mem_unionSplitting hmem;

/-- If `L.Consistent` and `¬L.IsUnionSplitting`, there are `D : HookData (Fin n)`, `φ ∈ L` and `V`
with `¬D.root ⊩[⟨D.F, V⟩] φ`, `φ.depth ≤ D.len + 1`, `D.F ⊧ coreUnionSplitting L`, `D.F ⊭ L`,
`D.F⥜u ⊧ L` for every non-root `u`, `D.refl ↔ deadEnd ⊭ L`, `deadEnd ⊧ L` if `¬D.refl`,
`reflPoint ⊧ L` and no dead end in `D.F` if `D.refl`.
- [CZ98, p. 366]
-/
theorem exists_hookData (hc : L.Consistent) (hL : ¬L.IsUnionSplitting) :
    ∃ (n : ℕ) (D : HookData (Fin n)) (φ : Formula ℕ) (V : Fin n → ℕ → Prop),
      φ ∈ L ∧ ¬D.root ⊩[⟨D.F, V⟩] φ ∧ φ.depth ≤ D.len + 1 ∧
      D.F ⊧ coreUnionSplitting L ∧ D.F ⊭ L ∧
      (∀ u, ¬D.F.IsRootedBy u → D.F⥜u ⊧ L) ∧
      (D.refl ↔ deadEnd ⊭ L) ∧ (¬D.refl → deadEnd ⊧ L) ∧
      (D.refl → reflPoint ⊧ L) ∧ (D.refl → ∀ u : D.F.World, ∃ v, u ≺ v) := by
  obtain ⟨n, F, r, hcore, hnL, hgen, ⟨φ, hφ, V, hV⟩, hcyc⟩ := exists_minimal_counterexample hL;
  obtain ⟨p, hp⟩ := hcyc.exists_path;
  let D : HookData (Fin n) :=
    { F := F, root := r, path := p, path_rel := hp, len := φ.depth,
      m := n + φ.depth + 2, card_add_len_lt := by simp, refl := deadEnd ⊭ L };
  use n, D, φ, V, hφ, hV, by simp [D], hcore, hnL, hgen, Iff.rfl, not_not.mp;
  and_intros;
  · exact (makinson hc).resolve_left;
  · intro hD u;
    by_contra! hu;
    exact hD <| deadEnd_validates_of_forall_not_rel hu <|
      hgen u <| not_isRootedBy_of_forall_not_rel hcyc hu;

end NormalLogic

end
