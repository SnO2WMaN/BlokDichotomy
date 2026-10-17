module

public import BlokDichotomy.Kripke.Generated

/-!
# P-morphisms

P-morphisms of frames and models, and preservation of truth and validity.

## References

- [CZ98, §3.3, Theorem 3.15]
-/

@[expose] public section

universe u u₁ u₂ u₃ v

variable {κ₁ : Type u₁} {κ₂ : Type u₂} {k₃ : Type u₃} {α : Type v}

namespace Frame

/-- A p-morphism from `F` to `G`.
- [CZ98, §3.3] -/
structure PMorphism (F : Frame κ₁) (G : Frame κ₂) where
  toFun : F.World → G.World
  forth {x y : F.World} (Rxy : x ≺ y) : toFun x ≺ toFun y
  back {x : F.World} {z : G.World} (Rxz : toFun x ≺ z) : ∃ y, x ≺ y ∧ toFun y = z

infixr:25 " →ₚ " => PMorphism

namespace PMorphism

variable {F : Frame κ₁} {G : Frame κ₂} {H : Frame k₃} {x y : F.World} {z : G.World} {n : ℕ}

instance : CoeFun (F →ₚ G) (fun _ => F.World → G.World) := ⟨PMorphism.toFun⟩

variable (f : F →ₚ G)

@[simp] lemma toFun_eq_coe : f.toFun = ⇑f := rfl

protected def id (F : Frame κ₁) : F →ₚ F where
  toFun := id
  forth Rxy := Rxy
  back {_ z} Rxz := ⟨z, Rxz, rfl⟩

@[simp] lemma id_apply : PMorphism.id F x = x := rfl

def comp (g : G →ₚ H) (f : F →ₚ G) : F →ₚ H where
  toFun := g ∘ f
  forth Rxy := g.forth <| f.forth Rxy
  back {x w} Rxw := by
    obtain ⟨z, Rxz, rfl⟩ := g.back Rxw;
    obtain ⟨y, Rxy, rfl⟩ := f.back Rxz;
    exact ⟨y, Rxy, rfl⟩;

@[simp] lemma comp_apply (g : G →ₚ H) : g.comp f x = g (f x) := rfl

lemma forth_relItr (Rxy : x ≺^[n] y) : f x ≺^[n] f y := by
  induction n generalizing x with
  | zero => simp_all;
  | succ n ih =>
    obtain ⟨w, Rxw, Rwy⟩ := Rxy;
    exact ⟨f w, f.forth Rxw, ih Rwy⟩;

lemma back_relItr (Rxz : f x ≺^[n] z) : ∃ y, (x ≺^[n] y) ∧ f y = z := by
  induction n generalizing x with
  | zero => exact ⟨x, rfl, Rxz⟩;
  | succ n ih =>
    obtain ⟨w, Rxw, Rwz⟩ := Rxz;
    obtain ⟨y, Rxy, rfl⟩ := f.back Rxw;
    obtain ⟨y', Ryy', rfl⟩ := ih Rwz;
    exact ⟨y', ⟨y, Rxy, Ryy'⟩, rfl⟩;

lemma mem_reach (h : y ∈ F.Reach x) : f y ∈ G.Reach (f x) := by
  obtain ⟨n, Rxy⟩ := h;
  exact ⟨n, f.forth_relItr Rxy⟩;

/-- The inclusion `F⥜x →ₚ F`.
- [CZ98, §3.3] -/
def ofPointGenerate (F : Frame κ₁) (x : F.World) : F⥜x →ₚ F where
  toFun := Subtype.val
  forth Rxy := Rxy
  back {y z} Ryz := ⟨⟨z, reach_of_rel y.2 Ryz⟩, Ryz, rfl⟩

def pointGenerate (x : F.World) : F⥜x →ₚ G⥜(f x) where
  toFun y := ⟨f y.1, f.mem_reach y.2⟩
  forth Rxy := f.forth Rxy
  back {y z} Ryz := by
    obtain ⟨w, Ryw, hwz⟩ := f.back Ryz;
    exact ⟨⟨w, reach_of_rel y.2 Ryw⟩, Ryw, Subtype.ext hwz⟩;

lemma pointGenerate_surjective (x : F.World) : Function.Surjective (f.pointGenerate x) := by
  rintro ⟨z, n, Rxz⟩;
  obtain ⟨y, Rxy, rfl⟩ := f.back_relItr Rxz;
  exact ⟨⟨y, n, Rxy⟩, rfl⟩;

end PMorphism


section Regenerate

variable {F : Frame κ₁} {x : F.World}

def pointGenerate_pointGenerate (y : (F⥜x).World) :
    (F⥜x)⥜y →ₚ F⥜y.1 :=
  (PMorphism.ofPointGenerate F x).pointGenerate y

lemma pointGenerate_pointGenerate_surjective (y : (F⥜x).World) :
    Function.Surjective (pointGenerate_pointGenerate y) :=
  PMorphism.pointGenerate_surjective _ y

lemma pointGenerate_pointGenerate_injective (y : (F⥜x).World) :
    Function.Injective (pointGenerate_pointGenerate y) := by
  rintro ⟨⟨a, _⟩, _⟩ ⟨⟨b, _⟩, _⟩ h;
  simp only [pointGenerate_pointGenerate, PMorphism.pointGenerate, PMorphism.ofPointGenerate,
    Subtype.mk.injEq] at h;
  subst h;
  rfl;

end Regenerate

end Frame


namespace Model

/-- A p-morphism of the underlying frames of `M` and `N` preserving the valuation.
- [CZ98, §3.3] -/
structure PMorphism (M : Model κ₁ α) (N : Model κ₂ α) extends M.toFrame →ₚ N.toFrame where
  val_iff {x : M.World} {a : α} : M.Val x a ↔ N.Val (toFun x) a

infixr:25 " →ₚ " => PMorphism

namespace PMorphism

variable {M : Model κ₁ α} {N : Model κ₂ α} {x : M.World} {φ : Formula α}

instance : CoeFun (M →ₚ N) (fun _ => M.World → N.World) := ⟨fun f => f.toFun⟩

variable (f : M →ₚ N)

@[simp] lemma toFun_eq_coe : f.toFun = ⇑f := rfl

/-- `x ⊩[M] φ` iff `f x ⊩[N] φ`.
- [CZ98, Theorem 3.15] -/
lemma forces_iff : x ⊩[M] φ ↔ f x ⊩[N] φ := by
  induction φ generalizing x with
  | falsum => simp;
  | atom a => exact f.val_iff;
  | imp φ ψ ihφ ihψ => simp only [Model.World.forces_imp, Model.World.NotForces, ihφ, ihψ];
  | dia φ ih =>
    rw [Model.World.forces_dia, Model.World.forces_dia];
    constructor;
    · rintro ⟨y, Rxy, hy⟩;
      exact ⟨f y, f.forth Rxy, ih.mp hy⟩;
    · rintro ⟨z, Rxz, hz⟩;
      obtain ⟨y, Rxy, rfl⟩ := f.back Rxz;
      exact ⟨y, Rxy, ih.mpr hz⟩;

end PMorphism

end Model


namespace Frame

variable {F : Frame κ₁} {G : Frame κ₂} {φ : Formula α} {L : NormalLogic α}

open Model.World

/-- If `f : F →ₚ G` is surjective and `F ⊧ φ`, then `G ⊧ φ`.
- [CZ98, Theorem 3.15] -/
lemma Validates.of_surjective_pMorphism (f : F →ₚ G) (hf : Function.Surjective f) (h : F ⊧ φ) :
    G ⊧ φ := by
  intro V z;
  obtain ⟨x, rfl⟩ := hf z;
  exact Model.PMorphism.forces_iff
    (M := ⟨F, fun x a => V (f x) a⟩) (N := ⟨G, V⟩) { f with val_iff := Iff.rfl } |>.mp <| h _ x;

lemma ValidateLogic.of_surjective_pMorphism (f : F →ₚ G) (hf : Function.Surjective f)
    (h : F ⊧ L) : G ⊧ L :=
  fun φ hA => Validates.of_surjective_pMorphism f hf <| h φ hA

end Frame

end
