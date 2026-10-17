module

public import BlokDichotomy.Kripke.PMorphism

/-!
# Transporting a frame along a bijection

The frame `F.transport e` along a bijection `e`, and `F.ulift`.
-/

@[expose] public section

universe u u' v

variable {κ : Type u} {κ' : Type u'} {α : Type v}

namespace Frame

def transport (F : Frame κ) (e : κ ≃ κ') : Frame κ' :=
  ⟨fun a b => Rel (F := F) (e.symm a) (e.symm b)⟩

variable {F : Frame κ} {e : κ ≃ κ'} {φ : Formula α} {L : NormalLogic α}

def PMorphism.toTransport (F : Frame κ) (e : κ ≃ κ') : F →ₚ F.transport e where
  toFun := e
  forth {x y} Rxy := show Rel (F := F) (e.symm (e x)) (e.symm (e y)) by simpa using Rxy
  back {x z} Rxz := by
    have Rxz' : Rel (F := F) (e.symm (e x)) (e.symm z) := Rxz;
    exact ⟨e.symm z, by simpa using Rxz', by simp⟩;

def PMorphism.ofTransport (F : Frame κ) (e : κ ≃ κ') : F.transport e →ₚ F where
  toFun := e.symm
  forth Rxy := Rxy
  back {a y} Ray := ⟨e y, show Rel (F := F) (e.symm a) (e.symm (e y)) by simpa using Ray, by simp⟩

@[simp]
lemma validates_transport_iff : F.transport e ⊧ φ ↔ F ⊧ φ :=
  ⟨Validates.of_surjective_pMorphism (PMorphism.ofTransport F e) e.symm.surjective,
    Validates.of_surjective_pMorphism (PMorphism.toTransport F e) e.surjective⟩

@[simp]
lemma validateLogic_transport_iff : F.transport e ⊧ L ↔ F ⊧ L :=
  forall₂_congr fun _ _ => validates_transport_iff

abbrev ulift (F : Frame κ) : Frame (ULift.{u'} κ) := F.transport Equiv.ulift.symm

end Frame

end
