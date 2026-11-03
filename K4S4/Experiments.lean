module

public import BlokDichotomy.Modal.Blok
public import BlokDichotomy.Modal.Kripke.Correspondence

/-!
# Experiments with normal extensions of K4 and S4

Applications of existing degree bounds and frame correspondence results.
-/

@[expose] public section

namespace Modal.K4S4

variable {L : NormalLogic ℕ}

example [L.IsNExt 𝐊𝟒] : 1 ≤ L.degree.{0} 𝐊𝟒 (fun _ _ => True) :=
  NormalLogic.one_le_degree

example : L.degree.{0} 𝐊𝟒 (fun _ _ => True) ≤ Cardinal.continuum :=
  NormalLogic.degree_le_continuum

example [L.IsNExt 𝐒𝟒]
    (h : L.degree.{0} 𝐒𝟒 (fun _ _ => True) = Cardinal.continuum) :
    L.degree.{0} 𝐊𝟒 (fun _ _ => True) = Cardinal.continuum := by
  apply le_antisymm NormalLogic.degree_le_continuum;
  calc
    Cardinal.continuum = L.degree.{0} 𝐒𝟒 (fun _ _ => True) := h.symm
    _ ≤ L.degree.{0} 𝐊𝟒 (fun _ _ => True) := NormalLogic.degree_le_degree_of_isNExt

example {κ : Type} (F : Frame κ) [IsTrans _ F.Rel] (A : Formula ℕ) :
    F ⊧ □A 🡒 □□A :=
  Frame.validates_four_of_trans

end Modal.K4S4
