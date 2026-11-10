module

public import K4S4.Construction.BaseNaming

/-!
# Identifying the isolated minimal point
-/

@[expose] public section

namespace Modal.K4S4.Construction

open Formula Model.World

variable {I : Set ℕ} {V : Point I → ℕ → Prop}

private lemma ladder_ne_basePoint (k : Fin 3) (j : Fin 4) :
    (Point.ladder k 1 : Point I) ≠ basePoint j := by
  unfold basePoint;
  split <;> simp;

private lemma rel_h_basePoint_iff (j : Fin 4) :
    rel (Point.h : Point I) (basePoint j) ↔ j = 3 := by
  unfold basePoint;
  split <;> simp_all [rel] <;> omega;

private lemma root_of_sees_base (e : Fin 4 ≃ Fin 4) (hne : e 3 ≠ 3) {x : Point I}
    (h : ∀ k : Fin 3, rel x (basePoint (e k.castSucc))) : x = .r := by
  obtain ⟨l, hl⟩ := e.surjective 3;
  have hl₁ : l.val < 3 := by
    have : l ≠ 3 := fun h => hne <| h ▸ hl;
    omega;
  let j : Fin 3 := ⟨l.val, hl₁⟩;
  have hj : j.castSucc = l := by ext; rfl;
  have hh : rel x .h := by simpa only [hj, hl, basePoint_three] using h j;
  have hx : x = .r ∨ x = .h := by cases x <;> simp_all [rel];
  rcases hx with hx | rfl;
  · exact hx;
  · have h₀ := (rel_h_basePoint_iff (e 0)).mp <| h 0;
    have h₁ := (rel_h_basePoint_iff (e 1)).mp <| h 1;
    have : (0 : Fin 4) = 1 := e.injective <| h₀.trans h₁.symm;
    exact False.elim <| by have := congrArg Fin.val this; omega;

private lemma exists_tau_one_of_base_permutation (e : Fin 4 ≃ Fin 4)
    (h : ∀ k x, x ⊩[constructionModel V] baseName k ↔ x = basePoint (e k))
    (hne : e 3 ≠ 3) : ∃ x, x ⊩[constructionModel V] tau 1 := by
  obtain ⟨l, hl⟩ := e.surjective 3;
  have hl₁ : l.val < 3 := by
    have : l ≠ 3 := fun h => hne <| h ▸ hl;
    omega;
  let j : Fin 3 := ⟨l.val, hl₁⟩;
  have hj : e j.castSucc = 3 := by simpa only [j, Fin.castSucc_mk] using hl;
  let k : Fin 3 := j + 1;
  have hkj : k ≠ j := by dsimp [k]; omega;
  have hkj' : k + 1 ≠ j := by dsimp [k]; omega;
  have hkj'' : k + 2 = j := by dsimp [k]; omega;
  have ha : e k.castSucc ≠ 3 := by
    intro h₁;
    exact hkj <| Fin.castSucc_injective 3 <| e.injective <| h₁.trans hj.symm;
  have hb : e (k + 1).castSucc ≠ 3 := by
    intro h₁;
    exact hkj' <| Fin.castSucc_injective 3 <| e.injective <| h₁.trans hj.symm;
  have hab : e k.castSucc ≠ e (k + 1).castSucc := by
    apply e.injective.ne;
    apply (Fin.castSucc_injective 3).ne;
    omega;
  obtain ⟨c, hc₁, hc₂⟩ := exists_ladder_succ_sees_base_pair (I := I) ha hb hab;
  have hL : ∀ m x, x ⊩[constructionModel V] nameLadder m 0 ↔
      x = basePoint (e m.castSucc) := fun m x => by
    simpa only [baseName_castSucc] using h m.castSucc x;
  have hC : basePoint (I := I) (e (k + 2).castSucc) = .h := by
    simp only [hkj'', hj, basePoint_three];
  have hn : (Point.ladder c 1) ⊩[constructionModel V] nameLadder k 1 := by
    change (Point.ladder c 1) ⊩[constructionModel V]
      (∼tau 0 ⋏ ◇(nameLadder k 0) ⋏ ◇(nameLadder (k + 1) 0) ⋏ ∼◇(nameLadder (k + 2) 0));
    simp only [forces_and];
    simp only [forces_neg, NotForces, tau, forces_or, hL, forces_dia,
      exists_eq_right, frame_rel, hC];
    exact ⟨by simp [ladder_ne_basePoint], hc₁, hc₂, by simp [rel]⟩;
  exact ⟨.ladder c 1, forces_tau_iff.mpr ⟨k, hn⟩⟩;

lemma base_permutation_fixes_three (e : Fin 4 ≃ Fin 4)
    (h : ∀ k x, x ⊩[constructionModel V] baseName k ↔ x = basePoint (e k))
    (hd : ∃ x, x ⊩[constructionModel V] nameD 0) : e 3 = 3 := by
  by_contra hne;
  obtain ⟨x, hx⟩ := hd;
  have hL : ∀ k z, z ⊩[constructionModel V] nameLadder k 0 ↔
      z = basePoint (e k.castSucc) := fun k z => by
    simpa only [baseName_castSucc] using h k.castSucc z;
  change x ⊩[constructionModel V] (◇(nameLadder 0 0) ⋏ ◇(nameLadder 1 0) ⋏
    ◇(nameLadder 2 0) ⋏ ∼◇(tau 1)) at hx;
  simp only [forces_and] at hx;
  simp only [forces_dia, hL, exists_eq_right, forces_neg, NotForces, frame_rel] at hx;
  have hroot : x = .r := root_of_sees_base e hne <| by
    simpa [Fin.forall_fin_succ] using ⟨hx.1, hx.2.1, hx.2.2.1⟩;
  obtain ⟨y, hy⟩ := exists_tau_one_of_base_permutation e h hne;
  exact hx.2.2.2 ⟨y, by simp [hroot, rel], hy⟩;

end Modal.K4S4.Construction
