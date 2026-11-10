module

public import K4S4.Construction.BaseNaming

/-!
# The ladder and the coding formulas

The recursive names recover each ladder level up to a permutation of its columns.
The remaining names recover the chain and the optional coding points exactly.
-/

@[expose] public section

namespace Modal.K4S4.Construction

open Formula Model.World

variable {I : Set ℕ} {V : Point I → ℕ → Prop}

private lemma ladder_pair {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {n : ℕ} {x : Point I} :
    ((∀ k, x ≠ .ladder k n) ∧ rel x (.ladder a n) ∧ rel x (.ladder b n) ∧
      ¬rel x (.ladder c n)) ↔ x = .ladder (c + 1) (n + 1) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all;
  all_goals cases x <;> simp [rel, ladderRel] <;> omega;

private lemma all_ladder_no_next {n : ℕ} {x : Point I} :
    ((∀ k, rel x (.ladder k n)) ∧ ¬∃ k, rel x (.ladder k (n + 1))) ↔ x = .d n := by
  cases x <;> simp [rel, ladderRel, Fin.forall_fin_succ, Fin.exists_fin_succ];
  all_goals omega;

def nextPermutation (e : Fin 3 ≃ Fin 3) : Fin 3 ≃ Fin 3 :=
  (Equiv.addRight (2 : Fin 3)).trans <| e.trans <| Equiv.addRight (1 : Fin 3)

lemma ladder_names_succ {n : ℕ} {e : Fin 3 ≃ Fin 3}
    (h : ∀ k x, x ⊩[constructionModel V] nameLadder k n ↔ x = .ladder (e k) n) :
    ∀ k x, x ⊩[constructionModel V] nameLadder k (n + 1) ↔
      x = .ladder (nextPermutation e k) (n + 1) := by
  intro k x;
  have hτ := forces_tau_of_ladder_names h (x := x);
  have hd : ∀ j, (x ⊩[constructionModel V] ◇(nameLadder j n)) ↔ rel x (.ladder (e j) n) := by
    intro j;
    simp only [forces_dia, h, exists_eq_right, frame_rel];
  have h₁ : k ≠ k + 1 := by omega;
  have h₂ : k ≠ k + 2 := by omega;
  have h₃ : k + 1 ≠ k + 2 := by omega;
  change (x ⊩[constructionModel V] (∼tau n ⋏ ◇(nameLadder k n) ⋏
    ◇(nameLadder (k + 1) n) ⋏ ∼◇(nameLadder (k + 2) n))) ↔ _;
  rw [forces_and, forces_and, forces_and];
  simpa only [forces_neg, NotForces, hτ, not_exists, hd,
    nextPermutation, Equiv.trans_apply, Equiv.coe_addRight] using
    ladder_pair (I := I) (n := n) (x := x)
      (e.injective.ne h₁) (e.injective.ne h₂) (e.injective.ne h₃);

lemma ladder_names_of_base {e : Fin 3 ≃ Fin 3}
    (h : ∀ k x, x ⊩[constructionModel V] nameLadder k 0 ↔ x = .ladder (e k) 0) :
    ∀ n, ∃ f : Fin 3 ≃ Fin 3,
      ∀ k x, x ⊩[constructionModel V] nameLadder k n ↔ x = .ladder (f k) n := by
  intro n;
  induction n with
  | zero => exact ⟨e, h⟩;
  | succ n ih =>
    obtain ⟨f, hf⟩ := ih;
    exact ⟨nextPermutation f, ladder_names_succ hf⟩;

lemma nameD_of_ladder_names
    (h : ∀ n, ∃ e : Fin 3 ≃ Fin 3,
      ∀ k x, x ⊩[constructionModel V] nameLadder k n ↔ x = .ladder (e k) n)
    (n : ℕ) (x : Point I) : x ⊩[constructionModel V] nameD n ↔ x = .d n := by
  obtain ⟨e, he⟩ := h n;
  obtain ⟨f, hf⟩ := h (n + 1);
  have hd : ∀ j, (x ⊩[constructionModel V] ◇(nameLadder j n)) ↔ rel x (.ladder (e j) n) := by
    intro j;
    simp only [forces_dia, he, exists_eq_right, frame_rel];
  have hτ : (x ⊩[constructionModel V] ◇(tau (n + 1))) ↔ ∃ k, rel x (.ladder k (n + 1)) := by
    rw [forces_dia];
    constructor;
    · rintro ⟨y, hxy, hy⟩;
      obtain ⟨k, rfl⟩ := (forces_tau_of_ladder_names hf).mp hy;
      exact ⟨k, hxy⟩;
    · rintro ⟨k, hk⟩;
      exact ⟨.ladder k (n + 1), hk, (forces_tau_of_ladder_names hf).mpr ⟨k, rfl⟩⟩;
  have hall : (∀ k, rel x (.ladder (e k) n)) ↔ ∀ k, rel x (.ladder k n) :=
    e.forall_congr_right (q := fun k => rel x (.ladder k n));
  have hc := (and_congr hall (Iff.refl (¬∃ k, rel x (.ladder k (n + 1))))).trans
    (all_ladder_no_next (I := I) (n := n) (x := x));
  change (x ⊩[constructionModel V] (◇(nameLadder 0 n) ⋏ ◇(nameLadder 1 n) ⋏
    ◇(nameLadder 2 n) ⋏ ∼◇(tau (n + 1)))) ↔ _;
  rw [forces_and, forces_and, forces_and];
  simpa [forces_neg, NotForces, hd, hτ, Fin.forall_fin_succ, and_assoc] using hc;

private lemma forces_exactlyOne_iff (A : Fin 3 → Formula ℕ) (x : Point I) :
    x ⊩[constructionModel V] exactlyOne (A 0) (A 1) (A 2) ↔ ∃! k, x ⊩[constructionModel V] A k := by
  simp only [exactlyOne, forces_or, forces_and];
  simp [ExistsUnique, Fin.exists_fin_succ, Fin.forall_fin_succ];
  tauto;

private lemma coding_point {n : ℕ} {x : Point I} :
    (x ≠ .d n ∧ rel x (.d n) ∧ ∃! k, rel x (.ladder k (n + 1))) ↔
      ∃ h : n ∈ I, x = .e ⟨n, h⟩ := by
  cases x <;> simp [rel, ExistsUnique, Fin.exists_fin_succ, Fin.forall_fin_succ];
  omega;

lemma nameE_of_ladder_names
    (h : ∀ n, ∃ e : Fin 3 ≃ Fin 3,
      ∀ k x, x ⊩[constructionModel V] nameLadder k n ↔ x = .ladder (e k) n)
    (n : ℕ) (x : Point I) :
    x ⊩[constructionModel V] nameE n ↔ ∃ hn : n ∈ I, x = .e ⟨n, hn⟩ := by
  obtain ⟨e, he⟩ := h (n + 1);
  have hd := nameD_of_ladder_names h;
  have h₁ : ∀ j, (x ⊩[constructionModel V] ◇(nameLadder j (n + 1))) ↔
      rel x (.ladder (e j) (n + 1)) := by
    intro j;
    simp only [forces_dia, he, exists_eq_right, frame_rel];
  change (x ⊩[constructionModel V] (∼nameD n ⋏ ◇(nameD n) ⋏ exactlyOne
    (◇(nameLadder 0 (n + 1))) (◇(nameLadder 1 (n + 1))) (◇(nameLadder 2 (n + 1))))) ↔ _;
  rw [forces_and, forces_and];
  rw [forces_exactlyOne_iff (fun k => ◇(nameLadder k (n + 1))) x];
  have hU : (∃! k, rel x (.ladder (e k) (n + 1))) ↔
      ∃! k, rel x (.ladder k (n + 1)) :=
    e.existsUnique_congr_right (q := fun k => rel x (.ladder k (n + 1)));
  simpa only [forces_neg, NotForces, hd, forces_dia, exists_eq_right, frame_rel,
    h₁, hU] using
    (coding_point (I := I) (n := n) (x := x));

lemma nameY_of_names
    (hD : ∀ n x, x ⊩[constructionModel V] nameD n ↔ x = .d n)
    (hH : ∀ x, x ⊩[constructionModel V] nameH ↔ x = .h) (n : ℕ) (x : Point I) :
    x ⊩[constructionModel V] nameY n ↔ x = .y n := by
  cases n;
  all_goals simp only [nameY, forces_and];
  all_goals simp only [forces_neg, NotForces, forces_dia, hD, hH, exists_eq_right, frame_rel];
  all_goals cases x <;> simp [rel] <;> omega;

lemma nameR_of_names
    (h : ∃ e : Fin 3 ≃ Fin 3,
      ∀ k x, x ⊩[constructionModel V] nameLadder k 0 ↔ x = .ladder (e k) 0)
    (hH : ∀ x, x ⊩[constructionModel V] nameH ↔ x = .h)
    (hY : ∀ x, x ⊩[constructionModel V] nameY 0 ↔ x = .y 0) (x : Point I) :
    x ⊩[constructionModel V] nameR ↔ x = .r := by
  obtain ⟨e, he⟩ := h;
  simp only [nameR, forces_and, forces_dia, he, hH, hY, exists_eq_right, frame_rel];
  cases x <;> simp [rel];

end Modal.K4S4.Construction
