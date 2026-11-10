module

public import K4S4.Construction.Distinguished
public import K4S4.Construction.Marker

/-!
# Validity of the chain and coding axioms

The unrestricted naming lemma makes the chain axioms valid on the underlying Kripke
frames. The coding axiom at an index is valid exactly when that coding point is absent.
-/

@[expose] public section

namespace Modal.K4S4.Construction

open Formula Model.World

variable {I : Set ℕ} {V : Point I → ℕ → Prop}

lemma base_names_of_forces_nameR {x : Point I} (hx : x ⊩[constructionModel V] nameR) :
    ∃ e : Fin 3 ≃ Fin 3,
      (∀ k y, y ⊩[constructionModel V] nameLadder k 0 ↔ y = .ladder (e k) 0) ∧
        ∀ y, y ⊩[constructionModel V] nameH ↔ y = .h := by
  obtain ⟨hL, hH, hD⟩ := exists_base_names_of_forces_nameR hx;
  have hB : ∀ k : Fin 4, ∃ y, y ⊩[constructionModel V] baseName k := by
    intro k;
    fin_cases k;
    · exact hL 0;
    · exact hL 1;
    · exact hL 2;
    · exact hH;
  obtain ⟨e, he⟩ := exists_base_permutation hB;
  exact ladder_base_names_of_base_permutation e (base_permutation_fixes_three e he hD) he;

lemma forces_theta_of_names
    (hY : ∀ n x, x ⊩[constructionModel V] nameY n ↔ x = .y n)
    (n : ℕ) (x : Point I) : x ⊩[constructionModel V] theta n := by
  intro _;
  apply forces_box.mpr;
  intro y _ hy;
  obtain rfl := (hY n y).mp hy;
  apply forces_dia.mpr;
  use .y (n + 1);
  exact ⟨Nat.le_succ n, forces_and.mpr ⟨(hY (n + 1) _).mpr rfl, by
    rintro ⟨z, hz, hz'⟩;
    obtain rfl := (hY n z).mp hz';
    exact Nat.not_succ_le_self n hz⟩⟩;

lemma forces_chi_of_names
    (hE : ∀ n x, x ⊩[constructionModel V] nameE n ↔
      ∃ hn : n ∈ I, x = .e ⟨n, hn⟩)
    {n : ℕ} (hn : n ∉ I) (x : Point I) : x ⊩[constructionModel V] chi n := by
  intro _ hd;
  obtain ⟨y, _, hy⟩ := hd;
  obtain ⟨hn', _⟩ := (hE n y).mp hy;
  exact hn hn';

lemma frame_validates_theta (I : Set ℕ) (n : ℕ) : frame I ⊧ theta n := by
  intro V x hx;
  obtain ⟨e, hL, hH⟩ := base_names_of_forces_nameR hx;
  have hD := nameD_of_ladder_names <| ladder_names_of_base hL;
  have hY := nameY_of_names hD hH;
  exact forces_theta_of_names hY n x hx;

lemma frame_validates_chi_of_not_mem {n : ℕ} (hn : n ∉ I) : frame I ⊧ chi n := by
  intro V x hx;
  obtain ⟨e, hL, _⟩ := base_names_of_forces_nameR hx;
  have hE := nameE_of_ladder_names <| ladder_names_of_base hL;
  exact forces_chi_of_names hE hn x hx;

lemma frame_validates_chi {n : ℕ} : frame I ⊧ chi n ↔ n ∉ I :=
  ⟨fun h hn => frame_not_validates_chi hn h, frame_validates_chi_of_not_mem⟩

end Modal.K4S4.Construction
