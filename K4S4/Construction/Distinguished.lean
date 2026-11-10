module

public import K4S4.Construction.Naming

/-!
# A distinguished admissible valuation

The distinguished valuation realizes the root and every coding point present in the frame.
-/

@[expose] public section

namespace Modal.K4S4.Construction

open Model.World

variable {I : Set ℕ}

/-- The three naming variables have the prescribed types at the terminals and minima,
and are false at every other point. -/
def distinguishedValuation : Point I → ℕ → Prop
  | .o, a => a < 3
  | .h, a => a < 2
  | .ladder k 0, a => a = k.val
  | _, _ => False

abbrev distinguishedModel (I : Set ℕ) : Model (Point I) ℕ :=
  constructionModel distinguishedValuation

private lemma distinguished_atom (x : Point I) (a : ℕ) :
    x ⊩[distinguishedModel I] #a ↔ distinguishedValuation x a := Iff.rfl

lemma distinguishedValuation_admissible :
    (generalFrame I).IsAdmissible distinguishedValuation :=
  fun _ => ⟨False, 0, fun _ _ => Iff.rfl⟩

private lemma distinguished_terminal :
    (.o : Point I) ⊩[distinguishedModel I] nameO ∧
      (.o' : Point I) ⊩[distinguishedModel I] nameO' := by
  constructor;
  · apply forces_box.mpr;
    intro x hx;
    cases x <;> simp_all [frame_rel, rel, terminalType, forces_and,
      distinguished_atom, distinguishedValuation];
  · apply forces_box.mpr;
    intro x hx;
    cases x <;> simp_all [frame_rel, rel, terminalType,
      NotForces, forces_imp, distinguished_atom, distinguishedValuation];

lemma distinguished_mu (x : Point I) :
    x ⊩[distinguishedModel I] mu ↔ x ≠ .o ∧ x ≠ .o' :=
  forces_mu_iff_of_terminal_witnesses ⟨.o, distinguished_terminal.1⟩
    ⟨.o', distinguished_terminal.2⟩

lemma distinguished_ladderType (k : Fin 3) (x : Point I) :
    x ⊩[distinguishedModel I] ladderType k ↔ x = .ladder k 0 := by
  cases x;
  case ladder l n =>
    fin_cases k <;> fin_cases l <;> cases n <;>
      simp [ladderType, forces_imp, NotForces, distinguished_atom, distinguishedValuation];
  all_goals fin_cases k <;>
    simp [ladderType, forces_imp, NotForces, distinguished_atom, distinguishedValuation];

lemma distinguished_markerType (x : Point I) :
    x ⊩[distinguishedModel I] markerType ↔ x = .h := by
  cases x;
  case ladder k n =>
    fin_cases k <;> cases n <;>
      simp [markerType, forces_imp, NotForces, distinguished_atom, distinguishedValuation];
  all_goals simp [markerType, forces_imp, NotForces, distinguished_atom, distinguishedValuation];

lemma distinguished_nameH (x : Point I) :
    x ⊩[distinguishedModel I] nameH ↔ x = .h := by
  simp only [nameH, forces_and, distinguished_markerType, distinguished_mu];
  constructor;
  · tauto;
  · rintro rfl;
    have h : (.h : Point I) ⊩[distinguishedModel I] □(mu 🡒 markerType) := by
      apply forces_box.mpr;
      intro y hy hmu;
      have hy' : y = .h := by
        have h₁ := (distinguished_mu y).mp hmu;
        cases y <;> simp_all [frame_rel, rel];
      exact (distinguished_markerType y).mpr hy';
    exact ⟨by simp, rfl, h⟩;

lemma distinguished_nameLadder_zero (k : Fin 3) (x : Point I) :
    x ⊩[distinguishedModel I] nameLadder k 0 ↔ x = .ladder k 0 := by
  simp only [nameLadder, forces_and, distinguished_ladderType, distinguished_mu];
  constructor;
  · tauto;
  · rintro rfl;
    have h : (.ladder k 0 : Point I) ⊩[distinguishedModel I] □(mu 🡒 ladderType k) := by
      apply forces_box.mpr;
      intro y hy hmu;
      have hy' : y = .ladder k 0 := by
        have h₁ := (distinguished_mu y).mp hmu;
        cases y <;> simp_all [frame_rel, rel, ladderRel];
      exact (distinguished_ladderType k y).mpr hy';
    exact ⟨by simp, rfl, h⟩;

lemma distinguished_ladder_names : ∀ n, ∃ e : Fin 3 ≃ Fin 3,
    ∀ k x, x ⊩[distinguishedModel I] nameLadder k n ↔ x = .ladder (e k) n :=
  ladder_names_of_base (e := Equiv.refl _) distinguished_nameLadder_zero

lemma distinguished_nameD (n : ℕ) (x : Point I) :
    x ⊩[distinguishedModel I] nameD n ↔ x = .d n :=
  nameD_of_ladder_names distinguished_ladder_names n x

lemma distinguished_nameE (n : ℕ) (x : Point I) :
    x ⊩[distinguishedModel I] nameE n ↔ ∃ hn : n ∈ I, x = .e ⟨n, hn⟩ :=
  nameE_of_ladder_names distinguished_ladder_names n x

lemma distinguished_nameY (n : ℕ) (x : Point I) :
    x ⊩[distinguishedModel I] nameY n ↔ x = .y n :=
  nameY_of_names distinguished_nameD distinguished_nameH n x

lemma distinguished_nameR (x : Point I) :
    x ⊩[distinguishedModel I] nameR ↔ x = .r :=
  nameR_of_names ⟨Equiv.refl _, distinguished_nameLadder_zero⟩
    distinguished_nameH (distinguished_nameY 0) x

lemma distinguished_refutes_chi {n : ℕ} (hn : n ∈ I) :
    (.r : Point I) ⊮[distinguishedModel I] chi n := by
  intro h;
  apply h <| (distinguished_nameR _).mpr rfl;
  exact forces_dia.mpr ⟨.e ⟨n, hn⟩, by simp [frame_rel, rel],
    (distinguished_nameE n _).mpr ⟨hn, rfl⟩⟩;

lemma frame_not_validates_chi {n : ℕ} (hn : n ∈ I) : frame I ⊭ chi n :=
  fun h => distinguished_refutes_chi hn <| h distinguishedValuation .r

lemma generalFrame_not_validates_chi {n : ℕ} (hn : n ∈ I) : generalFrame I ⊭ chi n :=
  fun h => distinguished_refutes_chi hn <| h distinguishedValuation
    distinguishedValuation_admissible .r

end Modal.K4S4.Construction
