module

public import K4S4.Construction.BasePoints

/-!
# Naming the four minimal nonterminal points

Under arbitrary valuations, witnesses for the four base names determine a permutation
of the four minimal nonterminal points.
-/

@[expose] public section

namespace Modal.K4S4.Construction

open Formula Model.World

variable {I : Set ℕ} {V : Point I → ℕ → Prop}

lemma forces_tau_iff {n : ℕ} {x : Point I} :
    x ⊩[constructionModel V] tau n ↔ ∃ k, x ⊩[constructionModel V] nameLadder k n := by
  simp [tau, forces_or, Fin.exists_fin_succ];

lemma forces_tau_of_ladder_names {n : ℕ} {e : Fin 3 ≃ Fin 3}
    (h : ∀ k x, x ⊩[constructionModel V] nameLadder k n ↔ x = .ladder (e k) n) {x : Point I} :
    x ⊩[constructionModel V] tau n ↔ ∃ k, x = .ladder k n := by
  rw [forces_tau_iff];
  constructor;
  · rintro ⟨k, hk⟩;
    exact ⟨e k, (h k x).mp hk⟩;
  · rintro ⟨k, hk⟩;
    use e.symm k;
    exact (h (e.symm k) x).mpr <| by simpa using hk;

lemma exists_base_names_of_forces_nameR {x : Point I} (hx : x ⊩[constructionModel V] nameR) :
    (∀ k, ∃ y, y ⊩[constructionModel V] nameLadder k 0) ∧
      (∃ y, y ⊩[constructionModel V] nameH) ∧ (∃ y, y ⊩[constructionModel V] nameD 0) := by
  simp only [nameR, forces_and, forces_dia] at hx;
  obtain ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩, ⟨c, _, hc⟩, ⟨q, _, hh⟩, y, _, hy⟩ := hx;
  simp only [nameY, forces_and, forces_dia] at hy;
  obtain ⟨_, ⟨d, _, hd⟩, _⟩ := hy;
  and_intros;
  · intro k;
    fin_cases k;
    · exact ⟨a, ha⟩;
    · exact ⟨b, hb⟩;
    · exact ⟨c, hc⟩;
  · exact ⟨q, hh⟩;
  · exact ⟨d, hd⟩;

private lemma terminal_reachable (x : Point I) :
    ∃ t, (t = .o ∨ t = .o') ∧ rel x t := by
  cases x;
  case o' => exact ⟨.o', Or.inr rfl, trivial⟩;
  all_goals exact ⟨.o, Or.inl rfl, trivial⟩;

private lemma sees_terminals {x : Point I} (hx : x ≠ .o ∧ x ≠ .o') :
    rel x .o ∧ rel x .o' := by
  cases x <;> simp_all [rel];

private lemma terminal_types_inconsistent {x : Point I} :
    ¬(x ⊩[constructionModel V] terminalType true ∧
      x ⊩[constructionModel V] terminalType false) := by
  intro h;
  have hp := (forces_and.mp h.1).1;
  have hn := (forces_and.mp h.2).1;
  exact hn hp;

private lemma terminal_support (hO : ∃ x, x ⊩[constructionModel V] nameO)
    (hO' : ∃ x, x ⊩[constructionModel V] nameO') {x : Point I} :
    (x ⊩[constructionModel V] nameO → x = .o ∨ x = .o') ∧
      (x ⊩[constructionModel V] nameO' → x = .o ∨ x = .o') := by
  constructor;
  · intro hx;
    by_contra! h;
    obtain ⟨y, hy⟩ := hO';
    obtain ⟨t, ht, hyt⟩ := terminal_reachable y;
    have hxt : rel x t := by
      rcases ht with rfl | rfl;
      · exact (sees_terminals h).1;
      · exact (sees_terminals h).2;
    exact terminal_types_inconsistent ⟨forces_box.mp hx _ hxt, forces_box.mp hy _ hyt⟩;
  · intro hx;
    by_contra! h;
    obtain ⟨y, hy⟩ := hO;
    obtain ⟨t, ht, hyt⟩ := terminal_reachable y;
    have hxt : rel x t := by
      rcases ht with rfl | rfl;
      · exact (sees_terminals h).1;
      · exact (sees_terminals h).2;
    exact terminal_types_inconsistent ⟨forces_box.mp hy _ hyt, forces_box.mp hx _ hxt⟩;

lemma forces_mu_iff_of_terminal_witnesses (hO : ∃ x, x ⊩[constructionModel V] nameO)
    (hO' : ∃ x, x ⊩[constructionModel V] nameO') {x : Point I} :
    x ⊩[constructionModel V] mu ↔ x ≠ .o ∧ x ≠ .o' := by
  constructor;
  · intro hx;
    rw [mu, forces_and, forces_dia, forces_dia] at hx;
    obtain ⟨⟨y, hy, hyO⟩, z, hz, hzO'⟩ := hx;
    constructor;
    · rintro rfl;
      have hy' : y = .o := by cases y <;> simp_all [frame_rel, rel];
      have hz' : z = .o := by cases z <;> simp_all [frame_rel, rel];
      subst hy' hz';
      exact terminal_types_inconsistent
        ⟨forces_box.mp hyO _ (Frame.rel_refl _), forces_box.mp hzO' _ (Frame.rel_refl _)⟩;
    · rintro rfl;
      have hy' : y = .o' := by cases y <;> simp_all [frame_rel, rel];
      have hz' : z = .o' := by cases z <;> simp_all [frame_rel, rel];
      subst hy' hz';
      exact terminal_types_inconsistent
        ⟨forces_box.mp hyO _ (Frame.rel_refl _), forces_box.mp hzO' _ (Frame.rel_refl _)⟩;
  · intro hx;
    obtain ⟨y, hy⟩ := hO;
    obtain ⟨z, hz⟩ := hO';
    have hxy : rel x y := by
      rcases (terminal_support ⟨y, hy⟩ ⟨z, hz⟩).1 hy with rfl | rfl;
      · exact (sees_terminals hx).1;
      · exact (sees_terminals hx).2;
    have hxz : rel x z := by
      rcases (terminal_support ⟨y, hy⟩ ⟨z, hz⟩).2 hz with rfl | rfl;
      · exact (sees_terminals hx).1;
      · exact (sees_terminals hx).2;
    exact forces_and.mpr ⟨forces_dia.mpr ⟨y, hxy, hy⟩, forces_dia.mpr ⟨z, hxz, hz⟩⟩;

def baseName : Fin 4 → Formula ℕ
  | 0 => nameLadder 0 0
  | 1 => nameLadder 1 0
  | 2 => nameLadder 2 0
  | _ => nameH

def baseType : Fin 4 → Formula ℕ
  | 0 => ladderType 0
  | 1 => ladderType 1
  | 2 => ladderType 2
  | _ => markerType

@[simp] lemma baseName_castSucc (k : Fin 3) : baseName k.castSucc = nameLadder k 0 := by
  fin_cases k <;> rfl;

@[simp] lemma baseName_three : baseName 3 = nameH := rfl

lemma forces_baseName_iff {k : Fin 4} {x : Point I} :
    x ⊩[constructionModel V] baseName k ↔ x ⊩[constructionModel V] mu ∧
      x ⊩[constructionModel V] baseType k ∧
      ∀ y, rel x y → y ⊩[constructionModel V] mu → y ⊩[constructionModel V] baseType k := by
  have h : baseName k = mu ⋏ baseType k ⋏ □(mu 🡒 baseType k) := by
    fin_cases k <;> rfl;
  rw [h, forces_and, forces_and, forces_box];
  rfl;

lemma baseType_eq_of_forces {k l : Fin 4} {x : Point I}
    (hk : x ⊩[constructionModel V] baseType k)
    (hl : x ⊩[constructionModel V] baseType l) : k = l := by
  fin_cases k <;> fin_cases l <;>
    simp_all [baseType, ladderType, markerType, NotForces, forces_imp];

lemma terminal_witnesses_of_base {x : Point I} (hx : x ⊩[constructionModel V] baseName 0) :
    (∃ y, y ⊩[constructionModel V] nameO) ∧ (∃ y, y ⊩[constructionModel V] nameO') := by
  have hm := (forces_baseName_iff.mp hx).1;
  obtain ⟨⟨y, _, hy⟩, z, _, hz⟩ := forces_and.mp hm;
  exact ⟨⟨y, hy⟩, ⟨z, hz⟩⟩;

lemma exists_base_permutation (hbase : ∀ k : Fin 4, ∃ x, x ⊩[constructionModel V] baseName k) :
    ∃ e : Fin 4 ≃ Fin 4, ∀ k x,
      x ⊩[constructionModel V] baseName k ↔ x = basePoint (e k) := by
  classical
  choose x hx using hbase;
  obtain ⟨hO, hO'⟩ := terminal_witnesses_of_base (hx 0);
  have hm : ∀ y, y ⊩[constructionModel V] mu ↔ y ≠ .o ∧ y ≠ .o' :=
    fun _ => forces_mu_iff_of_terminal_witnesses hO hO';
  have hex : ∀ k, ∃ j : Fin 4, rel (x k) (basePoint j) :=
    fun k => exists_basePoint <| (hm _).mp <| (forces_baseName_iff.mp <| hx k).1;
  choose j hj using hex;
  have ht : ∀ k, (basePoint (j k) : Point I) ⊩[constructionModel V] baseType k := fun k =>
    (forces_baseName_iff.mp <| hx k).2.2 _ (hj k) <|
      (hm _).mpr <| basePoint_nonterminal _;
  have hi : Function.Injective j := by
    intro k l h;
    apply baseType_eq_of_forces (ht k);
    simpa only [h] using ht l;
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective j ⟨hi, Finite.surjective_of_injective hi⟩;
  have hs : ∀ k y, y ⊩[constructionModel V] baseName k → y = basePoint (e k) := by
    intro k y hy;
    obtain ⟨hyμ, _, hy⟩ := forces_baseName_iff.mp hy;
    apply eq_basePoint_of_unique ((hm y).mp hyμ) (e k);
    intro l hyl;
    obtain ⟨m, rfl⟩ := e.surjective l;
    have hkm : k = m := baseType_eq_of_forces
      (hy _ hyl <| (hm _).mpr <| basePoint_nonterminal _) (ht m);
    exact congrArg e hkm.symm;
  use e;
  intro k y;
  constructor;
  · exact hs k y;
  · intro hy;
    simpa only [hy, hs k (x k) (hx k)] using hx k;

lemma ladder_base_names_of_base_permutation (e : Fin 4 ≃ Fin 4) (he : e 3 = 3)
    (hb : ∀ k x, x ⊩[constructionModel V] baseName k ↔ x = basePoint (e k)) :
    ∃ f : Fin 3 ≃ Fin 3,
      (∀ k x, x ⊩[constructionModel V] nameLadder k 0 ↔ x = .ladder (f k) 0) ∧
        ∀ x, x ⊩[constructionModel V] nameH ↔ x = .h := by
  have hlt : ∀ k : Fin 3, (e k.castSucc).val < 3 := by
    intro k;
    have hne : e k.castSucc ≠ 3 := he ▸ e.injective.ne k.castSucc_ne_last;
    omega;
  let f : Fin 3 → Fin 3 := fun k => ⟨(e k.castSucc).val, hlt k⟩;
  have hf : Function.Injective f := by
    intro k l h;
    exact Fin.castSucc_injective 3 <| e.injective <| Fin.ext <|
      congrArg (fun a : Fin 3 => a.val) h;
  let p : Fin 3 ≃ Fin 3 := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩;
  have hpoint : ∀ k : Fin 3, (basePoint (e k.castSucc) : Point I) = .ladder (p k) 0 := by
    intro k;
    change (if h : (e k.castSucc).val < 3 then
      Point.ladder ⟨(e k.castSucc).val, h⟩ 0 else .h) = .ladder (f k) 0;
    simp [hlt, f];
  use p;
  constructor;
  · intro k x;
    simpa only [baseName_castSucc, hpoint k] using hb k.castSucc x;
  · intro x;
    simpa only [baseName_three, he, basePoint_three] using hb 3 x;

end Modal.K4S4.Construction
