module

public import K4S4.Construction.Basic
public import BlokDichotomy.Modal.GeneralFrame.Basic
public import BlokDichotomy.ToMathlib.Order.Monotone.Basic

/-!
# Frames for the indexed construction above S4

The underlying partial orders and the general frames whose admissible sets have an
eventually constant trace on the ascending chain.
-/

@[expose] public section

namespace Modal.K4S4.Construction

variable {I : Set ℕ}

def ladderRel (k : Fin 3) (m : ℕ) (l : Fin 3) (n : ℕ) : Prop :=
  (k = l ∧ m = n) ∨ n + 2 ≤ m ∨ (m = n + 1 ∧ (l = k ∨ l = k + 1))

def rel : Point I → Point I → Prop
  | .r, _ => True
  | .o, .o => True
  | .o', .o' => True
  | .o, _ | .o', _ => False
  | _, .o | _, .o' => True
  | .h, .h => True
  | .ladder k m, .ladder l n => ladderRel k m l n
  | .d m, .d n => m = n
  | .d m, .ladder _ n => n ≤ m
  | .e m, .e n => m = n
  | .e m, .d n => m.1 = n
  | .e m, .ladder k n => n ≤ m.1 ∨ (k = 0 ∧ n = m.1 + 1)
  | .y m, .y n => m ≤ n
  | .y m, .d n => m ≤ n
  | .y _, .ladder _ _ => True
  | _, _ => False

def frame (I : Set ℕ) : Frame (Point I) := ⟨rel⟩

abbrev constructionModel (V : Point I → ℕ → Prop) : Model (Point I) ℕ := ⟨frame I, V⟩

@[simp] lemma frame_rel (x y : Point I) : (frame I).Rel x y ↔ rel x y := Iff.rfl

@[simp] lemma rel_refl (x : Point I) : rel x x := by
  cases x <;> simp [rel, ladderRel];

lemma rel_trans {x y z : Point I} (h₁ : rel x y) (h₂ : rel y z) : rel x z := by
  cases x <;> cases y <;> cases z <;> simp_all [rel, ladderRel] <;> omega;

lemma rel_antisymm {x y : Point I} (h₁ : rel x y) (h₂ : rel y x) : x = y := by
  cases x <;> cases y <;> simp_all [rel, ladderRel] <;> omega;

instance : Std.Refl (rel (I := I)) := ⟨rel_refl⟩

instance : Std.Refl (frame I).Rel := ⟨rel_refl⟩

instance : IsTrans _ (frame I).Rel := ⟨fun _ _ _ => rel_trans⟩

instance : IsTrans (Point I) rel := ⟨fun _ _ _ => rel_trans⟩

/-- Membership in `X` is eventually constant along the ascending chain. -/
def Admissible (X : Set (Point I)) : Prop :=
  ∃ b : Prop, ∃ N : ℕ, ∀ n ≥ N, (.y n ∈ X ↔ b)

lemma admissible_univ : Admissible (Set.univ : Set (Point I)) :=
  ⟨True, 0, fun _ _ => Iff.rfl⟩

lemma Admissible.inter {X Y : Set (Point I)} (hX : Admissible X) (hY : Admissible Y) :
    Admissible (X ∩ Y) := by
  obtain ⟨b, N, hN⟩ := hX;
  obtain ⟨c, M, hM⟩ := hY;
  exact ⟨b ∧ c, max N M, fun n hn => and_congr
    (hN n <| le_trans (le_max_left _ _) hn) (hM n <| le_trans (le_max_right _ _) hn)⟩;

lemma Admissible.compl {X : Set (Point I)} (hX : Admissible X) : Admissible Xᶜ := by
  obtain ⟨b, N, hN⟩ := hX;
  exact ⟨¬b, N, fun n hn => not_congr <| hN n hn⟩;

lemma admissible_diaSet (X : Set (Point I)) : Admissible ((frame I).diaSet X) := by
  classical
  by_cases h : ∀ n : ℕ, .y n ∈ (frame I).diaSet X;
  · exact ⟨True, 0, fun n _ => iff_true_intro <| h n⟩;
  · push Not at h;
    obtain ⟨N, hN⟩ := h;
    use False, N;
    intro n hn;
    constructor;
    · rintro ⟨z, hz, hX⟩;
      exact hN ⟨z, rel_trans (y := .y n) hn hz, hX⟩;
    · exact False.elim;

def generalFrame (I : Set ℕ) : GeneralFrame (Point I) where
  toFrame := frame I
  Adm := {X | Admissible X}
  univ_mem := admissible_univ
  inter_mem := Admissible.inter
  compl_mem := Admissible.compl
  diaSet_mem _ := admissible_diaSet _

lemma cone_finite {x : Point I} (hr : x ≠ .r) (hy : ∀ n, x ≠ .y n) :
    {z | rel x z}.Finite := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ z, rel x z →
      z = x ∨ z = .o ∨ z = .o' ∨
        (∃ k n, n ≤ M ∧ z = .ladder k n) ∨ (∃ n, n ≤ M ∧ z = .d n) := by
    cases x with
    | r => exact False.elim <| hr rfl;
    | y n => exact False.elim <| hy n rfl;
    | h => use 0; intro z hz; cases z <;> simp_all [rel];
    | o => use 0; intro z hz; cases z <;> simp_all [rel];
    | o' => use 0; intro z hz; cases z <;> simp_all [rel];
    | ladder k n =>
      use n;
      intro z hz;
      cases z <;> simp_all [rel, ladderRel]; omega;
    | d n => use n; intro z hz; cases z <;> simp_all [rel];
    | e n => use n.1 + 1; intro z hz; cases z <;> simp_all [rel]; omega;
  let S : Finset (Point I) := {x, .o, .o'} ∪
    ((Finset.univ.product (Finset.range (M + 1))).image fun p => .ladder p.1 p.2) ∪
      ((Finset.range (M + 1)).image Point.d);
  apply S.finite_toSet.subset;
  intro z hz;
  rcases hM z hz with rfl | rfl | rfl | ⟨k, n, hn, rfl⟩ | ⟨n, hn, rfl⟩ <;>
    simp [S, *];

lemma strict_chain_tail_y {u : ℕ → Point I} (hR : ∀ n, rel (u n) (u (n + 1)))
    (hs : ∀ n, ¬rel (u (n + 1)) (u n)) (i : ℕ) : ∃ k, u (i + 1) = .y k := by
  have hi : Function.Injective u := injective_of_forall_rel_succ hR hs;
  have hchain : ∀ n, rel (u (i + 1)) (u (i + 1 + n)) :=
    fun n => Nat.rel_of_forall_rel_succ_of_le rel hR <| Nat.le_add_right _ n;
  have hinf : {z | rel (u (i + 1)) z}.Infinite :=
    Set.infinite_of_injective_forall_mem (fun _ _ h => Nat.add_left_cancel <| hi h) hchain;
  have hr : u (i + 1) ≠ .r := by
    intro h;
    apply hs i;
    simp [h, rel];
  by_contra h;
  push Not at h;
  exact (cone_finite hr h).not_infinite hinf;

open Model.World

lemma sigma_chain {V : Point I → ℕ → Prop} {x : Point I}
    (hx : x ⊮[(⟨frame I, V⟩ : Model _ ℕ)] sigma) :
    ∃ u : ℕ → Point I, (∀ n, rel (u n) (u (n + 1))) ∧
      (∀ n, ¬rel (u (n + 1)) (u n)) ∧
      ∀ n, V (u n) 3 ↔ ¬V (u (n + 1)) 3 := by
  classical
  obtain ⟨hx₀, hx₁⟩ := forces_and.mp <| not_forces_neg.mp hx;
  obtain ⟨h₀, h₁⟩ := forces_and.mp hx₁;
  have hb₀ := (forces_and.mp h₀).2;
  have hb₁ := (forces_and.mp h₁).2;
  obtain ⟨u, _, hu⟩ := exists_seq_of_forall_exists_rel
    (r := fun w v => rel w v ∧ ¬rel v w ∧ (V w 3 ↔ ¬V v 3))
    (P := fun _ w => rel x w ∧
      (w ⊩[(⟨frame I, V⟩ : Model _ ℕ)] #3 ∨
        w ⊩[(⟨frame I, V⟩ : Model _ ℕ)] (∼#3 ⋏ #4)))
    ⟨rel_refl x, Or.inl hx₀⟩ <| by
      intro n w hw;
      by_cases hw₀ : V w 3;
      · obtain ⟨v, hwv, hv⟩ := forces_dia.mp <| (forces_box.mp hb₀ w hw.1) hw₀;
        have hv₀ : ¬V v 3 := (forces_and.mp hv).1;
        have hn : ¬rel v w := by
          intro hvw;
          obtain rfl := rel_antisymm hwv hvw;
          exact hv₀ hw₀;
        exact ⟨v, ⟨hwv, hn, ⟨fun _ => hv₀, fun _ => hw₀⟩⟩,
          rel_trans hw.1 hwv, Or.inr hv⟩;
      · have hw₁ : w ⊩[(⟨frame I, V⟩ : Model _ ℕ)] (∼#3 ⋏ #4) := by
          rcases hw.2 with h | h;
          · exact False.elim <| hw₀ h;
          · exact h;
        obtain ⟨v, hwv, hv⟩ := forces_dia.mp <| (forces_box.mp hb₁ w hw.1) hw₁;
        have hv₀ : V v 3 := hv;
        have hn : ¬rel v w := by
          intro hvw;
          obtain rfl := rel_antisymm hwv hvw;
          exact hw₀ hv₀;
        exact ⟨v, ⟨hwv, hn, ⟨fun h => False.elim <| hw₀ h,
          fun h => False.elim <| h hv₀⟩⟩, rel_trans hw.1 hwv, Or.inl hv⟩;
  exact ⟨u, fun n => (hu n).2.1, fun n => (hu n).2.2.1, fun n => (hu n).2.2.2⟩;

theorem generalFrame_validates_sigma : generalFrame I ⊧ sigma := by
  intro V hV x;
  by_contra hx;
  obtain ⟨u, hR, hs, hu⟩ := sigma_chain hx;
  choose k hk using strict_chain_tail_y hR hs;
  have hmono : StrictMono k := by
    apply strictMono_nat_of_lt_succ;
    intro n;
    simpa [hk, rel] using hs (n + 1);
  obtain ⟨b, N, hN⟩ := hV 3;
  have h₁ : V (u (N + 1)) 3 ↔ b := by simpa [hk] using hN (k N) (hmono.id_le N);
  have h₂ : V (u (N + 1 + 1)) 3 ↔ b := by
    simpa [hk] using hN (k (N + 1)) (le_trans (Nat.le_succ N) <| hmono.id_le (N + 1));
  have h₃ := hu (N + 1);
  tauto;

end Modal.K4S4.Construction
