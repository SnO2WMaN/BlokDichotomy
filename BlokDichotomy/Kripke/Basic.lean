module

public import BlokDichotomy.Formula.Substitution
public import BlokDichotomy.Logic.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Data.Countable.Defs

@[expose]
public section

variable {κ : Type u} {α β : Type v}

structure Frame (κ : Type u) where
  Rel'      : κ → κ → Prop
namespace Frame

variable {F : Frame κ}

abbrev World {_ : Frame κ} := κ

variable {x y : F.World}

abbrev Rel {F : Frame κ} : F.World → F.World → Prop := F.Rel'
infixl:60 " ≺ " => Rel

@[grind]
def RelItr : ℕ → F.World → F.World → Prop
| 0     => (· = ·)
| n + 1 => λ x z => ∃ y, (x ≺ y) ∧ (Frame.RelItr n y z)
notation x " ≺^[" n "] " y => RelItr n x y

@[simp, grind .] lemma relItr_zero_self : x ≺^[0] x := by tauto;
@[simp, grind =] lemma iff_relItr_zero : (x ≺^[0] y) ↔ x = y := by simp [RelItr]

@[grind =] lemma iff_relItr_succ : (x ≺^[n + 1] y) ↔ ∃ z, x ≺ z ∧ (z ≺^[n] y) := Iff.rfl

@[grind =]
lemma iff_relItr_succ' : (x ≺^[n + 1] y) ↔ ∃ z, (x ≺^[n] z) ∧ z ≺ y := by
  induction n generalizing x y <;> grind;

@[simp, grind =] lemma iff_relItr_one : (x ≺^[1] y) ↔ x ≺ y := by grind;

lemma iff_relItr_add {m : ℕ} : (x ≺^[n + m] y) ↔ ∃ z, (x ≺^[n] z) ∧ (z ≺^[m] y) := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih => rw [show n + 1 + m = (n + m) + 1 by omega]; grind;

@[grind →] lemma relItr_head (hxy : x ≺ y) (hyz : y ≺^[n] z) : x ≺^[n + 1] z := by grind;
@[grind →] lemma relItr_tail {z : F.World} (hxy : x ≺^[n] y) (hyz : y ≺ z) : x ≺^[n + 1] z := by grind;

lemma relItr_trans {m : ℕ} {z : F.World} (hxy : x ≺^[n] y) (hyz : y ≺^[m] z) : x ≺^[n + m] z :=
  iff_relItr_add.mpr ⟨y, hxy, hyz⟩

lemma exists_relItr_of_le (h : x ≺^[n] y) (hmn : m ≤ n) : ∃ z, x ≺^[m] z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn;
  obtain ⟨z, hz, -⟩ := iff_relItr_add.mp h;
  exact ⟨z, hz⟩;

lemma exists_relItr_of_lt (h : x ≺^[n] y) (hmn : m < n) : ∃ z, x ≺^[m] z :=
  exists_relItr_of_le h hmn.le

end Frame



structure Model (κ : Type u) (α : Type v) extends Frame κ where
  Val'      : κ → α → Prop

namespace Model

variable {M : Model κ α}

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

end Model


namespace Model.World

variable {M : Model κ α} {x y: M.World} {A B : Formula α}

@[grind =]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
| #a    => M.Val x a
| ⊥     => False
| A 🡒 B => Forces M x A → Forces M x B
| ◇A    => ∃ y : M.World, x ≺ y ∧ Forces _ y A
notation:80 x:50 " ⊩[" M "] " A:50 => Forces M x A
infix:50 " ⊩ " => Forces _

abbrev NotForces (M : Model κ α) (x : M.World) (A : Formula α) : Prop := ¬(x ⊩ A)
notation:80 x:50 " ⊮[" M "] " A:50 => NotForces M x A
infix:50 " ⊮ " => NotForces _

@[simp, grind .] lemma forces_top : x ⊩ ⊤ := by grind;
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ x ⊮ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_dia : x ⊩ ◇A ↔ ∃ y : M.World, x ≺ y ∧ y ⊩ A := by grind;

@[grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := by tauto;
@[grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by grind;
@[grind =] lemma forces_or  : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by grind;
@[grind =] lemma forces_iff : x ⊩ A 🡘 B ↔ (x ⊩ A ↔ x ⊩ B) := by grind;
@[grind =] lemma forces_box : x ⊩ □A ↔ ∀ y : M.World, x ≺ y → y ⊩ A := by grind;

@[grind =]
lemma forces_multidia : x ⊩ ◇^[n]A ↔ ∃ y : M.World, (x ≺^[n] y) ∧ y ⊩ A := by
  induction n generalizing x <;> grind [Frame.RelItr];

@[grind =]
lemma forces_multidox : x ⊩ □^[n]A ↔ ∀ y : M.World, (x ≺^[n] y) → y ⊩ A := by
  induction n generalizing x <;> grind [Frame.RelItr];

@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := by tauto;
@[grind =] lemma not_forces_and : x ⊮ A ⋏ B ↔ x ⊮ A ∨ x ⊮ B := by grind;
@[grind =] lemma not_forces_or  : x ⊮ A ⋎ B ↔ x ⊮ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_neg : x ⊮ ∼A ↔ x ⊩ A := by grind;
@[grind =] lemma not_forces_imp : x ⊮ A 🡒 B ↔ x ⊩ A ∧ x ⊮ B := by grind;
@[grind =] lemma not_forces_dia : x ⊮ ◇A ↔ ∀ y : M.World, x ≺ y → y ⊮ A := by grind;
@[grind =] lemma not_forces_box : x ⊮ □A ↔ ∃ y : M.World, x ≺ y ∧ y ⊮ A := by grind;
@[grind =] lemma not_forces_multidia : x ⊮ ◇^[n]A ↔ ∀ y : M.World, (x ≺^[n] y) → y ⊮ A := by grind;
@[grind =] lemma not_forces_multibox : x ⊮ □^[n]A ↔ ∃ y : M.World, (x ≺^[n] y) ∧ y ⊮ A := by grind;

@[grind =]
lemma forces_subst {M : Model κ β} {x : M.World} {A : Formula α} (σ : Formula.Substitution α β) :
  x ⊩[M] A⟦σ⟧ ↔ x ⊩[⟨M.toFrame, fun w a => w ⊩[M] σ a⟩] A := by
  induction A generalizing x <;> grind;

end Model.World


namespace Model

variable {M : Model κ α} {A : Formula α}

@[grind]
def Validates (M : Model κ α) (A : Formula α) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validates

end Model



namespace Frame

variable {F : Frame κ} {A : Formula α}

@[grind =]
def Validates (F : Frame κ) (A : Formula α) : Prop := ∀ V, (Model.mk F V) ⊧ A
infix:50 " ⊧ " => Frame.Validates

@[grind]
def ValidatesSet (F : Frame κ) (X : Set (Formula α)) : Prop := ∀ A ∈ X, F.Validates A
infix:50 " ⊧ " => Frame.ValidatesSet

abbrev ValidateLogic (F : Frame κ) (L : NormalLogic α) : Prop := F ⊧ L.carrier
infix:50 " ⊧ " => Frame.ValidateLogic

lemma mdp (hA : F ⊧ A) (hAB : F ⊧ A 🡒 B) : F ⊧ B := by
  intro V x;
  exact hAB V x $ hA V x;

lemma nec (h : F ⊧ A) : F ⊧ □A := by grind;

lemma subst {σ : Formula.Substitution α α} (h : F ⊧ A) : F ⊧ A⟦σ⟧ := by
  intro V x;
  exact Model.World.forces_subst σ |>.mpr $ h (fun w a => w ⊩[⟨F, V⟩] σ a) x

abbrev logic (F : Frame κ) : NormalLogic α where
  carrier := { A | F ⊧ A }
  mdp := mdp
  nec := nec
  subst := subst

section Soundness

variable {X : FormulaSet α} {L : NormalLogic α}

lemma validates_ofSet (h : F ⊧ X) : F ⊧ (NormalLogic.ofSet X) := by
  rintro A hA;
  induction hA with
  | mem h' => exact h _ h';
  | mdp _ _ ihA ihAB => exact mdp ihA ihAB;
  | nec _ ih => exact nec ih;
  | subst _ ih => exact subst ih;

lemma validates_axiomsK : F ⊧ (FormulaSet.axiomsK : FormulaSet α) := by
  rintro A hA V x;
  cases hA <;> grind;

lemma validates_logicK : F ⊧ (logicK : NormalLogic α) := validates_ofSet validates_axiomsK

lemma validates_oadd (hL : F ⊧ L) (hX : F ⊧ X) : F ⊧ (L.oadd X) := by
  apply validates_ofSet;
  rintro A (hA | hA);
  . exact hL _ hA;
  . exact hX _ hA;

lemma not_mem_bot_of_validates [Nonempty κ] (h : F ⊧ L) : (⊥ : Formula α) ∉ L :=
  fun hbot => h ⊥ hbot (fun _ _ => True) (Classical.arbitrary κ)

lemma consistent_of_validates [Nonempty κ] (h : F ⊧ L) : L.Consistent :=
  NormalLogic.consistent_iff.mpr ⟨⊥, not_mem_bot_of_validates h⟩

end Soundness

end Frame


namespace Logic

def Incomplete (L : NormalLogic α) : Prop := ∃ A : Formula α, (∀ F : Frame κ, F ⊧ L → F ⊧ A) ∧ (A ∉ L.carrier)

end Logic


abbrev farthest (n : ℕ) : Formula α := ◇^[n]⊤ ⋏ ∼◇^[(n + 1)]⊤

namespace Model.World

variable {M : Model κ α} {x : M.World} {n : ℕ}

@[grind =]
lemma forces_multidia_top : x ⊩ ◇^[n]⊤ ↔ ∃ y, x ≺^[n] y := by
  induction n generalizing x <;> grind;

@[grind =]
lemma forces_neg_multidia_top : x ⊩ ∼◇^[n]⊤ ↔ ∀ y, ¬x ≺^[n] y := by
  induction n generalizing x <;> grind;

@[grind =]
lemma iff_forces_farthest : x ⊩ farthest n ↔ (∃ y, x ≺^[n] y) ∧ (∀ y, ¬(x ≺^[n + 1] y)) := by
  rw [forces_and, forces_multidia_top, forces_neg_multidia_top];

lemma not_forces_farthest_of_ne (hnm : n ≠ m) (h : x ⊩ farthest n) : x ⊮ farthest m := by
  obtain ⟨⟨y, hy⟩, hn⟩ := iff_forces_farthest.mp h;
  rw [NotForces, iff_forces_farthest];
  push Not;
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hlt;
  . rintro ⟨z, hz⟩;
    obtain ⟨w, hw⟩ := Frame.exists_relItr_of_le hz hlt;
    exact (hn w hw).elim;
  . rintro -;
    exact Frame.exists_relItr_of_le hy hlt;

end Model.World

abbrev axiomMaks (n : ℕ) : Formula ℕ := □((farthest n) 🡒 #0) ⋎ □((farthest n) 🡒 ∼#0)

namespace Frame

open Model.World

lemma iff_validate_axiomMaks {F : Frame κ} : F ⊧ (axiomMaks n) ↔
  (∀ x : F.World, ∀ y z, x ≺ y → x ≺ z → ∀ V,
    y ⊩[(⟨F, V⟩ : Model κ ℕ)] ◇^[n]⊤ ⋏ ∼◇^[(n + 1)]⊤ →
    z ⊩[⟨F, V⟩] ◇^[n]⊤ ⋏ ∼◇^[(n + 1)]⊤ →
    y = z
  ) := by
  constructor;
  . contrapose!;
    rintro ⟨x, y, z, Rxy, Rxz, V, hy, hz, nyz⟩;
    rw [forces_and, forces_multidia_top, forces_neg_multidia_top] at hy hz;
    obtain ⟨⟨y', Ryy'⟩, hy⟩ := hy;
    obtain ⟨⟨z', Rzz'⟩, hz⟩ := hz;
    unfold axiomMaks Frame.Validates Model.Validates;
    push Not;
    use λ x a => x ≠ y, x;
    grind;
  . grind;

end Frame



abbrev logicMaks (𝔸 : Set ℕ) : NormalLogic ℕ := logicK.oadd $ 𝔸.image axiomMaks

abbrev logicVer : NormalLogic α := logicK.oadd { □A | A }


section Ver

abbrev Frame.deadEnd : Frame (Fin 1) := ⟨fun _ _ => False⟩

namespace Frame

lemma validates_box_deadEnd {A : Formula α} : deadEnd ⊧ (□A) := by
  intro V x;
  apply Model.World.forces_box.mpr;
  grind;

lemma validates_logicVer_deadEnd : deadEnd ⊧ (logicVer : NormalLogic α) := by
  apply validates_oadd validates_logicK;
  rintro A ⟨B, rfl⟩;
  exact validates_box_deadEnd;

end Frame


lemma not_mem_bot_logicVer : (⊥ : Formula α) ∉ logicVer :=
  Frame.not_mem_bot_of_validates Frame.validates_logicVer_deadEnd

lemma consistent_logicVer : (logicVer : NormalLogic α).Consistent :=
  Frame.consistent_of_validates Frame.validates_logicVer_deadEnd

end Ver


section Maks

variable {𝔸 𝔹 : Set ℕ}

lemma logicMaks_le_logicVer : logicMaks 𝔸 ≤ logicVer := by
  apply NormalLogic.oadd_le NormalLogic.le_oadd;
  rintro A ⟨n, -, rfl⟩;
  have h₁ : □(farthest n 🡒 ∼#0) ∈ (logicVer) := NormalLogic.mem_oadd ⟨_, rfl⟩;
  have h₂ : (□(farthest n 🡒 ∼#0) 🡒 (∼□(farthest n 🡒 #0) 🡒 □(farthest n 🡒 ∼#0))) ∈ (logicVer) :=
    NormalLogic.mem_oadd_of_mem $ NormalLogic.mem_ofSet $ FormulaSet.axiomsK.imply₁;
  exact NormalLogic.mem_mdp h₁ h₂;

lemma not_mem_bot_logicMaks : ⊥ ∉ logicMaks 𝔸 :=
  fun h => not_mem_bot_logicVer $ logicMaks_le_logicVer h

lemma consistent_logicMaks : (logicMaks 𝔸).Consistent :=
  NormalLogic.Consistent.of_le logicMaks_le_logicVer consistent_logicVer

@[gcongr]
lemma logicMaks_mono (h : 𝔸 ⊆ 𝔹) : logicMaks 𝔸 ≤ logicMaks 𝔹 :=
  NormalLogic.oadd_mono le_rfl $ Set.image_mono h

open Model.World


private abbrev frameMaks (n : ℕ) : Frame (Unit ⊕ (Fin 2 × ℕ)) := ⟨fun x y =>
  match x, y with
  | .inl (),     .inr (_, l) => l = 0
  | .inr (i, k), .inr (j, l) => i = j ∧ l = k + 1 ∧ l ≤ n
  | _, _ => False
⟩

namespace frameMaks

variable {n m j k : ℕ} {i : Fin 2}

private lemma iff_relItr_inr {x : (frameMaks n).World} (hk : k ≤ n) :
  ((.inr (i, k)) ≺^[j] x) ↔ (k + j ≤ n ∧ x = .inr (i, k + j)) := by
  induction j generalizing k with
  | zero => simp_all [eq_comm];
  | succ j ih =>
    rw [Frame.iff_relItr_succ];
    constructor;
    . rintro ⟨(⟨⟩ | ⟨i', k'⟩), hz, hzw⟩;
      . contradiction;
      . obtain ⟨rfl, rfl, hk'⟩ := hz;
        grind;
    . rintro ⟨h₁, rfl⟩;
      use .inr (i, k + 1);
      grind;

private lemma forces_farthest {V} : (Sum.inr (i, 0)) ⊩[(⟨frameMaks n, V⟩ : Model _ ℕ)] farthest n := by
  apply iff_forces_farthest.mpr;
  constructor;
  . refine ⟨.inr (i, n), ?_⟩;
    rw [iff_relItr_inr (by omega)];
    simp;
  . intro y;
    rw [iff_relItr_inr (by omega)];
    rintro ⟨h, -⟩;
    omega;

private lemma not_validates_axiomMaks : ¬(frameMaks n) ⊧ axiomMaks n := by
  apply Frame.iff_validate_axiomMaks.not.mpr;
  push Not;
  use .inl (), .inr (0, 0), .inr (1, 0);
  and_intros;
  . tauto;
  . tauto;
  . use λ _ _ => False;
    and_intros;
    . exact forces_farthest;
    . exact forces_farthest;
    . simp;

private lemma validates_axiomMaks_of_ne (hmn : m ≠ n) : (frameMaks n) ⊧ axiomMaks m := by
  apply Frame.iff_validate_axiomMaks.mpr;
  rintro (⟨⟩ | ⟨i, k⟩) y z hxy hxz V hy hz;
  . match y, z, hxy, hxz with
    | .inr (i, l), .inr (j, l'), hxy, hxz =>
      have hl : l = 0 := hxy;
      have hl' : l' = 0 := hxz;
      subst hl hl';
      exact absurd hy $ not_forces_farthest_of_ne (by omega) forces_farthest;
  . match y, z, hxy, hxz with
    | .inr (i', l), .inr (j', l'), hxy, hxz =>
      grind;

private lemma validates_logicMaks (hn : n ∉ 𝔹) : (frameMaks n) ⊧ logicMaks 𝔹 := by
  apply Frame.validates_oadd Frame.validates_logicK;
  rintro A ⟨m, hm, rfl⟩;
  exact validates_axiomMaks_of_ne $ by rintro rfl; exact hn hm;

end frameMaks


lemma of_logicMaks_le (h : logicMaks 𝔸 ≤ logicMaks 𝔹) : 𝔸 ⊆ 𝔹 := by
  contrapose! h;
  obtain ⟨n, hn𝔸, hn𝔹⟩ := Set.not_subset.mp h;
  apply NormalLogic.le_iff.not.mpr;
  push Not;
  use axiomMaks n;
  and_intros;
  exact NormalLogic.mem_oadd (by grind);
  . intro hmem;
    exact frameMaks.not_validates_axiomMaks $ frameMaks.validates_logicMaks hn𝔹 _ hmem;

theorem injective_logicMaks : Function.Injective logicMaks := by
  intro 𝔸 𝔹 h;
  exact Set.Subset.antisymm (of_logicMaks_le (by grind)) (of_logicMaks_le (by grind));


instance : Uncountable (Set ℕ) := uncountable_iff_forall_not_surjective.mpr Function.cantor_surjective

theorem uncoutable_consistent_normal_logics : Uncountable ({ L : NormalLogic ℕ // L.Consistent }) := by
  apply Function.Injective.uncountable (f := fun 𝔸 => ⟨logicMaks 𝔸, consistent_logicMaks⟩);
  intro 𝔸 𝔹 h;
  exact injective_logicMaks $ by simpa using h;

end Maks

end
