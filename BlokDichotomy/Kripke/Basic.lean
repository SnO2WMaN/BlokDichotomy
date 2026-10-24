module

public import BlokDichotomy.Formula
public import BlokDichotomy.Logic.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Basic.Countable.Defs

/-!
# Kripke frames and models

Kripke frames and models, the forcing relation `x ⊩[M] φ`, validity `⊧` in models and frames,
and iterated accessibility `x ≺^[n] y`.
-/

@[expose]
public section

universe u v

variable {κ : Type u} {α β : Type v}

structure Frame (κ : Type u) where
  Rel' : κ → κ → Prop
namespace Frame

variable {F : Frame κ}

abbrev World (_ : Frame κ) := κ

variable {x y z : F.World} {n m : ℕ}

abbrev Rel {F : Frame κ} : F.World → F.World → Prop := F.Rel'
infixl:60 " ≺ " => Rel

abbrev NotRel {F : Frame κ} (x y : F.World) : Prop := ¬(x ≺ y)
infixl:60 " ⊀ " => NotRel

@[grind]
def RelItr : ℕ → F.World → F.World → Prop
| 0     => (· = ·)
| n + 1 => fun x z => ∃ y, (x ≺ y) ∧ (Frame.RelItr n y z)
notation x " ≺^[" n "] " y => RelItr n x y

abbrev NotRelItr {F : Frame κ} (n : ℕ) (x y : F.World) : Prop := ¬(x ≺^[n] y)
notation x:50 " ⊀^[" n "] " y:50 => NotRelItr n x y

@[simp, grind .] lemma relItr_zero_self : x ≺^[0] x := by tauto;
@[simp, grind =] lemma iff_relItr_zero : (x ≺^[0] y) ↔ x = y := by simp [RelItr]

@[grind =] lemma iff_relItr_succ : (x ≺^[n + 1] y) ↔ ∃ z, x ≺ z ∧ (z ≺^[n] y) := Iff.rfl

@[grind =]
lemma iff_relItr_succ' : (x ≺^[n + 1] y) ↔ ∃ z, (x ≺^[n] z) ∧ z ≺ y := by
  induction n generalizing x y <;> grind;

@[simp, grind =] lemma iff_relItr_one : (x ≺^[1] y) ↔ x ≺ y := by grind;

lemma iff_relItr_add : (x ≺^[n + m] y) ↔ ∃ z, (x ≺^[n] z) ∧ (z ≺^[m] y) := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih => rw [show n + 1 + m = (n + m) + 1 by omega]; grind;

@[grind →] lemma relItr_head (Rxy : x ≺ y) (Ryz : y ≺^[n] z) : x ≺^[n + 1] z := by grind;
@[grind →] lemma relItr_tail (Rxy : x ≺^[n] y) (Ryz : y ≺ z) : x ≺^[n + 1] z := by grind;

lemma relItr_trans (Rxy : x ≺^[n] y) (Ryz : y ≺^[m] z) : x ≺^[n + m] z :=
  iff_relItr_add.mpr ⟨y, Rxy, Ryz⟩

lemma exists_relItr_of_le (Rxy : x ≺^[n] y) (hmn : m ≤ n) : ∃ z, x ≺^[m] z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn;
  obtain ⟨z, Rxz, -⟩ := iff_relItr_add.mp Rxy;
  exact ⟨z, Rxz⟩;

lemma exists_relItr_of_lt (Rxy : x ≺^[n] y) (hmn : m < n) : ∃ z, x ≺^[m] z :=
  exists_relItr_of_le Rxy hmn.le

/-- `x ≺^+ y`: `y` is reachable from `x` in a positive number of steps. -/
def TransRel (x y : F.World) : Prop := ∃ n, 0 < n ∧ x ≺^[n] y
notation x " ≺^+ " y => TransRel x y

/-- `x ≺^* y`: `y` is reachable from `x` in some number of steps. -/
def ReflTransRel (x y : F.World) : Prop := ∃ n, x ≺^[n] y
notation x " ≺^* " y => ReflTransRel x y

lemma TransRel.reflTransRel (h : x ≺^+ y) : x ≺^* y := by
  obtain ⟨n, -, h⟩ := h;
  exact ⟨n, h⟩

lemma reflTransRel_of_relItr (Rxy : x ≺^[n] y) : x ≺^* y := ⟨n, Rxy⟩

lemma transRel_of_relItr (hn : 0 < n) (Rxy : x ≺^[n] y) : x ≺^+ y := ⟨n, hn, Rxy⟩

@[simp, grind .] lemma reflTransRel_refl (x : F.World) : x ≺^* x := ⟨0, relItr_zero_self⟩

lemma reflTransRel_of_rel (Rxy : x ≺ y) : x ≺^* y := ⟨1, iff_relItr_one.mpr Rxy⟩

lemma transRel_of_rel (Rxy : x ≺ y) : x ≺^+ y := ⟨1, Nat.one_pos, iff_relItr_one.mpr Rxy⟩

lemma reflTransRel_trans (Rxy : x ≺^* y) (Ryz : y ≺^* z) : x ≺^* z := by
  obtain ⟨n, hn⟩ := Rxy;
  obtain ⟨m, hm⟩ := Ryz;
  exact ⟨n + m, relItr_trans hn hm⟩

lemma ReflTransRel.tail (Rxy : x ≺^* y) (Ryz : y ≺ z) : x ≺^* z :=
  reflTransRel_trans Rxy (reflTransRel_of_rel Ryz)

@[simp, grind .] lemma rel_refl [Std.Refl F.Rel'] (x : F.World) : x ≺ x := refl x

@[grind →]
lemma rel_trans [IsTrans _ F.Rel'] (Rxy : x ≺ y) (Ryz : y ≺ z) : x ≺ z :=
  _root_.trans (r := F.Rel') Rxy Ryz

end Frame



structure Model (κ : Type u) (α : Type v) extends Frame κ where
  Val' : κ → α → Prop

namespace Model

variable {M : Model κ α}

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

end Model



/-- The formula true exactly at the points with a path of length `n` but none of length `n + 1`. -/
abbrev farthest (n : ℕ) : Formula α := ◇^[n]⊤ ⋏ ∼◇^[(n + 1)]⊤

/-- The one-point irreflexive frame. -/
abbrev deadEnd : Frame (Fin 1) := ⟨fun _ _ => False⟩

/-- The one-point reflexive frame. -/
abbrev reflPoint : Frame (Fin 1) := ⟨fun _ _ => True⟩


namespace Model.World

variable {M : Model κ α} {x y : M.World} {φ ψ : Formula α} {n : ℕ} {l : List (Formula α)}

@[grind =]
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
| #a    => M.Val x a
| ⊥     => False
| φ 🡒 ψ => Forces M x φ → Forces M x ψ
| ◇φ    => ∃ y : M.World, x ≺ y ∧ Forces _ y φ
notation:80 x:50 " ⊩[" M "] " φ:50 => Forces M x φ
infix:50 " ⊩ " => Forces _

abbrev NotForces (M : Model κ α) (x : M.World) (φ : Formula α) : Prop := ¬(x ⊩ φ)
notation:80 x:50 " ⊮[" M "] " φ:50 => NotForces M x φ
infix:50 " ⊮ " => NotForces _

@[simp, grind .] lemma forces_top : x ⊩ ⊤ := by grind;
@[grind =] lemma forces_imp : x ⊩ φ 🡒 ψ ↔ x ⊮ φ ∨ x ⊩ ψ := by grind;
@[grind =] lemma forces_dia : x ⊩ ◇φ ↔ ∃ y : M.World, x ≺ y ∧ y ⊩ φ := by grind;
@[grind =] lemma forces_neg : x ⊩ ∼φ ↔ x ⊮ φ := by tauto;
@[grind =] lemma forces_and : x ⊩ φ ⋏ ψ ↔ x ⊩ φ ∧ x ⊩ ψ := by grind;
@[grind =] lemma forces_or : x ⊩ φ ⋎ ψ ↔ x ⊩ φ ∨ x ⊩ ψ := by grind;
@[grind =] lemma forces_iff : x ⊩ φ 🡘 ψ ↔ (x ⊩ φ ↔ x ⊩ ψ) := by grind;
@[grind =] lemma forces_box : x ⊩ □φ ↔ ∀ y : M.World, x ≺ y → y ⊩ φ := by grind;

@[grind =]
lemma forces_multidia : x ⊩ ◇^[n]φ ↔ ∃ y : M.World, (x ≺^[n] y) ∧ y ⊩ φ := by
  induction n generalizing x <;> grind [Frame.RelItr];

@[grind =]
lemma forces_multidox : x ⊩ □^[n]φ ↔ ∀ y : M.World, (x ≺^[n] y) → y ⊩ φ := by
  induction n generalizing x <;> grind [Frame.RelItr];

@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := by tauto;
@[grind =] lemma not_forces_and : x ⊮ φ ⋏ ψ ↔ x ⊮ φ ∨ x ⊮ ψ := by grind;
@[grind =] lemma not_forces_or : x ⊮ φ ⋎ ψ ↔ x ⊮ φ ∧ x ⊮ ψ := by grind;
@[grind =] lemma not_forces_neg : x ⊮ ∼φ ↔ x ⊩ φ := by grind;
@[grind =] lemma not_forces_imp : x ⊮ φ 🡒 ψ ↔ x ⊩ φ ∧ x ⊮ ψ := by grind;
@[grind =] lemma not_forces_dia : x ⊮ ◇φ ↔ ∀ y : M.World, x ≺ y → y ⊮ φ := by grind;
@[grind =] lemma not_forces_box : x ⊮ □φ ↔ ∃ y : M.World, x ≺ y ∧ y ⊮ φ := by grind;
@[grind =] lemma not_forces_multidia : x ⊮ ◇^[n]φ ↔ ∀ y : M.World, (x ≺^[n] y) → y ⊮ φ := by grind;
@[grind =] lemma not_forces_multibox : x ⊮ □^[n]φ ↔ ∃ y : M.World, (x ≺^[n] y) ∧ y ⊮ φ := by grind;

@[simp, grind =]
lemma forces_conj : x ⊩ ⋀l ↔ ∀ φ ∈ l, x ⊩ φ := by
  induction l using List.induction_with_singleton with
  | nil => simp
  | singleton => simp
  | cons a l hl ih => simp [Formula.conj_cons_of_ne_nil hl, forces_and, ih]

@[simp, grind =]
lemma forces_disj : x ⊩ ⋁l ↔ ∃ φ ∈ l, x ⊩ φ := by
  induction l using List.induction_with_singleton with
  | nil => simp
  | singleton => simp
  | cons a l hl ih => simp [Formula.disj_cons_of_ne_nil hl, forces_or, ih]

/-- Two worlds with the same true variables and the same successors force the same formulas. -/
lemma forces_iff_of_same_succ (hval : ∀ a, M.Val x a ↔ M.Val y a)
    (hsucc : ∀ z, x ≺ z ↔ y ≺ z) : x ⊩ φ ↔ y ⊩ φ := by
  induction φ with
  | falsum => exact Iff.rfl;
  | atom a => exact hval a;
  | imp φ ψ ihφ ihψ => rw [forces_imp, forces_imp, NotForces, NotForces, ihφ, ihψ];
  | dia φ _ => simp only [forces_dia, hsucc];

/-- Truth of a formula depends only on the values of its variables. -/
lemma forces_congr_of_atoms [DecidableEq α] {V : M.World → α → Prop}
    (h : ∀ a ∈ φ.atoms, ∀ w, M.Val w a ↔ V w a) : x ⊩[M] φ ↔ x ⊩[⟨M.toFrame, V⟩] φ := by
  induction φ generalizing x with
  | falsum => exact Iff.rfl;
  | atom a => exact h a (by simp) x;
  | imp φ ψ ihφ ihψ =>
    rw [forces_imp, forces_imp, NotForces, NotForces,
      ihφ fun a ha => h a <| by simp [ha], ihψ fun a ha => h a <| by simp [ha]];
  | dia φ ih =>
    rw [forces_dia, forces_dia];
    exact exists_congr fun y => and_congr_right fun _ => ih h;

open Formula in
lemma forces_boxLe : x ⊩ □^≤[n]φ ↔ ∀ i ≤ n, ∀ y, (x ≺^[i] y) → y ⊩ φ := by
  induction n generalizing x with
  | zero => simp [boxLe];
  | succ n ih =>
    simp only [boxLe, forces_and, forces_box, ih];
    constructor;
    · rintro ⟨hx, h⟩ (_ | i) hi y Rxy;
      · rwa [Frame.iff_relItr_zero.mp Rxy] at hx;
      · obtain ⟨z, Rxz, Rzy⟩ := Rxy;
        exact h z Rxz i (by omega) y Rzy;
    · intro h;
      exact ⟨h 0 (by omega) x rfl, fun z Rxz i hi y Rzy => h (i + 1) (by omega) y ⟨z, Rxz, Rzy⟩⟩;

open Formula in
lemma forces_diaLe : x ⊩ ◇^≤[n]φ ↔ ∃ i ≤ n, ∃ y, (x ≺^[i] y) ∧ y ⊩ φ := by
  induction n generalizing x with
  | zero => simp [diaLe];
  | succ n ih =>
    simp only [diaLe, forces_or, forces_dia, ih];
    constructor;
    · rintro (hx | ⟨z, Rxz, i, hi, y, Rzy, hy⟩);
      · exact ⟨0, by omega, x, rfl, hx⟩;
      · exact ⟨i + 1, by omega, y, ⟨z, Rxz, Rzy⟩, hy⟩;
    · rintro ⟨(_ | i), hi, y, Rxy, hyA⟩;
      · rw [← Frame.iff_relItr_zero.mp Rxy] at hyA;
        exact Or.inl hyA;
      · obtain ⟨z, Rxz, Rzy⟩ := Rxy;
        exact Or.inr ⟨z, Rxz, i, by omega, y, Rzy, hyA⟩;

@[grind =]
lemma forces_multidia_top : x ⊩ ◇^[n]⊤ ↔ ∃ y, x ≺^[n] y := by
  induction n generalizing x <;> grind;

@[grind =]
lemma forces_neg_multidia_top : x ⊩ ∼◇^[n]⊤ ↔ ∀ y, x ⊀^[n] y := by
  induction n generalizing x <;> grind;

@[grind =]
lemma iff_forces_farthest : x ⊩ farthest n ↔ (∃ y, x ≺^[n] y) ∧ (∀ y, x ⊀^[n + 1] y) := by
  rw [forces_and, forces_multidia_top, forces_neg_multidia_top];

lemma not_forces_farthest_of_ne {m : ℕ} (hnm : n ≠ m) (h : x ⊩ farthest n) : x ⊮ farthest m := by
  obtain ⟨⟨y, Rxy⟩, hn⟩ := iff_forces_farthest.mp h;
  rw [NotForces, iff_forces_farthest];
  push Not;
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hlt;
  · rintro ⟨z, Rxz⟩;
    obtain ⟨w, Rxw⟩ := Frame.exists_relItr_of_le Rxz hlt;
    exact (hn w Rxw).elim;
  · rintro -;
    exact Frame.exists_relItr_of_le Rxy hlt;

@[grind →]
lemma forces_box_of_rel [IsTrans _ M.Rel'] {A : Formula α} (h : x ⊩ □A) (Rxy : x ≺ y) :
    y ⊩ □A :=
  forces_box.mpr fun _ Ryz => forces_box.mp h _ <| Frame.rel_trans Rxy Ryz

@[grind →]
lemma forces_dia_of_rel [IsTrans _ M.Rel'] {A : Formula α} (h : y ⊩ ◇A) (Rxy : x ≺ y) :
    x ⊩ ◇A := by
  obtain ⟨z, Ryz, hz⟩ := forces_dia.mp h;
  exact forces_dia.mpr ⟨z, Frame.rel_trans Rxy Ryz, hz⟩

lemma forces_neg_multidia_top_of_rel (hx : x ⊩ ∼◇^[n + 1]⊤) (Rxy : x ≺ y) : y ⊩ ∼◇^[n]⊤ := by
  rw [forces_neg_multidia_top] at hx ⊢;
  exact fun z Ryz => hx z <| Frame.relItr_head Rxy Ryz;

@[grind =]
lemma forces_subst {M : Model κ β} {x : M.World} {φ : Formula α} (s : Formula.Substitution α β) :
  x ⊩[M] φ⟦s⟧ ↔ x ⊩[⟨M.toFrame, fun w a => w ⊩[M] s a⟩] φ := by
  induction φ generalizing x <;> grind;

section Map

variable {M : Model κ β} {x : M.World}

lemma forces_map {φ : Formula α} {f : α → β} :
    x ⊩[M] φ.map f ↔ x ⊩[(⟨M.toFrame, fun w a => M.Val w (f a)⟩ : Model _ α)] φ := by
  unfold Formula.map;
  exact forces_subst _;

lemma forces_conj_map {ι : Type*} {l : List ι} {g : ι → Formula β} :
    x ⊩[M] ⋀(l.map g) ↔ ∀ i ∈ l, x ⊩[M] g i := by
  simp [forces_conj];

lemma forces_disj_map {ι : Type*} {l : List ι} {g : ι → Formula β} :
    x ⊩[M] ⋁(l.map g) ↔ ∃ i ∈ l, x ⊩[M] g i := by
  simp [forces_disj];

end Map

section Bisimilar

variable {κ₁ κ₂ : Type*} {M : Model κ₁ α} {N : Model κ₂ α}

def ModalEquivalent {M : Model κ₁ α} {N : Model κ₂ α} (x : M.World) (y : N.World) :=
  ∀ φ, x ⊩ φ ↔ y ⊩ φ
infix:60 " ↭ " => ModalEquivalent

namespace ModalEquivalent

variable {κ₃ : Type*} {O : Model κ₃ α} {x : M.World} {y : N.World} {z : O.World}

@[refl] lemma refl (x : M.World) : x ↭ x := fun _ => Iff.rfl

@[symm] lemma symm (h : x ↭ y) : y ↭ x := fun φ => (h φ).symm

@[trans] lemma trans (h₁ : x ↭ y) (h₂ : y ↭ z) : x ↭ z := fun φ => (h₁ φ).trans (h₂ φ)

end ModalEquivalent

/-- Two worlds without successors that agree on the variables agree on every formula. -/
lemma forces_iff_of_no_succ {x : M.World} {y : N.World}
    (hx : ∀ x', x ⊀ x')
    (hy : ∀ y', y ⊀ y')
    (hval : ∀ a, M.Val x a ↔ N.Val y a)
    : x ↭ y := by
  intro φ;
  induction φ with
  | dia φ _ =>
    apply iff_of_false;
    · contrapose! hx;
      rcases hx with ⟨x', _, -⟩;
      use x';
    · contrapose! hy;
      rcases hy with ⟨y', _, -⟩;
      use y';
  | _ => grind;

/-- In two models where every world has a successor and the valuations are constant and agree,
all worlds agree on every formula. -/
lemma forces_iff_of_serial
    (hM : ∀ x : M.World, ∃ x', x ≺ x')
    (hN : ∀ y : N.World, ∃ y', y ≺ y')
    (hval : ∀ (x : M.World) (y : N.World) a, M.Val x a ↔ N.Val y a)
    (x : M.World) (y : N.World) : x ↭ y := by
  intro φ;
  induction φ generalizing x y with
  | dia φ ih =>
    constructor;
    · rintro ⟨x', -, hx'⟩;
      obtain ⟨y', Ryy'⟩ := hN y;
      exact ⟨y', Ryy', (ih x' y').mp hx'⟩;
    · rintro ⟨y', -, hy'⟩;
      obtain ⟨x', Rxx'⟩ := hM x;
      exact ⟨x', Rxx', (ih x' y').mpr hy'⟩;
  | _ => grind;

end Bisimilar

end Model.World


namespace Model

variable {M : Model κ α} {φ : Formula α}

@[grind]
def Validates (M : Model κ α) (φ : Formula α) : Prop := ∀ x : M.World, x ⊩ φ
infix:50 " ⊧ " => Model.Validates

lemma not_validates_iff : ¬ M ⊧ φ ↔ ∃ x : M.World, x ⊮ φ := by
  simp [Validates]

/-- The formulas strongly valid in `M`, i.e. those all of whose substitution instances are valid
in `M`, form a normal logic.

- [Fin74a] -/
def logic (M : Model κ α) : NormalLogic α where
  carrier := {A | ∀ s : Formula.Substitution α α, M ⊧ A⟦s⟧}
  mdp hA hAB s x := hAB s x <| hA s x
  nec hA s x := World.forces_box.mpr fun y _ => hA s y
  subst {A t} hA s x := by
    rw [Formula.subst_subst];
    exact hA _ x

lemma mem_logic {A : Formula α} : A ∈ M.logic ↔ ∀ s : Formula.Substitution α α, M ⊧ A⟦s⟧ :=
  Iff.rfl

lemma validates_of_mem_logic {A : Formula α} (h : A ∈ M.logic) : M ⊧ A := by
  simpa using h (#·)

end Model



namespace Frame

variable {F : Frame κ} {φ ψ : Formula α}

@[grind =]
def Validates (F : Frame κ) (φ : Formula α) : Prop := ∀ V, (Model.mk F V) ⊧ φ
infix:50 " ⊧ " => Frame.Validates

abbrev NotValidates (F : Frame κ) (φ : Formula α) : Prop := ¬(F ⊧ φ)
infix:50 " ⊭ " => Frame.NotValidates

@[grind]
def ValidatesSet (F : Frame κ) (X : Set (Formula α)) : Prop := ∀ φ ∈ X, F.Validates φ
infix:50 " ⊧ " => Frame.ValidatesSet

abbrev ValidateLogic (F : Frame κ) (L : NormalLogic α) : Prop := F ⊧ L.carrier
infix:50 " ⊧ " => Frame.ValidateLogic

abbrev NotValidateLogic (F : Frame κ) (L : NormalLogic α) : Prop := ¬(F ⊧ L)
infix:50 " ⊭ " => Frame.NotValidateLogic

lemma not_validates_iff : F ⊭ φ ↔ ∃ V, ¬ (Model.mk F V) ⊧ φ := by
  simp [NotValidates, Validates]

lemma not_validates_iff' : F ⊭ φ ↔ ∃ V, ∃ x : (Model.mk F V).World, x ⊮[Model.mk F V] φ := by
  simp [not_validates_iff, Model.not_validates_iff]

lemma not_validatesSet_iff {X : Set (Formula α)} : ¬ F ⊧ X ↔ ∃ φ ∈ X, F ⊭ φ := by
  simp [ValidatesSet, NotValidates]

lemma not_validateLogic_iff {L : NormalLogic α} : F ⊭ L ↔ ∃ φ ∈ L, F ⊭ φ :=
  not_validatesSet_iff

lemma mdp (hA : F ⊧ φ) (hAB : F ⊧ φ 🡒 ψ) : F ⊧ ψ := by
  intro V x;
  exact hAB V x <| hA V x;

lemma nec (h : F ⊧ φ) : F ⊧ □φ := by grind;

lemma subst {s : Formula.Substitution α α} (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  intro V x;
  exact Model.World.forces_subst s |>.mpr <| h (fun w a => w ⊩[⟨F, V⟩] s a) x

abbrev logic (F : Frame κ) : NormalLogic α where
  carrier := { φ | F ⊧ φ }
  mdp := mdp
  nec := nec
  subst := subst

/-- A formula valid in a frame is strongly valid in every model on it. -/
lemma logic_le_model_logic {V : κ → α → Prop} : F.logic ≤ (Model.mk F V).logic :=
  fun _ h s => subst (s := s) h V

section Soundness

variable {X : FormulaSet α} {L : NormalLogic α}

lemma validates_ofSet (h : F ⊧ X) : F ⊧ (NormalLogic.ofSet X) := by
  rintro φ hA;
  induction hA with
  | mem h' => exact h _ h';
  | mdp _ _ ihφ ihφψ => exact mdp ihφ ihφψ;
  | nec _ ih => exact nec ih;
  | subst _ ih => exact subst ih;

lemma validates_axiomsK : F ⊧ (FormulaSet.axiomsK : FormulaSet α) := by
  rintro φ hA V x;
  cases hA <;> grind;

lemma validates_logicK : F ⊧ (𝐊 : NormalLogic α) := validates_ofSet validates_axiomsK

lemma validates_add (hL : F ⊧ L) (hX : F ⊧ X) : F ⊧ (L + X) := by
  apply validates_ofSet;
  rintro φ (hA | hA);
  · exact hL _ hA;
  · exact hX _ hA;

lemma not_mem_bot_of_validates [Nonempty F.World] (h : F ⊧ L) : (⊥ : Formula α) ∉ L :=
  fun hbot => h ⊥ hbot (fun _ _ => True) (Classical.arbitrary F.World)

lemma consistent_of_validates [Nonempty F.World] (h : F ⊧ L) : L.Consistent :=
  NormalLogic.consistent_iff.mpr ⟨⊥, not_mem_bot_of_validates h⟩

end Soundness

end Frame



end
