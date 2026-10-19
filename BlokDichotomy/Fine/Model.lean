module

public import BlokDichotomy.Fine.Basic
public import BlokDichotomy.ToMathlib.Order.Monotone.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Fine's model

The countermodel `𝔄` of [Fin74a] witnessing `∼ε ∉ logicS4Fine`: a partial order on four families
of points `a_m`, `b_m`, `c_m`, `d_m`, in which only `d`-points start infinite strict chains. The
involution `swap` exchanging the `b`- and `c`-families is an automorphism of the underlying frame.
The points form the inductive type `fineFrame.World` (with the relation `fineFrame.R` and the
valuation `fineModel.val`), which gives the frame `fineFrame` and the model `fineModel`; facts
about the forcing relation of a frame or a model are stated in the namespace of that object.

## References

- [Fin74a, p. 25]
-/

@[expose] public section

/-- The points of Fine's model.

- [Fin74a, p. 25] -/
inductive fineFrame.World
| a (m : ℕ)
| b (m : ℕ)
| c (m : ℕ)
| d (m : ℕ)
deriving DecidableEq

namespace fineFrame

open Fine

/-- The accessibility relation of Fine's model, given in closed form (no transitive closure),
reconstructed from [Fin74a]'s (partly missing) definition. -/
@[grind =]
def R : World → World → Prop
| .b m, .b k => k ≤ m
| .b m, .c k => k + 2 ≤ m
| .c m, .c k => k ≤ m
| .c m, .b k => k + 2 ≤ m
| .a m, .a k => k = m
| .a m, .b k => k ≤ m + 1
| .a m, .c k => k ≤ m + 1
| .d n, .d k => n ≤ k
| .d n, .a m => n ≤ m
| .d _, .b _ => True
| .d _, .c _ => True
| _, _ => False

@[simp] lemma R_a_a {m k : ℕ} : R (.a m) (.a k) ↔ k = m := by simp [R];
@[simp] lemma R_a_b {m k : ℕ} : R (.a m) (.b k) ↔ k ≤ m + 1 := by simp [R];
@[simp] lemma R_a_c {m k : ℕ} : R (.a m) (.c k) ↔ k ≤ m + 1 := by simp [R];
@[simp] lemma R_a_d {m k : ℕ} : ¬ R (.a m) (.d k) := by simp [R];
@[simp] lemma R_b_a {m k : ℕ} : ¬ R (.b m) (.a k) := by simp [R];
@[simp] lemma R_b_b {m k : ℕ} : R (.b m) (.b k) ↔ k ≤ m := by simp [R];
@[simp] lemma R_b_c {m k : ℕ} : R (.b m) (.c k) ↔ k + 2 ≤ m := by simp [R];
@[simp] lemma R_b_d {m k : ℕ} : ¬ R (.b m) (.d k) := by simp [R];
@[simp] lemma R_c_a {m k : ℕ} : ¬ R (.c m) (.a k) := by simp [R];
@[simp] lemma R_c_b {m k : ℕ} : R (.c m) (.b k) ↔ k + 2 ≤ m := by simp [R];
@[simp] lemma R_c_c {m k : ℕ} : R (.c m) (.c k) ↔ k ≤ m := by simp [R];
@[simp] lemma R_c_d {m k : ℕ} : ¬ R (.c m) (.d k) := by simp [R];
@[simp] lemma R_d_a {n m : ℕ} : R (.d n) (.a m) ↔ n ≤ m := by simp [R];
@[simp] lemma R_d_b {n k : ℕ} : R (.d n) (.b k) := by simp [R];
@[simp] lemma R_d_c {n k : ℕ} : R (.d n) (.c k) := by simp [R];
@[simp] lemma R_d_d {n k : ℕ} : R (.d n) (.d k) ↔ n ≤ k := by simp [R];

@[grind .] lemma R_refl (w : World) : R w w := by cases w <;> simp;

@[grind →]
lemma R_trans {x y z : World} (hxy : R x y) (hyz : R y z) : R x z := by
  cases x <;> cases y <;> cases z <;> simp_all <;> omega;

/-- `R` is antisymmetric, so `(World, R)` is a partial order. -/
lemma R_antisymm {x y : World} (hxy : R x y) (hyx : R y x) : x = y := by
  cases x <;> cases y <;> simp_all <;> omega;

instance : Std.Refl R := ⟨R_refl⟩

instance : IsTrans World R := ⟨fun _ _ _ => R_trans⟩

/-- The `R`-cone of a point other than a `d`-point is finite. -/
lemma cone_finite {w : World} (hw : ∀ k, w ≠ .d k) : {z | R w z}.Finite := by
  obtain ⟨m, hm⟩ : ∃ m, ∀ z, R w z → ∃ k ≤ m, z = .a k ∨ z = .b k ∨ z = .c k := by
    cases w with
    | d k => exact absurd rfl (hw k);
    | a m =>
      use m + 1;
      intro z hz;
      cases z <;> simp_all;
    | b m =>
      use m + 1;
      intro z hz;
      cases z <;> simp_all <;> omega;
    | c m =>
      use m + 1;
      intro z hz;
      cases z <;> simp_all <;> omega;
  apply ((Finset.range (m + 1)).image World.a ∪ (Finset.range (m + 1)).image World.b ∪
    (Finset.range (m + 1)).image World.c).finite_toSet.subset;
  intro z hz;
  obtain ⟨k, hk, rfl | rfl | rfl⟩ := hm z hz <;> simp [Nat.lt_succ_iff, hk];

/-- Every infinite strict `R`-chain consists entirely of `d`-points. -/
lemma strict_chain_all_d {u : ℕ → World} (hR : ∀ m, R (u m) (u (m + 1)))
    (hs : ∀ m, ¬R (u (m + 1)) (u m)) (i : ℕ) : ∃ k, u i = .d k := by
  have hinj : Function.Injective u := injective_of_forall_rel_succ (r := R) hR hs;
  have hchain : ∀ n, R (u i) (u (i + n)) := by
    intro n;
    induction n with
    | zero => simpa using R_refl (u i);
    | succ n ih => exact R_trans ih (hR (i + n));
  have hinj' : Function.Injective fun n => u (i + n) := by
    intro a b hab;
    have := hinj hab;
    omega;
  have hinf : {z | R (u i) z}.Infinite := Set.infinite_of_injective_forall_mem hinj' hchain;
  by_contra h;
  push Not at h;
  exact (cone_finite h).not_infinite hinf

/-! ### The `b`/`c` mirror involution -/

/-- The involution on Fine's model's worlds exchanging the `b`- and `c`-families and fixing
the `a`- and `d`-families. -/
def swap : World → World
| .a m => .a m
| .b m => .c m
| .c m => .b m
| .d m => .d m

@[simp] lemma swap_a {m : ℕ} : swap (.a m) = .a m := rfl
@[simp] lemma swap_b {m : ℕ} : swap (.b m) = .c m := rfl
@[simp] lemma swap_c {m : ℕ} : swap (.c m) = .b m := rfl
@[simp] lemma swap_d {m : ℕ} : swap (.d m) = .d m := rfl

lemma swap_involutive : Function.Involutive swap := by intro x; cases x <;> rfl;

@[simp] lemma swap_swap (w : World) : swap (swap w) = w := swap_involutive w

/-- `R` does not distinguish the `b`- and `c`-families, only their indices. -/
lemma R_swap {x y : World} : R (swap x) (swap y) ↔ R x y := by cases x <;> cases y <;> simp;

end fineFrame

/-- Fine's frame: the points `fineFrame.World` ordered by `fineFrame.R`.

- [Fin74a, p. 25] -/
abbrev fineFrame : Frame fineFrame.World := ⟨fineFrame.R⟩

namespace fineModel

/-- The valuation of Fine's model, reconstructed from [Fin74a]: `V(q₀) = {b₀}`, `V(q₁) = {b₁}`,
`V(r₀) = {c₀}`, `V(r₁) = {c₁}`, `V(p₀) = {d_{2k} : k ≥ 0}`, `V(p₁) = {d_{2k+1} : k ≥ 0}`, and
all other atoms are valuated `∅`. Atom indices follow Fine's `p₀, p₁, q₀, q₁, r₀, r₁, s, t`
(`#0`–`#7`). -/
@[grind =]
def val : fineFrame.World → ℕ → Prop
| .b 0, 2 => True
| .b 1, 3 => True
| .c 0, 4 => True
| .c 1, 5 => True
| .d n, 0 => n % 2 = 0
| .d n, 1 => n % 2 = 1
| _, _ => False

@[simp] lemma val_a {m a : ℕ} : ¬ val (.a m) a := by simp [val];
@[simp] lemma val_b_iff {m a : ℕ} : val (.b m) a ↔ (m = 0 ∧ a = 2) ∨ (m = 1 ∧ a = 3) := by
  rcases m with _ | _ | m <;> rcases a with _ | _ | _ | _ | a <;> simp [val];
@[simp] lemma val_c_iff {m a : ℕ} : val (.c m) a ↔ (m = 0 ∧ a = 4) ∨ (m = 1 ∧ a = 5) := by
  rcases m with _ | _ | m <;> rcases a with _ | _ | _ | _ | _ | _ | a <;> simp [val];
@[simp] lemma val_d_iff {n a : ℕ} : val (.d n) a ↔ (a = 0 ∧ n % 2 = 0) ∨ (a = 1 ∧ n % 2 = 1) := by
  rcases a with _ | _ | a <;> simp [val];

end fineModel

/-- Fine's model: `fineFrame` with the valuation `fineModel.val`.

- [Fin74a, p. 25] -/
abbrev fineModel : Model fineFrame.World ℕ := ⟨fineFrame, fineModel.val⟩

namespace fineFrame

open Fine fineFrame.World

variable {V : World → ℕ → Prop} {x y : World}

@[simp] lemma rel_iff : Frame.Rel (F := fineFrame) x y ↔ R x y := Iff.rfl

@[simp] lemma forces_atom {n : ℕ} : x ⊩[⟨fineFrame, V⟩] #n ↔ V x n := Iff.rfl

end fineFrame

namespace fineModel

open Fine fineFrame.World

variable {x : fineFrame.World}

@[simp high] lemma forces_atom_0_iff : x ⊩[fineModel] #0 ↔ ∃ k, x = .d k ∧ k % 2 = 0 := by
  cases x <;> simp
@[simp high] lemma forces_atom_1_iff : x ⊩[fineModel] #1 ↔ ∃ k, x = .d k ∧ k % 2 = 1 := by
  cases x <;> simp
@[simp high] lemma forces_atom_2_iff : x ⊩[fineModel] #2 ↔ x = .b 0 := by cases x <;> simp
@[simp high] lemma forces_atom_3_iff : x ⊩[fineModel] #3 ↔ x = .b 1 := by cases x <;> simp
@[simp high] lemma forces_atom_4_iff : x ⊩[fineModel] #4 ↔ x = .c 0 := by cases x <;> simp
@[simp high] lemma forces_atom_5_iff : x ⊩[fineModel] #5 ↔ x = .c 1 := by cases x <;> simp

end fineModel

end
