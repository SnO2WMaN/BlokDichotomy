module

public import BlokDichotomy.Fine.Basic
public import BlokDichotomy.ToMathlib.Order.Monotone.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Fine's model

The countermodel `𝔄` of [Fin74] witnessing `∼E ∉ Fine.logic`: a partial order on four families
of points `a_m`, `b_m`, `c_m`, `d_m`, in which only `d`-points start infinite strict chains.

## References

- [Fin74, p. 25]
-/

@[expose] public section

namespace Fine

/-- The points of Fine's model.

- [Fin74, p. 25] -/
inductive World
| a (m : ℕ)
| b (m : ℕ)
| c (m : ℕ)
| d (m : ℕ)
deriving DecidableEq

/-- The accessibility relation of Fine's model, given in closed form (no transitive closure),
reconstructed from [Fin74]'s (partly missing) definition. -/
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

@[grind .] lemma R_refl (w : World) : R w w := by cases w <;> simp [R]

@[grind →]
lemma R_trans {x y z : World} (hxy : R x y) (hyz : R y z) : R x z := by
  cases x <;> cases y <;> cases z <;> simp_all [R] <;> omega

/-- `R` is antisymmetric, so `(World, R)` is a partial order. -/
lemma R_antisymm {x y : World} (hxy : R x y) (hyx : R y x) : x = y := by
  cases x <;> cases y <;> simp_all [R] <;> omega

instance : Std.Refl R := ⟨R_refl⟩

instance : IsTrans World R := ⟨fun _ _ _ => R_trans⟩

abbrev frame : Frame World := ⟨R⟩

/-- The valuation of Fine's model, reconstructed from [Fin74]: `V(q₀) = {b₀}`, `V(q₁) = {b₁}`,
`V(r₀) = {c₀}`, `V(r₁) = {c₁}`, `V(p₀) = {d_{2k} : k ≥ 0}`, `V(p₁) = {d_{2k+1} : k ≥ 0}`, and
all other atoms are valuated `∅`. Atom indices follow `Fine.p0, .p1, .q0, .q1, .r0, .r1, .s, .t`
(`#0`–`#7`). -/
@[grind =]
def val : World → ℕ → Prop
| .b 0, 2 => True
| .b 1, 3 => True
| .c 0, 4 => True
| .c 1, 5 => True
| .d n, 0 => n % 2 = 0
| .d n, 1 => n % 2 = 1
| _, _ => False

def model : Model World ℕ := ⟨frame, val⟩

/-! ### Cone finiteness and confinement to the `d`-points -/

/-- The `R`-cone of a `b`-point is finite. -/
lemma cone_b_finite (m : ℕ) : {z | R (.b m) z}.Finite := by
  apply Set.Finite.subset (Finset.image World.b (Finset.range (m + 1)) ∪
    Finset.image World.c (Finset.range (m + 1))).finite_toSet;
  rintro z hz;
  cases z with
  | b k =>
    simp [R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    left; exact ⟨k, by omega, rfl⟩
  | c k =>
    simp [R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    right; exact ⟨k, by omega, rfl⟩
  | a k => simp [R] at hz
  | d k => simp [R] at hz

/-- The `R`-cone of a `c`-point is finite. -/
lemma cone_c_finite (m : ℕ) : {z | R (.c m) z}.Finite := by
  apply Set.Finite.subset (Finset.image World.b (Finset.range (m + 1)) ∪
    Finset.image World.c (Finset.range (m + 1))).finite_toSet;
  rintro z hz;
  cases z with
  | b k =>
    simp [R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    left; exact ⟨k, by omega, rfl⟩
  | c k =>
    simp [R] at hz;
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, Set.mem_union,
      Set.mem_image, Set.mem_Iio];
    right; exact ⟨k, by omega, rfl⟩
  | a k => simp [R] at hz
  | d k => simp [R] at hz

/-- The `R`-cone of an `a`-point is finite. -/
lemma cone_a_finite (m : ℕ) : {z | R (.a m) z}.Finite := by
  apply Set.Finite.subset ({World.a m} ∪ Finset.image World.b (Finset.range (m + 2)) ∪
    Finset.image World.c (Finset.range (m + 2)) : Finset World).finite_toSet;
  rintro z hz;
  cases z with
  | a k => simp [R] at hz; simp [hz]
  | b k =>
    simp [R] at hz;
    simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_range,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_Iio];
    exact Or.inl (Or.inr ⟨k, by omega, rfl⟩)
  | c k =>
    simp [R] at hz;
    simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_range,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_Iio];
    exact Or.inr ⟨k, by omega, rfl⟩
  | d k => simp [R] at hz

/-- Every infinite strict `R`-chain consists entirely of `d`-points. -/
lemma strict_chain_all_d {u : ℕ → World} (hR : ∀ m, R (u m) (u (m + 1)))
    (hs : ∀ m, ¬R (u (m + 1)) (u m)) (i : ℕ) : ∃ k, u i = .d k := by
  have hinj : Function.Injective u := injective_of_forall_rel_succ (r := R) hR hs;
  have hchain : ∀ n, R (u i) (u (i + n)) := by
    intro n; induction n with
    | zero => simpa using R_refl (u i)
    | succ n ih => exact R_trans ih (hR (i + n))
  have hmem : ∀ n, u (i + n) ∈ {z | R (u i) z} := hchain
  have hfinj : Function.Injective (fun n => u (i + n)) :=
    fun a b hab => by have := hinj hab; omega
  have hinf : {z | R (u i) z}.Infinite := Set.infinite_of_injective_forall_mem hfinj hmem
  cases hui : u i with
  | d k => exact ⟨k, rfl⟩
  | b m => exact absurd (hui ▸ hinf) (cone_b_finite m).not_infinite
  | c m => exact absurd (hui ▸ hinf) (cone_c_finite m).not_infinite
  | a m => exact absurd (hui ▸ hinf) (cone_a_finite m).not_infinite

end Fine

end
