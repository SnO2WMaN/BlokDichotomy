module

public import BlokDichotomy.Incomplete.Naming
public import BlokDichotomy.Incomplete.Minimal
public import Mathlib.Tactic.DeriveCountable

/-!
# Blok's dichotomy theorem

The degree of Kripke incompleteness of a normal logic extending `𝐊` is `1` or the continuum.

## References

- [CZ98, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/

@[expose] public section

universe u

deriving instance Countable for Formula

namespace NormalLogic

open Cardinal

variable {L : NormalLogic ℕ} {P : {κ : Type u} → Frame κ → Prop}

/--
`degree P L ≤ 𝔠` for `L : NormalLogic ℕ`.
- [CZ98, §10.5]
-/
theorem degree_le_continuum : degree P L ≤ 𝔠 :=
  calc degree P L ≤ Cardinal.mk (Set (Formula ℕ)) :=
        mk_le_of_injective (f := fun L₁ : Companion P L => (L₁.1 : Set (Formula ℕ)))
          fun _ _ h => Subtype.ext <| SetLike.coe_injective h
    _ = 2 ^ Cardinal.mk (Formula ℕ) := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero mk_le_aleph0
    _ = 𝔠 := two_power_aleph0

variable [L.IsNExt 𝐊]

/--
If `L` is consistent and not a union-splitting of `𝐊`, then its degree is `𝔠`.
- [CZ98, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/
theorem degree_eq_continuum (hc : L.Consistent) (hL : ¬L.IsUnionSplitting)
  : L.degree.{u} (fun _ => True) = 𝔠 := by
  obtain ⟨n, D, φ, V, hφ, hV, hdepth, -, -, hgen, hrefl, -⟩ := exists_hookData hc hL;
  apply le_antisymm degree_le_continuum;
  exact Naming.HookInterface.continuum_le_degree (H := D.hooked)
    (fun I => D.hookInterface hc hgen hrefl hV hdepth I) (Naming.shift_mem hφ) (by omega);

/--
For consistent `L`, the degree of `L` is `1` iff `L` is a union-splitting of `𝐊`.
- [CZ98, Theorem 10.51, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/
theorem degree_eq_one_iff_isUnionSplitting (hc : L.Consistent)
  : L.degree (fun _ => True) = 1 ↔ L.IsUnionSplitting := by
  constructor;
  · intro h;
    exact
      not_not.mp fun hL => (one_lt_aleph0.trans aleph0_lt_continuum).ne'
      ((degree_eq_continuum hc hL).symm.trans h)
  · exact degree_eq_one_of_isUnionSplitting

/--
Blok's dichotomy: the degree of Kripke incompleteness of `L` is `1` or `𝔠`.
- [CZ98, Theorem 10.59]
- [Blok78, Theorem 4.9]
-/
theorem blok_dichotomy : L.degree.{u} (fun _ => True) = 1 ∨ L.degree.{u} (fun _ => True) = 𝔠 := by
  by_cases hc : L.Consistent;
  · by_cases hL : L.IsUnionSplitting;
    · exact Or.inl <| degree_eq_one_of_isUnionSplitting hL;
    · exact Or.inr <| degree_eq_continuum hc hL;
  · exact Or.inl <| degree_eq_one_of_not_consistent hc;

end NormalLogic

end
