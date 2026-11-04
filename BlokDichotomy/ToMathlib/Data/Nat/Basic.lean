module

public import Mathlib.Data.Nat.Basic

/-!
# Successor modulo `m`
-/

@[expose] public section

namespace Nat

lemma succ_mod_of_lt {p m : ℕ} (h : p % m + 1 < m) : (p + 1) % m = p % m + 1 := by
  rw [← Nat.mod_add_mod];
  exact Nat.mod_eq_of_lt h

lemma succ_mod_of_eq {p m : ℕ} (h : p % m + 1 = m) : (p + 1) % m = 0 := by
  rw [← Nat.mod_add_mod, h, Nat.mod_self]

end Nat

end
