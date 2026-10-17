module

public import BlokDichotomy.Kripke.PMorphism
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cycles in Kripke frames

Cycles in frames, and cycle-freeness of finite frames.

## References

- [CZ98, p. 362]
-/

@[expose] public section

universe u u' v

variable {κ : Type u} {ι : Type u'} {α : Type v}

namespace Frame

variable {F : Frame κ} {G : Frame ι} {x y z : F.World} {n m k : ℕ}

/-- `F` has a point `x` with `x ≺^[n] x` for some `n > 0`.
- [CZ98, p. 362] -/
def HasCycle (F : Frame κ) : Prop := ∃ x : F.World, ∃ n, 0 < n ∧ x ≺^[n] x

/-- `F` has no cycle.
- [CZ98, p. 362] -/
def CycleFree (F : Frame κ) : Prop := ¬F.HasCycle

lemma relItr_map (f : F.World → G.World) (hf : ∀ {x y : F.World}, x ≺ y → f x ≺ f y)
    (Rxy : x ≺^[n] y) : f x ≺^[n] f y := by
  induction n generalizing x with
  | zero => simp_all;
  | succ n ih =>
    obtain ⟨w, Rxw, Rwy⟩ := Rxy;
    exact ⟨f w, hf Rxw, ih Rwy⟩;

lemma HasCycle.of_forth (f : F.World → G.World) (hf : ∀ {x y : F.World}, x ≺ y → f x ≺ f y)
    (h : F.HasCycle) : G.HasCycle := by
  obtain ⟨x, n, hn, Rxx⟩ := h;
  exact ⟨f x, n, hn, relItr_map f hf Rxx⟩;

lemma HasCycle.of_pMorphism (f : F →ₚ G) (h : F.HasCycle) : G.HasCycle :=
  h.of_forth f f.forth

lemma CycleFree.of_pMorphism (f : F →ₚ G) (h : G.CycleFree) : F.CycleFree :=
  fun hF => h <| hF.of_pMorphism f

lemma relItr_mul (Rxx : x ≺^[k] x) : x ≺^[k * m] x := by
  induction m with
  | zero => simp;
  | succ m ih => rw [Nat.mul_succ]; exact relItr_trans ih Rxx;

lemma exists_path (Rxy : x ≺^[n] y) :
    ∃ p : ℕ → F.World, p 0 = x ∧ p n = y ∧ ∀ i < n, p i ≺ p (i + 1) := by
  induction n generalizing x with
  | zero => exact ⟨fun _ => x, rfl, Rxy, by simp⟩;
  | succ n ih =>
    obtain ⟨w, Rxw, Rwy⟩ := Rxy;
    obtain ⟨p, hp₀, hpn, hp⟩ := ih Rwy;
    use fun i => if i = 0 then x else p (i - 1);
    and_intros;
    · simp;
    · simpa using hpn;
    · rintro (_ | i) hi;
      · simpa [hp₀] using Rxw;
      · simpa using hp i (by omega);

lemma relItr_of_path {p : ℕ → F.World} (hp : ∀ i < n, p i ≺ p (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) : p i ≺^[j - i] p j := by
  induction j with
  | zero => obtain rfl : i = 0 := (by omega); simp;
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hij';
    · simp;
    · rw [show j + 1 - i = (j - i) + 1 by omega];
      exact relItr_tail (ih (by omega) (by omega)) (hp j (by omega));

/-- If `x ≺^[Nat.card F.World] y`, then some `z` reachable from `x` has `z ≺^[k] z` for some
`k > 0`. -/
lemma exists_cycle_of_relItr_card [Finite F.World] (Rxy : x ≺^[Nat.card F.World] y) :
    ∃ z ∈ F.Reach x, ∃ k, 0 < k ∧ z ≺^[k] z := by
  obtain ⟨p, hp₀, -, hp⟩ := exists_path Rxy;
  have hni : ¬Function.Injective (fun i : Fin (Nat.card F.World + 1) => p i) := by
    intro hi;
    have := Nat.card_le_card_of_injective _ hi;
    simp at this;
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hni;
  have hne' : (i : ℕ) ≠ j := Fin.val_ne_of_ne hne;
  wlog hlt : (i : ℕ) < j generalizing i j;
  · exact this j i hij.symm hne.symm hne'.symm <| by omega;
  use p i;
  and_intros;
  · have := relItr_of_path hp (Nat.zero_le i) (by omega);
    rw [hp₀] at this;
    exact mem_reach_of_relItr this;
  · use j - i;
    and_intros;
    · omega;
    · have := relItr_of_path hp hlt.le (by omega);
      rwa [← hij] at this;

/-- A finite frame is cycle-free iff `x ⊀^[n] y` for all `x y` and some `n`.
- [CZ98, p. 362] -/
lemma cycleFree_iff_exists_not_relItr [Finite F.World] :
    F.CycleFree ↔ ∃ n, ∀ x y : F.World, x ⊀^[n] y := by
  constructor;
  · intro h;
    use Nat.card F.World;
    intro x y Rxy;
    obtain ⟨z, -, k, hk, Rzz⟩ := exists_cycle_of_relItr_card Rxy;
    exact h ⟨z, k, hk, Rzz⟩;
  · rintro ⟨n, hn⟩ ⟨x, k, hk, Rxx⟩;
    obtain ⟨z, Rxz⟩ := exists_relItr_of_le (relItr_mul (m := n) Rxx) (Nat.le_mul_of_pos_left n hk);
    exact hn x z Rxz;

open Model.World in
lemma validates_neg_multidia_top_iff :
    F ⊧ (∼◇^[n]⊤ : Formula α) ↔ ∀ x y : F.World, x ⊀^[n] y := by
  constructor;
  · intro h x;
    exact forces_neg_multidia_top.mp <| h (fun _ _ => True) x;
  · intro h V x;
    exact forces_neg_multidia_top.mpr <| h x;

/-- A finite frame is cycle-free iff it validates `∼◇^[n]⊤` for some `n`.
- [CZ98, p. 362] -/
lemma cycleFree_iff_validates_neg_multidia_top [Finite F.World] :
    F.CycleFree ↔ ∃ n, F ⊧ (∼◇^[n]⊤ : Formula α) := by
  simp only [validates_neg_multidia_top_iff];
  exact cycleFree_iff_exists_not_relItr;

/-- A finite nonempty cycle-free frame has `n` such that `x ≺^[n] y` for some `x y` and
`x ⊀^[n + 1] y` for all `x y`. -/
lemma CycleFree.exists_height [Finite F.World] [Nonempty F.World] (h : F.CycleFree) :
    ∃ n, (∃ x y : F.World, x ≺^[n] y) ∧ ∀ x y : F.World, x ⊀^[n + 1] y := by
  obtain ⟨n, hn, hn'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
    (fun h₀ => h₀ (Classical.arbitrary F.World) _ relItr_zero_self)
    (cycleFree_iff_exists_not_relItr.mp h);
  push Not at hn;
  exact ⟨n, hn, hn'⟩;

end Frame


namespace Model.World

variable {M : Model κ α} {x : M.World}

/-- On a finite frame, `x ⊩ farthest n` for some `n`, or a cycle is reachable from `x`.
- [CZ98, p. 362] -/
lemma exists_forces_farthest_or_reach_cycle [Finite M.World] :
    (∃ n, x ⊩[M] farthest n) ∨ ∃ y ∈ M.Reach x, ∃ k, 0 < k ∧ y ≺^[k] y := by
  by_cases hex : ∃ n, ∀ y : M.World, x ⊀^[n] y;
  · obtain ⟨n, hn, hn'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
      (fun h₀ => h₀ x Frame.relItr_zero_self) hex;
    push Not at hn;
    exact Or.inl ⟨n, iff_forces_farthest.mpr ⟨hn, hn'⟩⟩;
  · push Not at hex;
    obtain ⟨y, Rxy⟩ := hex (Nat.card M.World);
    exact Or.inr <| Frame.exists_cycle_of_relItr_card Rxy;

end Model.World

end
