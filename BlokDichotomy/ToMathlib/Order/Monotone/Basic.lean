module

public import Mathlib.Order.Monotone.Basic

/-!
# Chains along a relation indexed by `ℕ`

Dependent choice of a chain whose `m`-th point satisfies a stage-indexed invariant, and
injectivity of a chain along a transitive relation none of whose steps can be reversed.
-/

@[expose] public section

variable {α : Type*} {r : α → α → Prop}

/-- If every point satisfying `P m` has an `r`-successor satisfying `P (m + 1)`, then every point
satisfying `P 0` starts an `r`-chain whose `m`-th point satisfies `P m`. -/
theorem exists_seq_of_forall_exists_rel {P : ℕ → α → Prop} {a : α} (ha : P 0 a)
    (h : ∀ m x, P m x → ∃ y, r x y ∧ P (m + 1) y) :
    ∃ f : ℕ → α, f 0 = a ∧ ∀ m, P m (f m) ∧ r (f m) (f (m + 1)) := by
  choose g hg using h;
  let F : (m : ℕ) → {x // P m x} :=
    fun m => Nat.rec ⟨a, ha⟩ (fun m x => ⟨g m x.1 x.2, (hg m x.1 x.2).2⟩) m;
  exact ⟨fun m => (F m).1, rfl, fun m => ⟨(F m).2, (hg m _ (F m).2).1⟩⟩

/-- A chain along a transitive relation none of whose steps can be reversed is injective. -/
theorem injective_of_forall_rel_succ [IsTrans α r] {f : ℕ → α}
    (h : ∀ n, r (f n) (f (n + 1))) (hs : ∀ n, ¬r (f (n + 1)) (f n)) : Function.Injective f := by
  refine .of_lt_imp_ne fun i j hij heq => hs i ?_;
  rcases (Nat.succ_le_of_lt hij).eq_or_lt with hj | hj;
  · have : f (i + 1) = f i := (congrArg f hj).trans heq.symm;
    simpa [this] using h i;
  · exact heq ▸ Nat.rel_of_forall_rel_succ_of_lt r h hj
