module

public import BlokDichotomy.Logic.Basic
public import BlokDichotomy.Kripke.Basic
public import Mathlib.Order.Zorn

/-!
# Completeness of normal logics via the canonical model

Maximal consistent sets, Lindenbaum's lemma, the canonical model, and the truth lemma.

## References

- [CZ98, Theorem 1.16, §5.1]
-/

@[expose] public section

universe v

namespace Formula

variable {α : Type v} {φ ψ : Formula α} {l : List (Formula α)}

/-- A Boolean evaluation of formulas: it respects `⊥` and `🡒`, and assigns arbitrary truth values
to atoms and `◇`-formulas. -/
structure BoolEval (α : Type v) where
  eval : Formula α → Prop
  eval_bot' : ¬eval ⊥
  eval_imp' (φ ψ : Formula α) : eval (φ 🡒 ψ) ↔ (eval φ → eval ψ)

namespace BoolEval

instance : CoeFun (BoolEval α) (fun _ => Formula α → Prop) := ⟨BoolEval.eval⟩

variable (v : BoolEval α)

@[simp, grind .] lemma eval_bot : v ⊥ ↔ False := iff_false_intro v.eval_bot'
@[simp, grind .] lemma eval_top : v ⊤ := (v.eval_imp' ⊥ ⊥).mpr id
@[simp, grind =] lemma eval_imp : v (φ 🡒 ψ) ↔ (v φ → v ψ) := v.eval_imp' φ ψ
@[simp, grind =] lemma eval_neg : v (∼φ) ↔ ¬v φ := by simp
@[simp, grind =] lemma eval_and : v (φ ⋏ ψ) ↔ v φ ∧ v ψ := by simp
@[simp, grind =] lemma eval_or : v (φ ⋎ ψ) ↔ v φ ∨ v ψ := by simp; tauto
@[simp, grind =] lemma eval_iff : v (φ 🡘 ψ) ↔ (v φ ↔ v ψ) := by simp; tauto
@[simp, grind =] lemma eval_conj : v (⋀l) ↔ ∀ φ ∈ l, v φ := by induction l <;> simp_all
@[simp, grind =] lemma eval_disj : v (⋁l) ↔ ∃ φ ∈ l, v φ := by
  induction l with
  | nil => simp;
  | cons φ l ih => rw [disj_cons, eval_or, ih, List.exists_mem_cons_iff];

end BoolEval

def IsTautology (φ : Formula α) : Prop := ∀ v : BoolEval α, v.eval φ

end Formula

namespace FormulaSet

variable {α : Type v} {L : NormalLogic α}

def Consistent (L : NormalLogic α) (Γ : FormulaSet α) : Prop := Γ ⊬[L] ⊥

end FormulaSet

namespace NormalLogic

variable {α : Type v} {L : NormalLogic α}

/-- A maximal `L`-consistent set of formulas.
- [CZ98, §5.1]
-/
@[ext]
structure MaximalConsistentSet (L : NormalLogic α) where
  carrier : FormulaSet α
  maximal : Maximal (FormulaSet.Consistent L) carrier

namespace MaximalConsistentSet

instance : SetLike L.MaximalConsistentSet (Formula α) where
  coe x := x.carrier
  coe_injective _ _ h := MaximalConsistentSet.ext h

end MaximalConsistentSet

end NormalLogic

namespace FormulaSet

open Formula NormalLogic Derives

variable {α : Type v} {L : NormalLogic α} {Γ : FormulaSet α} {φ ψ : Formula α}

lemma consistent_insert_neg_iff [L.IsNExt 𝐊] :
    (insert (∼φ) Γ).Consistent L ↔ Γ ⊬[L] φ := by
  unfold FormulaSet.Consistent NotDerives;
  rw [deduction_iff];
  refine ⟨fun h hA => h <| deduction <|
    Derives.mdp (hA.mono <| Set.subset_insert _ Γ) (mem <| Set.mem_insert _ Γ),
    fun h hA => h <| of_imp_mem dne hA⟩

lemma consistent_singleton_neg_iff [L.IsNExt 𝐊] : ({∼φ} : FormulaSet α).Consistent L ↔ φ ∉ L := by
  rw [← insert_empty_eq, consistent_insert_neg_iff];
  unfold NotDerives;
  rw [empty_iff];

lemma consistent_empty_iff [L.IsNExt 𝐊] : (∅ : FormulaSet α).Consistent L ↔ ⊥ ∉ L := by
  unfold FormulaSet.Consistent NotDerives;
  rw [empty_iff];

/-- Every `L`-consistent set is contained in a maximal `L`-consistent set.
- [CZ98, Lemma 5.1]
-/
theorem lindenbaum (h : Γ.Consistent L) : ∃ x : L.MaximalConsistentSet, Γ ⊆ x.carrier := by
  obtain ⟨Δ, hΓΔ, hΔ⟩ := zorn_subset_nonempty { Δ : FormulaSet α | Δ.Consistent L } (by
    intro c hc hchain hne;
    use ⋃₀ c;
    constructor;
    · intro hbot;
      obtain ⟨Δ, hΔ, hfin, hd⟩ := hbot.exists_finite;
      obtain ⟨t, ht, hΔt⟩ :=
        DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne hchain.directedOn hfin hΔ;
      exact hc ht <| hd.mono hΔt;
    · intro s hs;
      exact Set.subset_sUnion_of_mem hs) Γ h;
  exact ⟨⟨Δ, hΔ⟩, hΓΔ⟩;

end FormulaSet

namespace NormalLogic.MaximalConsistentSet

open Formula Derives

variable {α : Type v} {L : NormalLogic α} {φ ψ : Formula α} {l : List (Formula α)}
  (x : L.MaximalConsistentSet)

lemma consistent : x.carrier.Consistent L := x.maximal.prop

lemma bot_not_mem : ⊥ ∉ x := fun h => x.consistent <| mem h

variable [L.IsNExt 𝐊]

lemma mem_of_derives (h : x.carrier ⊢[L] φ) : φ ∈ x := by
  have hc : (insert φ x.carrier).Consistent L := fun hbot =>
    x.consistent <| cut h hbot;
  exact x.maximal.2 hc (Set.subset_insert φ x.carrier) <| Set.mem_insert φ x.carrier;

lemma mem_iff_derives : φ ∈ x ↔ x.carrier ⊢[L] φ :=
  ⟨mem, x.mem_of_derives⟩

lemma mem_of_mem_logic (h : φ ∈ L) : φ ∈ x :=
  x.mem_of_derives <| thm h

lemma mem_mdp (hA : φ ∈ x) (hAB : φ 🡒 ψ ∈ x) : ψ ∈ x :=
  x.mem_of_derives <| Derives.mdp (mem hA) (mem hAB)

lemma mem_of_imp_mem (hAB : φ 🡒 ψ ∈ L) (hA : φ ∈ x) : ψ ∈ x :=
  x.mem_mdp hA <| x.mem_of_mem_logic hAB

lemma neg_mem_of_not_mem (h : φ ∉ x) : ∼φ ∈ x := by
  apply x.mem_of_derives;
  apply deduction;
  by_contra hc;
  exact h <| x.maximal.2 hc (Set.subset_insert φ x.carrier) <| Set.mem_insert φ x.carrier;

lemma mem_or_neg_mem (φ : Formula α) : φ ∈ x ∨ ∼φ ∈ x :=
  (em (φ ∈ x)).imp_right x.neg_mem_of_not_mem

lemma imp_mem_iff : φ 🡒 ψ ∈ x ↔ φ ∈ x → ψ ∈ x := by
  constructor;
  · exact fun h hA => x.mem_mdp hA h;
  · intro h;
    rcases x.mem_or_neg_mem φ with hA | hA;
    · exact x.mem_of_derives <| of_imp_mem imply₁ <| mem <| h hA;
    · apply x.mem_of_derives;
      apply deduction;
      apply Derives.efq;
      exact Derives.mdp (mem <| Set.mem_insert φ x.carrier)
        (mem <| Set.mem_insert_of_mem φ hA);

lemma neg_mem_iff : ∼φ ∈ x ↔ φ ∉ x := by
  rw [x.imp_mem_iff];
  have := x.bot_not_mem;
  tauto;

def toBoolEval : BoolEval α where
  eval := (· ∈ x)
  eval_bot' := x.bot_not_mem
  eval_imp' _ _ := x.imp_mem_iff

@[grind .] lemma top_mem : ⊤ ∈ x := x.toBoolEval.eval_top
@[grind =] lemma and_mem_iff : φ ⋏ ψ ∈ x ↔ φ ∈ x ∧ ψ ∈ x := x.toBoolEval.eval_and
@[grind =] lemma or_mem_iff : φ ⋎ ψ ∈ x ↔ φ ∈ x ∨ ψ ∈ x := x.toBoolEval.eval_or
@[grind =] lemma iff_mem_iff : φ 🡘 ψ ∈ x ↔ (φ ∈ x ↔ ψ ∈ x) := x.toBoolEval.eval_iff
@[grind =] lemma conj_mem_iff : ⋀l ∈ x ↔ ∀ φ ∈ l, φ ∈ x := x.toBoolEval.eval_conj
@[grind =] lemma disj_mem_iff : ⋁l ∈ x ↔ ∃ φ ∈ l, φ ∈ x := x.toBoolEval.eval_disj

lemma exists_mem_not_mem_of_ne {x y : L.MaximalConsistentSet} (hxy : x ≠ y) :
    ∃ φ ∈ x, φ ∉ y := by
  contrapose! hxy;
  ext φ;
  constructor;
  · exact hxy φ;
  · intro hy;
    by_contra hx;
    exact (y.neg_mem_iff.mp <| hxy _ <| x.neg_mem_of_not_mem hx) hy;

end NormalLogic.MaximalConsistentSet

namespace NormalLogic

open Formula Derives

variable {α : Type v} {L : NormalLogic α} {φ : Formula α} [L.IsNExt 𝐊]

lemma exists_maximalConsistentSet_not_mem (h : φ ∉ L) :
    ∃ x : L.MaximalConsistentSet, φ ∉ x := by
  obtain ⟨x, hsub⟩ := FormulaSet.lindenbaum <| FormulaSet.consistent_singleton_neg_iff.mpr h;
  exact ⟨x, x.neg_mem_iff.mp <| hsub rfl⟩;

/-- `φ ∈ L` iff `φ ∈ x` for every maximal `L`-consistent set `x`.
- [CZ98, Theorem 5.5]
-/
lemma mem_iff_forall_maximalConsistentSet : φ ∈ L ↔ ∀ x : L.MaximalConsistentSet, φ ∈ x := by
  constructor;
  · exact fun h x => x.mem_of_mem_logic h;
  · intro h;
    by_contra hφ;
    obtain ⟨x, hφx⟩ := exists_maximalConsistentSet_not_mem hφ;
    exact hφx <| h x;

/-- Classical tautologies belong to `L`.
- [CZ98, Theorem 1.16]
-/
@[grind <=]
theorem mem_of_isTautology (h : φ.IsTautology) : φ ∈ L :=
  mem_iff_forall_maximalConsistentSet.mpr fun x => h x.toBoolEval

lemma Consistent.nonempty_maximalConsistentSet (h : L.Consistent) :
    Nonempty L.MaximalConsistentSet := by
  obtain ⟨x, -⟩ := FormulaSet.lindenbaum
    <| FormulaSet.consistent_empty_iff.mpr
    <| consistent_iff_bot_not_mem.mp h;
  exact ⟨x⟩;

lemma consistent_iff_nonempty_maximalConsistentSet :
    L.Consistent ↔ Nonempty L.MaximalConsistentSet := by
  constructor;
  · exact Consistent.nonempty_maximalConsistentSet;
  · rintro ⟨x⟩;
    exact consistent_iff.mpr ⟨⊥, fun h => x.bot_not_mem <| x.mem_of_mem_logic h⟩;

/-- The canonical model of `L`: the worlds are the maximal `L`-consistent sets, `x ≺ y` iff
`◇φ ∈ x` for every `φ ∈ y`, and `#a` is true at `x` iff `#a ∈ x`.
- [CZ98, §5.1]
-/
def canonicalModel (L : NormalLogic α) : Model L.MaximalConsistentSet α where
  Rel' x y := ∀ φ ∈ y, ◇φ ∈ x
  Val' x a := #a ∈ x

namespace canonicalModel

variable {x y : L.canonicalModel.World}

omit [L.IsNExt 𝐊] in
lemma rel_def : x ≺ y ↔ ∀ φ ∈ y, ◇φ ∈ x := Iff.rfl

omit [L.IsNExt 𝐊] in
lemma val_def {a : α} : L.canonicalModel.Val x a ↔ #a ∈ x := Iff.rfl

lemma rel_iff_box : x ≺ y ↔ ∀ φ, □φ ∈ x → φ ∈ y := by
  constructor;
  · intro Rxy φ hA;
    by_contra hy;
    have h₁ : ◇(∼φ) ∈ x := Rxy _ <| y.neg_mem_of_not_mem hy;
    exact (x.neg_mem_iff.mp hA) h₁;
  · intro h φ hA;
    by_contra hx;
    have h₁ : □(∼φ) ∈ x :=
      x.mem_of_imp_mem (iff_mp neg_dia_iff_box_neg) <| x.neg_mem_of_not_mem hx;
    exact (y.neg_mem_iff.mp <| h _ h₁) hA;

/-- If `◇φ ∈ x`, then `x ≺ y` and `φ ∈ y` for some `y`.
- [CZ98, Lemma 5.2]
-/
lemma exists_rel_of_dia_mem (h : ◇φ ∈ x) : ∃ y, x ≺ y ∧ φ ∈ y := by
  have hc : (insert φ { ψ | □ψ ∈ x } : FormulaSet α).Consistent L := by
    intro hbot;
    have h₁ : x.carrier ⊢[L] □(∼φ) := by
      apply mono _ (box <| deduction hbot);
      rintro _ ⟨ψ, hB, rfl⟩;
      exact hB;
    have h₂ : ∼◇φ ∈ x :=
      x.mem_of_imp_mem (iff_mpr neg_dia_iff_box_neg) <| x.mem_of_derives h₁;
    exact (x.neg_mem_iff.mp h₂) h;
  obtain ⟨y, hsub⟩ := FormulaSet.lindenbaum hc;
  exact ⟨y, rel_iff_box.mpr fun ψ hB => hsub <| Set.mem_insert_of_mem _ hB,
    hsub <| Set.mem_insert φ _⟩;

/-- `x ⊩ φ` iff `φ ∈ x`.
- [CZ98, Theorem 5.4]
-/
theorem truthlemma : x ⊩ φ ↔ φ ∈ x := by
  induction φ generalizing x with
  | falsum => exact iff_of_false (Model.World.not_forces_bot) x.bot_not_mem;
  | atom a => tauto;
  | imp φ ψ ihφ ihψ =>
    grind [MaximalConsistentSet.imp_mem_iff];
  | dia φ ih =>
    rw [Model.World.forces_dia];
    constructor;
    · rintro ⟨y, Rxy, hy⟩;
      exact Rxy _ <| ih.mp hy;
    · intro h;
      obtain ⟨y, Rxy, hy⟩ := exists_rel_of_dia_mem h;
      use y;
      constructor;
      · assumption;
      · exact ih.mpr hy;

end canonicalModel

/-- `φ ∈ L` iff `φ` is valid in the canonical model of `L`.
- [CZ98, Theorem 5.5]
-/
theorem mem_iff_canonicalModel_validates : φ ∈ L ↔ L.canonicalModel ⊧ φ := by
  rw [mem_iff_forall_maximalConsistentSet];
  exact ⟨fun h x => canonicalModel.truthlemma.mpr <| h x,
    fun h x => canonicalModel.truthlemma.mp <| h x⟩;

lemma canonicalModel_validates_of_mem (h : φ ∈ L) : L.canonicalModel ⊧ φ :=
  mem_iff_canonicalModel_validates.mp h

lemma exists_world_not_forces (h : φ ∉ L) : ∃ x : L.canonicalModel.World, x ⊮ φ := by
  contrapose! h;
  apply mem_iff_canonicalModel_validates.mpr;
  apply h;

end NormalLogic

end
