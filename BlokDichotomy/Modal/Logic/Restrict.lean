module

public import BlokDichotomy.Modal.Formula
public import BlokDichotomy.Modal.Logic.Basic

/-!
# Restricting a normal logic to fewer variables

`L.comap f hf` is the normal logic over `β` of the formulas whose renaming along an injection
`f : β → α` lies in `L`, and `L.restrict n` is its instance for `Fin.val : Fin n → ℕ`.

## References

- [CZ98, §10.5]
-/

@[expose] public section

namespace Modal

namespace FormulaSet

variable {α β : Type*} {φ : Formula α}

lemma axiomsK.subst (s : Formula.Substitution α β) (h : φ ∈ axiomsK) : φ⟦s⟧ ∈ axiomsK := by
  cases h <;> simp only [Formula.subst_imp, Formula.subst_dia, Formula.subst_bot] <;> constructor

end FormulaSet


namespace NormalLogic

open Formula

variable {α β : Type*} {φ : Formula α}

lemma mem_logicK_subst (s : Substitution α β) (h : φ ∈ 𝐊) : φ⟦s⟧ ∈ 𝐊 := by
  induction h generalizing β with
  | mem h => exact mem_ofSet <| FormulaSet.axiomsK.subst s h;
  | mdp _ _ ihφ ihφψ => exact mem_mdp (ihφ s) (ihφψ s);
  | nec _ ih => exact mem_nec (ih s);
  | subst _ ih => rw [subst_subst]; exact ih _;

lemma mem_logicK_map (f : α → β) (h : φ ∈ 𝐊) : φ.map f ∈ 𝐊 :=
  mem_logicK_subst _ h

variable (L : NormalLogic α) (f : β → α) (hf : Function.Injective f)

/--
The formulas `φ` over `β` with `φ.map f ∈ L`.
- [CZ98, §10.5]
-/
def comap : NormalLogic β where
  carrier := { φ | φ.map f ∈ L }
  mdp {_ _} hA hAB := L.mdp hA hAB
  nec {_} h := L.nec h
  subst {φ s} h := by
    classical
    let τ : Substitution α α := fun a => if h : ∃ b, f b = a then (s h.choose).map f else #a;
    have hτ : (fun b => τ (f b)) = fun b => (s b).map f := by
      funext b;
      have h₁ : ∃ b', f b' = f b := ⟨b, rfl⟩;
      simp only [τ, h₁, dite_true];
      rw [hf h₁.choose_spec];
    have h₂ : (φ.map f)⟦τ⟧ ∈ L := L.subst h;
    rw [subst_map, hτ, ← map_subst] at h₂;
    exact h₂;

variable {L f hf}

@[simp] lemma mem_comap_iff {φ : Formula β} : φ ∈ L.comap f hf ↔ φ.map f ∈ L := Iff.rfl

instance [L.IsNExt 𝐊] : (L.comap f hf).IsNExt 𝐊 :=
  ⟨fun φ h => show φ.map f ∈ L from mem_of_mem_logicK <| mem_logicK_map f h⟩

lemma subst_mem_comap (h : φ ∈ L) (s : Substitution α β) : φ⟦s⟧ ∈ L.comap f hf := by
  rw [mem_comap_iff, map_subst];
  exact L.subst h;

lemma comap_mono {L₁ L₂ : NormalLogic α} (h : L₁ ≤ L₂) : L₁.comap f hf ≤ L₂.comap f hf :=
  fun _ hB => h hB

lemma Consistent.comap [L.IsNExt 𝐊] (h : L.Consistent) : (L.comap f hf).Consistent := by
  rw [consistent_iff_bot_not_mem] at h ⊢;
  exact h;

/--
The formulas over `Fin n` whose renaming along `Fin.val` lies in `L`.
- [CZ98, §10.5]
-/
abbrev restrict (L : NormalLogic ℕ) (n : ℕ) : NormalLogic (Fin n) :=
  L.comap Fin.val Fin.val_injective

lemma mem_restrict_iff {L : NormalLogic ℕ} {n : ℕ} {φ : Formula (Fin n)} :
    φ ∈ L.restrict n ↔ φ.map Fin.val ∈ L := Iff.rfl

lemma subst_mem_restrict {L : NormalLogic ℕ} {n : ℕ} {φ : Formula ℕ} (h : φ ∈ L)
    (s : Substitution ℕ (Fin n)) : φ⟦s⟧ ∈ L.restrict n :=
  subst_mem_comap h s

end NormalLogic

end Modal

end
