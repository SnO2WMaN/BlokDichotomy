module

public import BlokDichotomy.Kripke.Completeness
public import BlokDichotomy.Logic.Restrict

/-!
# Conjunctive normal forms

Every `◇`-free formula is equivalent in `𝐊`, under every substitution, to a conjunction of
clauses over a finite set of variables containing its atoms. The clauses are read off a truth
table.

This is a folklore fact of classical propositional logic.
-/

@[expose] public section

universe u

namespace Formula

variable {ι : Type u} {A B : Formula ι}

/-- Evaluation of a `◇`-free formula under a truth assignment to its atoms; `◇`-formulas are
evaluated to `False`. -/
def evalAtoms (ε : ι → Prop) : Formula ι → Prop
  | #a => ε a
  | ⊥ => False
  | A 🡒 B => evalAtoms ε A → evalAtoms ε B
  | ◇_ => False

@[simp] lemma evalAtoms_atom {ε : ι → Prop} {a : ι} : evalAtoms ε (#a) = ε a := rfl
@[simp] lemma evalAtoms_bot {ε : ι → Prop} : evalAtoms ε (⊥ : Formula ι) = False := rfl
@[simp] lemma evalAtoms_imp {ε : ι → Prop} :
    evalAtoms ε (A 🡒 B) = (evalAtoms ε A → evalAtoms ε B) := rfl

lemma evalAtoms_congr [DecidableEq ι] {ε ε' : ι → Prop} (h : ∀ a ∈ A.atoms, ε a ↔ ε' a) :
    evalAtoms ε A ↔ evalAtoms ε' A := by
  induction A with
  | atom a => exact h a (by simp);
  | falsum => exact Iff.rfl;
  | imp A B ihA ihB =>
    simp only [evalAtoms_imp];
    rw [ihA fun a ha => h a (by simp [ha]), ihB fun a ha => h a (by simp [ha])];
  | dia A ih => exact Iff.rfl;

/-- A Boolean evaluation of a `◇`-free formula is determined by its values on the atoms. -/
lemma BoolEval.eval_iff_evalAtoms (v : BoolEval ι) (h : A.depth = 0) :
    v A ↔ evalAtoms (fun a => v (#a)) A := by
  induction A with
  | atom a => exact Iff.rfl;
  | falsum => simp;
  | imp A B ihA ihB =>
    simp only [depth_imp, Nat.max_eq_zero_iff] at h;
    rw [BoolEval.eval_imp, ihA h.1, ihB h.2, evalAtoms_imp];
  | dia A ih => simp at h;

open Classical in
/-- The subsets `I` of `s` such that `A` is false under the assignment making exactly the
variables in `I` true. -/
noncomputable def refutingSets (s : Finset ι) (A : Formula ι) : Finset (Finset ι) :=
  s.powerset.filter fun I => ¬ evalAtoms (· ∈ I) A

lemma mem_refutingSets {s : Finset ι} {I : Finset ι} :
    I ∈ refutingSets s A ↔ I ⊆ s ∧ ¬ evalAtoms (· ∈ I) A := by
  simp [refutingSets]

variable [DecidableEq ι] {s : Finset ι}

/-- The conjunction of one clause for each assignment on `s` that refutes `A`: the clause for `I`
says that the variables in `I` are not all true or some variable of `s \ I` is true. -/
noncomputable def cnf (s : Finset ι) (A : Formula ι) : Formula ι :=
  ⋀ ((refutingSets s A).toList.map
    fun I => ⋀ (I.toList.map (#·)) 🡒 ⋁ ((s \ I).toList.map (#·)))

/-- A truth assignment satisfies `A` iff it satisfies every clause of `A.cnf s`. -/
lemma evalAtoms_iff_forall_clause (hA : A.atoms ⊆ s) (ε : ι → Prop) :
    evalAtoms ε A ↔
      ∀ I ∈ s.powerset, ¬ evalAtoms (· ∈ I) A → (∀ a ∈ I, ε a) → ∃ a ∈ s \ I, ε a := by
  classical
  constructor;
  · intro h I hI hnI hε;
    by_contra hex;
    push Not at hex;
    apply hnI;
    rw [Finset.mem_powerset] at hI;
    rw [evalAtoms_congr (ε' := ε)];
    · exact h;
    · intro a ha;
      by_cases haI : a ∈ I;
      · exact ⟨fun _ => hε a haI, fun _ => haI⟩;
      · exact ⟨fun h' => absurd h' haI, fun h' => absurd h' (hex a (Finset.mem_sdiff.mpr
          ⟨hA ha, haI⟩))⟩;
  · intro h;
    by_contra hε;
    have h₁ := h (s.filter ε) (Finset.mem_powerset.mpr (Finset.filter_subset _ _));
    have h₂ : ¬ evalAtoms (· ∈ s.filter ε) A := by
      rw [evalAtoms_congr (ε' := ε)];
      · exact hε;
      · intro a ha;
        simp [hA ha];
    obtain ⟨a, ha, haε⟩ := h₁ h₂ (fun a ha => (Finset.mem_filter.mp ha).2);
    rw [Finset.mem_sdiff, Finset.mem_filter] at ha;
    exact ha.2 ⟨ha.1, haε⟩;

lemma depth_cnf : (A.cnf s).depth = 0 := by
  classical
  apply depth_conj_eq_zero;
  intro B hB;
  obtain ⟨I, -, rfl⟩ := List.mem_map.mp hB;
  simp only [depth_imp, Nat.max_eq_zero_iff];
  constructor;
  · apply depth_conj_eq_zero;
    intro C hC;
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hC;
    rfl;
  · apply depth_disj_eq_zero;
    intro C hC;
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hC;
    rfl;

/-- A `◇`-free formula is Boolean-equivalent to its conjunctive normal form. -/
theorem isTautology_iff_cnf (h : A.depth = 0) (hA : A.atoms ⊆ s) :
    (A 🡘 A.cnf s).IsTautology := by
  classical
  intro v;
  rw [BoolEval.eval_iff, BoolEval.eval_iff_evalAtoms v h,
    evalAtoms_iff_forall_clause hA];
  rw [cnf, BoolEval.eval_conj];
  constructor;
  · intro H B hB;
    obtain ⟨I, hI, rfl⟩ := List.mem_map.mp hB;
    rw [Finset.mem_toList, mem_refutingSets] at hI;
    rw [BoolEval.eval_imp, BoolEval.eval_conj, BoolEval.eval_disj];
    intro h₁;
    obtain ⟨a, ha, hva⟩ := H I (Finset.mem_powerset.mpr hI.1) hI.2 fun a ha =>
      h₁ _ (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩);
    exact ⟨#a, List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩, hva⟩;
  · intro H I hI hnI h₁;
    have h₂ := H _ <| List.mem_map.mpr
      ⟨I, Finset.mem_toList.mpr (mem_refutingSets.mpr ⟨Finset.mem_powerset.mp hI, hnI⟩), rfl⟩;
    rw [BoolEval.eval_imp, BoolEval.eval_conj, BoolEval.eval_disj] at h₂;
    obtain ⟨B, hB, hvB⟩ := h₂ fun B hB => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hB;
      exact h₁ a (Finset.mem_toList.mp ha);
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hB;
    exact ⟨a, Finset.mem_toList.mp ha, hvB⟩;

/-- The substitution instances of a `◇`-free formula and of its conjunctive normal form are
equivalent in every normal logic. -/
theorem cnf_iff_mem {α : Type*} {L : NormalLogic α} [L.IsNExt 𝐊] (h : A.depth = 0)
    (hA : A.atoms ⊆ s) (σ : Substitution ι α) : A⟦σ⟧ 🡘 (A.cnf s)⟦σ⟧ ∈ L :=
  NormalLogic.mem_of_mem_logicK <| NormalLogic.mem_logicK_subst σ <|
    NormalLogic.mem_of_isTautology (isTautology_iff_cnf h hA)

lemma subst_cnf {α : Type*} (σ : Substitution ι α) :
    (A.cnf s)⟦σ⟧ = ⋀ ((refutingSets s A).toList.map
      fun I => ⋀ (I.toList.map σ) 🡒 ⋁ ((s \ I).toList.map σ)) := by
  simp [cnf, List.map_map, Function.comp_def]

end Formula

namespace NormalLogic

variable {α ι : Type*} {L : NormalLogic α} [L.IsNExt 𝐊] {l : List ι} {f g : ι → Formula α}

lemma conj_map_iff_congr (h : ∀ i ∈ l, f i 🡘 g i ∈ L) :
    ⋀ (l.map f) 🡘 ⋀ (l.map g) ∈ L := by
  induction l with
  | nil => exact iff_refl;
  | cons i l ih =>
    simp only [List.map_cons, Formula.conj_cons];
    exact and_iff_congr (h i List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem _ hj));

lemma disj_map_iff_congr (h : ∀ i ∈ l, f i 🡘 g i ∈ L) :
    ⋁ (l.map f) 🡘 ⋁ (l.map g) ∈ L := by
  induction l with
  | nil => exact iff_refl;
  | cons i l ih =>
    simp only [List.map_cons, Formula.disj_cons];
    exact or_iff_congr (h i List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem _ hj));

end NormalLogic

end
