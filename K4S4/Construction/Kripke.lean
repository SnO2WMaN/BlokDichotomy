module

public import K4S4.Construction.Basic
public import BlokDichotomy.ToMathlib.Order.Monotone.Basic

/-!
# Kripke equivalence of the indexed extensions

The chain axiom excludes an infinite strict chain in every validating Kripke frame.
The transition axioms consequently make the root formula false throughout such a frame.
-/

@[expose] public section

namespace Modal.K4S4.Construction

open Model.World NormalLogic

universe u

variable {κ : Type u} {F : Frame κ}

private def alternatingVal (f : ℕ → F.World) (x : F.World) : ℕ → Prop
  | 3 => ∃ n, x = f (2 * n)
  | 4 => ∃ n, x = f (2 * n + 1)
  | _ => False

private lemma not_even_at_odd {f : ℕ → F.World} (hf : Function.Injective f) (n : ℕ) :
    ¬alternatingVal f (f (2 * n + 1)) 3 := by
  rintro ⟨m, hm⟩;
  have := hf hm;
  omega;

lemma not_validates_sigma_of_chain {f : ℕ → F.World}
    (hR : ∀ n, f n ≺ f (n + 1)) (hf : Function.Injective f) : F ⊭ sigma := by
  intro h;
  apply h (alternatingVal f) (f 0);
  simp only [forces_and, forces_box];
  have h₁ : ∀ n, f (2 * n) ⊩[⟨F, alternatingVal f⟩] ◇(∼#3 ⋏ #4) := by
    intro n;
    exact forces_dia.mpr ⟨f (2 * n + 1), hR _,
      forces_and.mpr ⟨not_even_at_odd hf n, n, rfl⟩⟩;
  have h₂ : ∀ n, f (2 * n + 1) ⊩[⟨F, alternatingVal f⟩] ◇#3 := by
    intro n;
    use f (2 * n + 2);
    exact ⟨hR _, n + 1, rfl⟩;
  and_intros;
  · exact ⟨0, rfl⟩;
  · rintro ⟨n, hn⟩;
    rw [hn];
    exact h₁ n;
  · rintro x _ ⟨n, rfl⟩;
    exact h₁ n;
  · intro h;
    obtain ⟨_, n, hn⟩ := forces_and.mp h;
    rw [hn];
    exact h₂ n;
  · intro x _ h;
    obtain ⟨_, n, hn⟩ := forces_and.mp h;
    rw [hn];
    exact h₂ n;

lemma validates_not_nameR_of_baseLogic (hF : F ⊧ baseLogic) : F ⊧ ∼nameR := by
  obtain ⟨_, _⟩ := Frame.validates_logicS4_iff.mp
    (fun A hA => hF A <| NormalLogic.le_add hA);
  intro V x hx;
  obtain ⟨z, hxz, hz⟩ := (forces_and.mp <| (forces_and.mp <|
    (forces_and.mp <| (forces_and.mp hx).2).2).2).2;
  obtain ⟨f, _, hf⟩ := exists_seq_of_forall_exists_rel
    (r := fun y z : F.World => y ≺ z ∧ z ⊀ y)
    (P := fun n z => x ≺ z ∧ z ⊩[⟨F, V⟩] nameY n) ⟨hxz, hz⟩ <| by
      intro n y hy;
      have hθ := forces_box.mp (hF (theta n)
        (NormalLogic.mem_add <| Set.mem_insert_of_mem _ ⟨n, rfl⟩) V x hx) y hy.1 hy.2;
      obtain ⟨z, hyz, hz⟩ := forces_dia.mp hθ;
      obtain ⟨hzy, hneg⟩ := forces_and.mp hz;
      exact ⟨z, ⟨hyz, fun h => forces_neg.mp hneg ⟨y, h, hy.2⟩⟩,
        Frame.rel_trans hy.1 hyz, hzy⟩;
  have hR : ∀ n, f n ≺ f (n + 1) := fun n => (hf n).2.1;
  exact not_validates_sigma_of_chain hR
    (injective_of_forall_rel_succ hR fun n => (hf n).2.2)
    (hF sigma <| NormalLogic.mem_add <| Set.mem_insert _ _);

lemma validates_chi_of_baseLogic (hF : F ⊧ baseLogic) (n : ℕ) : F ⊧ chi n :=
  fun V x hx => False.elim <| validates_not_nameR_of_baseLogic hF V x hx

lemma chi_mem_frameLogic (n : ℕ) :
    chi n ∈ baseLogic.frameLogic.{u} (fun _ _ => True) :=
  fun _ _ _ hF => validates_chi_of_baseLogic hF n

lemma sourceLogic_frameEquiv (I : Set ℕ) :
    FrameEquiv.{u} (fun _ _ => True) (sourceLogic I)
      (baseLogic.frameLogic.{u} (fun _ _ => True)) := by
  apply FrameEquiv.trans (L₂ := baseLogic) _ NormalLogic.frameEquiv_frameLogic;
  intro κ F _;
  constructor;
  · exact fun hF A hA => hF A <| NormalLogic.le_add hA;
  · intro hF;
    apply Frame.validates_add hF;
    rintro _ ⟨n, _, rfl⟩;
    exact validates_chi_of_baseLogic hF n;

end Modal.K4S4.Construction
