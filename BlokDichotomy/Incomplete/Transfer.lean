module

public import BlokDichotomy.Incomplete.Hooked
public import BlokDichotomy.Formula

/-!
# Refutations survive the hooking

The valuation `D.liftVal I V` on the hooked frame, and truth of formulas of bounded modal depth
under it.

## References

- [Blok78, Theorem 4.6]
- [CZ98, Proposition 3.2]
-/

@[expose] public section

universe u

namespace HookData

open Formula Model.World

variable {κ : Type u} {D : HookData κ} {I : Set ℕ} {α : Type*}

section Unwind

variable (D) in
def unwindRel : D.F.World ⊕ Fin (D.len + 1) → D.F.World ⊕ Fin (D.len + 1) → Prop
  | .inl u, .inl v => u ≺ v
  | .inl u, .inr t => u = D.path 0 ∧ t.1 = 0
  | .inr t, .inl v => D.path (t.1 + 1) ≺ v
  | .inr t, .inr t' => t'.1 = t.1 + 1

variable (D) in
/-- The frame on `D.F.World ⊕ Fin (D.len + 1)` with relation `D.unwindRel`.
- [CZ98, Fig. 10.4]
-/
def unwind : Frame (D.F.World ⊕ Fin (D.len + 1)) := ⟨D.unwindRel⟩

variable (D) in
/-- The p-morphism `D.unwind →ₚ D.F`.
- [CZ98, Fig. 10.4]
-/
def unwindProj : D.unwind →ₚ D.F where
  toFun
    | .inl u => u
    | .inr t => D.path (t.1 + 1)
  forth {x y} h := by
    rcases x with u | t <;> rcases y with v | t';
    · exact h;
    · obtain ⟨rfl, ht'⟩ := h;
      simpa [ht'] using D.path_rel 0;
    · exact h;
    · have ht' : t'.1 = t.1 + 1 := h;
      simpa [ht'] using D.path_rel (t.1 + 1);
  back {x z} h := by
    rcases x with u | t <;> exact ⟨.inl z, h, rfl⟩

lemma unwindProj_surjective : Function.Surjective (D.unwindProj) := fun u => ⟨.inl u, rfl⟩

lemma validates_of_unwind_validates {L : NormalLogic α} (h : D.unwind ⊧ L) : D.F ⊧ L :=
  Frame.ValidateLogic.of_surjective_pMorphism D.unwindProj unwindProj_surjective h

end Unwind


variable (D I) in
def liftVal (V : D.F.World → α → Prop) : D.World I → α → Prop
  | .base u, a => V u a
  | .copy t _, a => V (D.path (t + 1)) a
  | _, _ => False

lemma isAdmissible_liftVal (V : D.F.World → α → Prop) :
    (D.hooked I).IsAdmissible (D.liftVal I V) := by
  intro a;
  apply mem_adm_of_forall;
  intro w hw;
  cases w <;> simp_all [liftVal, World.IsA];

section Transfer

variable [DecidableEq α]

/-- If `V'` agrees with `V` on `.base u` and `.copy t _` for the atoms of `φ`, then
`.base u ⊩ φ ↔ u ⊩ φ` when `φ.depth ≤ D.len + 1`, and
`.copy t _ ⊩ φ ↔ D.path (t + 1) ⊩ φ` when `φ.depth + t ≤ D.len`.
- [Blok78, Theorem 4.6]
- [CZ98, Proposition 3.2]
-/
theorem forces_transfer {P : α → Prop} {V : D.F.World → α → Prop} {V' : D.World I → α → Prop}
    (hbase : ∀ u a, P a → (V' (.base u) a ↔ V u a))
    (hcopy : ∀ t ht a, P a → (V' (.copy t ht) a ↔ V (D.path (t + 1)) a))
    {φ : Formula α} (hA : ∀ a ∈ φ.atoms, P a) :
    (∀ u, φ.depth ≤ D.len + 1 →
      ((.base u : D.World I) ⊩[(D.hooked I).model V'] φ ↔ u ⊩[⟨D.F, V⟩] φ)) ∧
    (∀ t ht, φ.depth + t ≤ D.len →
      ((.copy t ht : D.World I) ⊩[(D.hooked I).model V'] φ ↔ D.path (t + 1) ⊩[⟨D.F, V⟩] φ)) := by
  induction φ with
  | atom a =>
    have ha : P a := hA a <| by simp;
    exact ⟨fun u _ => hbase u a ha, fun t ht _ => hcopy t ht a ha⟩;
  | falsum => exact ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩;
  | imp φ ψ ihφ ihψ =>
    obtain ⟨hA₁, hA₂⟩ := ihφ fun a ha => hA a <| by simp [ha];
    obtain ⟨hB₁, hB₂⟩ := ihψ fun a ha => hA a <| by simp [ha];
    constructor;
    · intro u hu;
      simp only [depth_imp, sup_le_iff] at hu;
      exact imp_congr (hA₁ u hu.1) (hB₁ u hu.2);
    · intro t ht h;
      simp only [depth_imp] at h;
      exact imp_congr (hA₂ t ht <| by omega) (hB₂ t ht <| by omega);
  | dia φ ih =>
    obtain ⟨h₁, h₂⟩ := ih hA;
    simp only [depth_dia];
    constructor;
    · intro u hu;
      constructor;
      · rintro ⟨y, hy, hyA⟩;
        rcases rel_base_iff.mp hy with ⟨v, rfl, Ruv⟩ | ⟨rfl, rfl⟩;
        · exact ⟨v, Ruv, (h₁ v <| by omega).mp hyA⟩;
        · exact ⟨D.path 1, D.path_rel 0, (h₂ 0 _ <| by omega).mp hyA⟩;
      · rintro ⟨v, Ruv, hv⟩;
        exact ⟨.base v, Ruv, (h₁ v <| by omega).mpr hv⟩;
    · intro t ht h;
      constructor;
      · rintro ⟨y, hy, hyA⟩;
        rcases rel_copy_iff.mp hy with ⟨v, rfl, hv⟩ | ⟨ht', rfl⟩ | ⟨rfl, -⟩;
        · exact ⟨v, hv, (h₁ v <| by omega).mp hyA⟩;
        · exact ⟨D.path (t + 1 + 1), D.path_rel (t + 1), (h₂ (t + 1) ht' <| by omega).mp hyA⟩;
        · omega;
      · rintro ⟨v, hv, hvA⟩;
        exact ⟨.base v, hv, (h₁ v <| by omega).mpr hvA⟩;

end Transfer

/-- If `φ.depth ≤ D.len + 1`, then `.base u ⊩ φ` under `D.liftVal I V` iff `u ⊩ φ` under `V`.
- [Blok78, Theorem 4.6]
- [CZ98, Proposition 3.2]
-/
theorem forces_liftVal_base_iff {V : D.F.World → α → Prop} {φ : Formula α}
    (hA : φ.depth ≤ D.len + 1) (u : D.F.World) :
    (.base u : D.World I) ⊩[(D.hooked I).model (D.liftVal I V)] φ ↔ u ⊩[⟨D.F, V⟩] φ := by
  classical
  exact (forces_transfer (P := fun _ => True) (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (fun _ _ => trivial)).1 u hA

end HookData

end
