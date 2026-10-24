module

public import BlokDichotomy.Propositional.Kripke.Basic
public import Mathlib.Order.Zorn

/-!
# Completeness of `𝐈𝐧𝐭` via the canonical model

Prime theories, the prime extension lemma, the canonical model of a superintuitionistic logic,
the truth lemma, and the completeness of `𝐈𝐧𝐭` for reflexive transitive frames.

## References

- [CZ98, Theorem 2.43, §5.1]
-/

@[expose] public section

universe v

namespace Propositional

namespace Logic

variable {α : Type v} {L : Logic α} {Γ : FormulaSet α} {A B : Formula α}

/-- A theory of `L` that is closed under derivability, omits `⊥`, and contains a disjunct of each
disjunction it contains: the first component of a maximal `L`-consistent tableau.
- [CZ98, §5.1] -/
@[ext]
structure PrimeTheory (L : Logic α) where
  carrier : FormulaSet α
  closed {A : Formula α} : carrier ⊢[L] A → A ∈ carrier
  bot_not_mem : ⊥ ∉ carrier
  prime {A B : Formula α} : A ⋎ B ∈ carrier → A ∈ carrier ∨ B ∈ carrier

namespace PrimeTheory

instance : SetLike L.PrimeTheory (Formula α) where
  coe x := x.carrier
  coe_injective _ _ h := PrimeTheory.ext h

variable {x : L.PrimeTheory}

@[grind →] lemma mem_of_derives (h : x.carrier ⊢[L] A) : A ∈ x := x.closed h

lemma mem_of_mem_logic (h : A ∈ L) : A ∈ x := x.closed <| Derives.thm h

@[grind =>]
lemma mem_mdp (h₁ : A ∈ x) (h₂ : A 🡒 B ∈ x) : B ∈ x :=
  x.closed <| Derives.mdp (Derives.mem h₁) (Derives.mem h₂)

@[grind =]
lemma and_mem_iff [L.IsExt 𝐈𝐧𝐭] : A ⋏ B ∈ x ↔ A ∈ x ∧ B ∈ x := by
  constructor;
  · intro h;
    exact ⟨x.mem_of_derives <| .and_left <| .mem h, x.mem_of_derives <| .and_right <| .mem h⟩;
  · rintro ⟨h₁, h₂⟩;
    exact x.mem_of_derives <| .and_intro (.mem h₁) (.mem h₂);

@[grind =]
lemma or_mem_iff [L.IsExt 𝐈𝐧𝐭] : A ⋎ B ∈ x ↔ A ∈ x ∨ B ∈ x := by
  constructor;
  · exact x.prime;
  · rintro (h | h);
    · exact x.mem_of_derives <| .or_inl <| .mem h;
    · exact x.mem_of_derives <| .or_inr <| .mem h;

end PrimeTheory

/-- If `A` is not derivable from `Γ`, then some prime theory contains `Γ` but not `A`.
- [CZ98, Lemma 5.1] -/
theorem exists_primeTheory [L.IsExt 𝐈𝐧𝐭] (h : Γ ⊬[L] A) :
    ∃ x : L.PrimeTheory, Γ ⊆ x.carrier ∧ A ∉ x := by
  obtain ⟨Δ, hΓΔ, hΔ⟩ := zorn_subset_nonempty { Δ : FormulaSet α | Γ ⊆ Δ ∧ Δ ⊬[L] A } (by
    intro c hc hchain hne;
    use ⋃₀ c;
    constructor;
    · constructor;
      · obtain ⟨Δ, hΔ⟩ := hne;
        exact (hc hΔ).1.trans <| Set.subset_sUnion_of_mem hΔ;
      · intro hd;
        obtain ⟨Θ, hΘ, hfin, hd'⟩ := hd.exists_finite;
        obtain ⟨t, ht, hΘt⟩ :=
          DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion hne hchain.directedOn hfin hΘ;
        exact (hc ht).2 <| hd'.mono hΘt;
    · intro s hs;
      exact Set.subset_sUnion_of_mem hs) Γ ⟨subset_rfl, h⟩;
  obtain ⟨hΓΔ', hΔA⟩ := hΔ.prop;
  have hmax : ∀ B, insert B Δ ⊬[L] A → B ∈ Δ := by
    intro B hB;
    exact hΔ.2 ⟨hΓΔ'.trans (Set.subset_insert B Δ), hB⟩ (Set.subset_insert B Δ)
      (Set.mem_insert B Δ);
  have hclosed : ∀ {B}, Δ ⊢[L] B → B ∈ Δ := by
    intro B hB;
    apply hmax;
    intro hd;
    exact hΔA <| .mdp hB <| .deduction hd;
  have hbot : ⊥ ∉ Δ := by
    by_contra hbot;
    exact hΔA <| .efq <| .mem hbot;
  have hprime : ∀ {B C : Formula α}, B ⋎ C ∈ Δ → B ∈ Δ ∨ C ∈ Δ := by
    intro B C hor;
    by_contra hn;
    push Not at hn;
    have h₁ : insert B Δ ⊢[L] A := by
      by_contra hd;
      exact hn.1 <| hmax B hd;
    have h₂ : insert C Δ ⊢[L] A := by
      by_contra hd;
      exact hn.2 <| hmax C hd;
    exact hΔA <| .or_elim (.mem hor) h₁ h₂;
  use ⟨Δ, hclosed, hbot, hprime⟩;
  constructor;
  · exact hΓΔ';
  · by_contra hA;
    exact hΔA <| .mem hA;

/-- The canonical model of `L`: the worlds are the prime theories of `L`, ordered by inclusion,
and `#a` is true at `x` iff `#a ∈ x`.
- [CZ98, §5.1] -/
def canonicalModel (L : Logic α) : Model L.PrimeTheory α where
  toFrame := ⟨fun x y => x.carrier ⊆ y.carrier⟩
  Val x a := (#a : Formula α) ∈ x
  hereditary Rxy _ h := Rxy h

namespace canonicalModel

instance : IsPreorder L.PrimeTheory L.canonicalModel.Rel where
  refl _ := subset_rfl
  trans _ _ _ := subset_trans

variable [L.IsExt 𝐈𝐧𝐭] {x : L.canonicalModel.World}

/-- `x ⊩ A` iff `A ∈ x`.
- [CZ98, Theorem 5.4] -/
theorem truthlemma : x ⊩ A ↔ A ∈ x := by
  induction A generalizing x with
  | atom a => exact Iff.rfl;
  | falsum => exact iff_of_false Model.World.not_forces_bot x.bot_not_mem;
  | imp A B ihA ihB =>
    constructor;
    · intro h;
      by_contra hn;
      have hnd : insert A x.carrier ⊬[L] B := by
        by_contra hd;
        exact hn <| x.mem_of_derives <| Derives.deduction hd;
      obtain ⟨y, hy, hBy⟩ := exists_primeTheory hnd;
      have hxy : L.canonicalModel.Rel x y := fun _ hz => hy <| Set.mem_insert_of_mem A hz;
      exact hBy <| ihB.mp <| h y hxy <| ihA.mpr <| hy <| Set.mem_insert A x.carrier;
    · intro h y hxy hAy;
      exact ihB.mpr <| y.mem_mdp (ihA.mp hAy) <| hxy h;
  | _ => grind;

end canonicalModel

/-- `A ∈ L` iff `A` is valid in the canonical model of `L`.
- [CZ98, Theorem 5.5] -/
theorem mem_iff_canonicalModel_validates [L.IsExt 𝐈𝐧𝐭] : A ∈ L ↔ L.canonicalModel ⊧ A := by
  constructor;
  · intro h x;
    exact canonicalModel.truthlemma.mpr <| x.mem_of_mem_logic h;
  · intro h;
    by_contra hn;
    have hnd : ∅ ⊬[L] A := by
      by_contra hd;
      exact hn <| Derives.empty_iff.mp hd;
    obtain ⟨x, -, hx⟩ := exists_primeTheory hnd;
    exact hx <| canonicalModel.truthlemma.mp <| h x;

end Logic

/-- `𝐈𝐧𝐭` is sound and complete for the reflexive transitive frames.
- [CZ98, Theorem 2.43] -/
theorem mem_logicInt_iff {α : Type v} {A : Formula α} :
    A ∈ 𝐈𝐧𝐭 ↔ ∀ (κ : Type v) (F : Frame κ) [IsPreorder _ F.Rel], F ⊧ A := by
  constructor;
  · intro h κ F _;
    exact Frame.validates_of_mem_logicInt h;
  · intro h;
    apply Logic.mem_iff_canonicalModel_validates.mpr;
    exact h (logicInt (α := α)).PrimeTheory (logicInt (α := α)).canonicalModel.toFrame
      (logicInt (α := α)).canonicalModel.Val (logicInt (α := α)).canonicalModel.hereditary;

end Propositional

end
