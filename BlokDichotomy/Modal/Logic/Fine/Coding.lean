module

public import BlokDichotomy.Modal.Logic.Fine

/-!
# Fine's frame with coding points

Fine's frame `fineFrame` extended, for a set `I` of natural numbers, by the points `t_i` which
code the elements of `I`, and the proof that a valuation satisfying a handful of pinning
conditions at a point is forced to behave as in Fine's model.

## References

- [Fin74a]
-/

@[expose] public section

namespace Modal

namespace Fine

open Formula Model.World

section

variable {κ : Type*} {M : Model κ ℕ} {x : M.World} {j : ℕ} [IsTrans _ M.Rel] [Std.Refl M.Rel]

lemma exists_forces_atom₃_of_forces_β (h : x ⊩ β (j + 1)) : ∃ y, x ≺ y ∧ y ⊩ #3 := by
  induction j generalizing x with
  | zero => exact ⟨x, Frame.rel_refl x, by simpa using h⟩
  | succ j ih =>
    rw [β_add_two, forces_and, forces_and] at h;
    obtain ⟨y, Rxy, hy⟩ := forces_dia.mp h.1;
    obtain ⟨z, Ryz, hz⟩ := ih hy;
    exact ⟨z, Frame.rel_trans Rxy Ryz, hz⟩

lemma exists_forces_atom₅_of_forces_γ (h : x ⊩ γ (j + 1)) : ∃ y, x ≺ y ∧ y ⊩ #5 := by
  induction j generalizing x with
  | zero => exact ⟨x, Frame.rel_refl x, by simpa using h⟩
  | succ j ih =>
    rw [γ_add_two, forces_and, forces_and] at h;
    obtain ⟨y, Rxy, hy⟩ := forces_dia.mp h.1;
    obtain ⟨z, Ryz, hz⟩ := ih hy;
    exact ⟨z, Frame.rel_trans Rxy Ryz, hz⟩

end

/-- The formula `η_i`, true at the points that see an `α_i`- and an `α_{i+1}`-point but no
`α_{i+2}`-point. -/
def η (i : ℕ) : Formula ℕ := ◇(α i) ⋏ ◇(α (i + 1)) ⋏ ∼◇(α (i + 2))

lemma forces_η_iff {κ : Type*} {M : Model κ ℕ} {x : M.World} {i : ℕ} :
    x ⊩ η i ↔ x ⊩ ◇(α i) ∧ x ⊩ ◇(α (i + 1)) ∧ x ⊩ ∼◇(α (i + 2)) := by
  simp only [η, forces_and]

end Fine

/-- Fine's frame extended by the points `t_i = (4, i)`; `t_i` sees `a_i`, `a_{i+1}` and the `b`-
and `c`-points up to level `i + 2` when `i ∈ I`, and is an isolated reflexive point otherwise.

- [Fin74a, p. 25] -/
abbrev codingFrame (I : Set ℕ) : Frame (Fin 5 × ℕ) := ⟨fun
  | (1, m), (1, k) => k ≤ m
  | (1, m), (2, k) => k + 2 ≤ m
  | (2, m), (2, k) => k ≤ m
  | (2, m), (1, k) => k + 2 ≤ m
  | (0, m), (0, k) => k = m
  | (0, m), (1, k) => k ≤ m + 1
  | (0, m), (2, k) => k ≤ m + 1
  | (3, n), (3, k) => n ≤ k
  | (3, n), (0, m) => n ≤ m
  | (3, _), (1, _) => True
  | (3, _), (2, _) => True
  | (3, n), (4, i) => i ∈ I ∧ n ≤ i
  | (4, i), (4, k) => k = i
  | (4, i), (0, k) => i ∈ I ∧ (k = i ∨ k = i + 1)
  | (4, i), (1, k) => i ∈ I ∧ k ≤ i + 2
  | (4, i), (2, k) => i ∈ I ∧ k ≤ i + 2
  | _, _ => False⟩

namespace codingFrame

open Fine Model.World

variable {I : Set ℕ} {x y z : (codingFrame I).World} {m k n i : ℕ}

/-- The five families of points of the coding frame. -/
@[simp, match_pattern] abbrev a (m : ℕ) : (codingFrame I).World := (0, m)
@[simp, match_pattern] abbrev b (m : ℕ) : (codingFrame I).World := (1, m)
@[simp, match_pattern] abbrev c (m : ℕ) : (codingFrame I).World := (2, m)
@[simp, match_pattern] abbrev d (m : ℕ) : (codingFrame I).World := (3, m)
@[simp, match_pattern] abbrev t (m : ℕ) : (codingFrame I).World := (4, m)

/-- Case analysis on the points of the coding frame. -/
@[elab_as_elim]
theorem casesOn {P : (codingFrame I).World → Prop} (x : (codingFrame I).World)
    (a : ∀ m, P (codingFrame.a m)) (b : ∀ m, P (codingFrame.b m))
    (c : ∀ m, P (codingFrame.c m)) (d : ∀ m, P (codingFrame.d m))
    (t : ∀ m, P (codingFrame.t m)) : P x := by
  obtain ⟨⟨_ | _ | _ | _ | _ | i, hi⟩, m⟩ := x
  · exact a m
  · exact b m
  · exact c m
  · exact d m
  · exact t m
  · omega

@[simp] lemma not_rel_iff : x ⊀ y ↔ ¬ x ≺ y := Iff.rfl

@[simp] lemma rel_a_a : ((a m : (codingFrame I).World) ≺ a k) ↔ k = m := Iff.rfl
@[simp] lemma rel_a_b : ((a m : (codingFrame I).World) ≺ b k) ↔ k ≤ m + 1 := Iff.rfl
@[simp] lemma rel_a_c : ((a m : (codingFrame I).World) ≺ c k) ↔ k ≤ m + 1 := Iff.rfl
@[simp] lemma rel_a_d : (a m : (codingFrame I).World) ⊀ d k := id
@[simp] lemma rel_a_t : (a m : (codingFrame I).World) ⊀ t k := id
@[simp] lemma rel_b_a : (b m : (codingFrame I).World) ⊀ a k := id
@[simp] lemma rel_b_b : ((b m : (codingFrame I).World) ≺ b k) ↔ k ≤ m := Iff.rfl
@[simp] lemma rel_b_c : ((b m : (codingFrame I).World) ≺ c k) ↔ k + 2 ≤ m := Iff.rfl
@[simp] lemma rel_b_d : (b m : (codingFrame I).World) ⊀ d k := id
@[simp] lemma rel_b_t : (b m : (codingFrame I).World) ⊀ t k := id
@[simp] lemma rel_c_a : (c m : (codingFrame I).World) ⊀ a k := id
@[simp] lemma rel_c_b : ((c m : (codingFrame I).World) ≺ b k) ↔ k + 2 ≤ m := Iff.rfl
@[simp] lemma rel_c_c : ((c m : (codingFrame I).World) ≺ c k) ↔ k ≤ m := Iff.rfl
@[simp] lemma rel_c_d : (c m : (codingFrame I).World) ⊀ d k := id
@[simp] lemma rel_c_t : (c m : (codingFrame I).World) ⊀ t k := id
@[simp] lemma rel_d_a : ((d n : (codingFrame I).World) ≺ a m) ↔ n ≤ m := Iff.rfl
@[simp] lemma rel_d_b : (d n : (codingFrame I).World) ≺ b k := trivial
@[simp] lemma rel_d_c : (d n : (codingFrame I).World) ≺ c k := trivial
@[simp] lemma rel_d_d : ((d n : (codingFrame I).World) ≺ d k) ↔ n ≤ k := Iff.rfl
@[simp] lemma rel_d_t : ((d n : (codingFrame I).World) ≺ t i) ↔ i ∈ I ∧ n ≤ i := Iff.rfl
@[simp] lemma rel_t_a : ((t i : (codingFrame I).World) ≺ a k) ↔ i ∈ I ∧ (k = i ∨ k = i + 1) :=
  Iff.rfl
@[simp] lemma rel_t_b : ((t i : (codingFrame I).World) ≺ b k) ↔ i ∈ I ∧ k ≤ i + 2 := Iff.rfl
@[simp] lemma rel_t_c : ((t i : (codingFrame I).World) ≺ c k) ↔ i ∈ I ∧ k ≤ i + 2 := Iff.rfl
@[simp] lemma rel_t_d : (t i : (codingFrame I).World) ⊀ d k := id
@[simp] lemma rel_t_t : ((t i : (codingFrame I).World) ≺ t k) ↔ k = i := Iff.rfl

instance : Std.Refl (codingFrame I).Rel where
  refl w := by
    cases w using casesOn <;> simp

instance : IsTrans (codingFrame I).World (codingFrame I).Rel where
  trans x y z hxy hyz := by
    cases x using casesOn <;> cases y using casesOn <;> cases z using casesOn <;> simp_all <;>
      omega

lemma rel_antisymm (hxy : x ≺ y) (hyx : y ≺ x) : x = y := by
  cases x using casesOn <;> cases y using casesOn <;> simp_all <;> omega

/-- The cone above a point other than a `d`-point is finite. -/
lemma cone_finite {w : (codingFrame I).World} (hw : ∀ k, w ≠ d k) : {z | w ≺ z}.Finite := by
  obtain ⟨m, hm⟩ : ∃ m, ∀ z, w ≺ z → ∃ k ≤ m, z = a k ∨ z = b k ∨ z = c k ∨ z = t k := by
    cases w using casesOn with
    | d k => exact absurd rfl (hw k)
    | a m =>
      use m + 1
      intro z hz
      cases z using casesOn <;> simp_all
    | b m =>
      use m + 1
      intro z hz
      cases z using casesOn <;> simp_all <;> omega
    | c m =>
      use m + 1
      intro z hz
      cases z using casesOn <;> simp_all <;> omega
    | t m =>
      use m + 2
      intro z hz
      cases z using casesOn <;> simp_all
      omega
  apply ((Finset.range (m + 1)).image a ∪ (Finset.range (m + 1)).image b ∪
    (Finset.range (m + 1)).image c ∪ (Finset.range (m + 1)).image t).finite_toSet.subset
  intro z hz
  obtain ⟨k, hk, rfl | rfl | rfl | rfl⟩ := hm z hz <;> simp [hk]

/-- An infinite strict chain consists of `d`-points. -/
lemma strict_chain_all_d {u : ℕ → (codingFrame I).World} (hR : ∀ m, u m ≺ u (m + 1))
    (hs : ∀ m, u (m + 1) ⊀ u m) (i : ℕ) : ∃ k, u i = d k := by
  have hinj : Function.Injective u := injective_of_forall_rel_succ hR hs
  have hchain : ∀ n, u i ≺ u (i + n) := by
    intro n
    induction n with
    | zero => exact Frame.rel_refl _
    | succ n ih => exact Frame.rel_trans ih (hR (i + n))
  have hinj' : Function.Injective fun n => u (i + n) := by
    intro a b hab
    have := hinj hab
    omega
  have hinf : {z | u i ≺ z}.Infinite := Set.infinite_of_injective_forall_mem hinj' hchain
  by_contra h
  push Not at h
  exact (cone_finite h).not_infinite hinf

/-- The involution exchanging the `b`- and `c`-families. -/
def swap : (codingFrame I).World → (codingFrame I).World
| a m => a m
| b m => c m
| c m => b m
| d m => d m
| t m => t m

@[simp] lemma swap_a : swap (a m : (codingFrame I).World) = a m := rfl
@[simp] lemma swap_b : swap (b m : (codingFrame I).World) = c m := rfl
@[simp] lemma swap_c : swap (c m : (codingFrame I).World) = b m := rfl
@[simp] lemma swap_d : swap (d m : (codingFrame I).World) = d m := rfl
@[simp] lemma swap_t : swap (t m : (codingFrame I).World) = t m := rfl

lemma swap_involutive : Function.Involutive (swap (I := I)) := by
  intro x
  cases x using casesOn <;> rfl

@[simp] lemma swap_swap (x : (codingFrame I).World) : swap (swap x) = x := swap_involutive x

lemma rel_swap : (swap x ≺ swap y) ↔ x ≺ y := by
  cases x using casesOn <;> cases y using casesOn <;> simp

variable {V : (codingFrame I).World → ℕ → Prop} {w : (codingFrame I).World} {A B : Formula ℕ}

@[simp] lemma forces_atom {n : ℕ} : x ⊩[⟨codingFrame I, V⟩] #n ↔ V x n := Iff.rfl

private lemma exists_rel_of_guard
    (hg : y ⊩[⟨codingFrame I, V⟩] A 🡒 (∼B ⋏ ◇B)) (hp : y ⊩[⟨codingFrame I, V⟩] A) :
    ∃ z, y ≺ z ∧ z ⊀ y ∧ z ⊩[⟨codingFrame I, V⟩] B := by
  obtain ⟨hnq, hq⟩ := forces_and.mp (hg hp);
  obtain ⟨z, hyz, hz⟩ := forces_dia.mp hq;
  use z, hyz;
  and_intros;
  · by_contra hzy;
    obtain rfl := rel_antisymm hyz hzy;
    exact forces_neg.mp hnq hz;
  · exact hz

private lemma exists_p01_chain (hD : w ⊩[⟨codingFrame I, V⟩] δ) :
    ∃ u : ℕ → (codingFrame I).World, u 0 = w ∧
      ∀ i, u i ≺ u (i + 1) ∧ u (i + 1) ⊀ u i ∧
        w ≺ u i ∧ u i ⊩[⟨codingFrame I, V⟩] (#0 ⋎ #1) := by
  obtain ⟨hp01, hbox₁, hbox₂, -⟩ := forces_δ_iff.mp hD;
  have step : ∀ y : (codingFrame I).World, w ≺ y → y ⊩[⟨codingFrame I, V⟩] (#0 ⋎ #1) →
      ∃ v, y ≺ v ∧ v ⊀ y ∧ w ≺ v ∧ v ⊩[⟨codingFrame I, V⟩] (#0 ⋎ #1) := by
    intro y hwy hy;
    rcases forces_or.mp hy with hy₀ | hy₁;
    · obtain ⟨z, hyz, hzy, hz⟩ := exists_rel_of_guard (forces_box.mp hbox₁ y hwy) hy₀;
      exact ⟨z, hyz, hzy, Frame.rel_trans hwy hyz, forces_or.mpr (Or.inr hz)⟩;
    · obtain ⟨z, hyz, hzy, hz⟩ := exists_rel_of_guard (forces_box.mp hbox₂ y hwy) hy₁;
      exact ⟨z, hyz, hzy, Frame.rel_trans hwy hyz, forces_or.mpr (Or.inl hz)⟩;
  obtain ⟨u, hu₀, hu⟩ := exists_seq_of_forall_exists_rel (r := fun y v => y ≺ v ∧ v ⊀ y)
    (P := fun _ y => w ≺ y ∧ y ⊩[⟨codingFrame I, V⟩] (#0 ⋎ #1)) ⟨Frame.rel_refl w, hp01⟩ <| by
      rintro - y ⟨hwy, hy⟩;
      obtain ⟨v, hyv, hvy, hwv, hv⟩ := step y hwy hy;
      exact ⟨v, ⟨hyv, hvy⟩, hwv, hv⟩;
  use u;
  and_intros;
  · exact hu₀;
  · intro i;
    exact ⟨(hu i).2.1, (hu i).2.2, (hu i).1⟩

/-- A point forcing `δ` is a `d`-point. -/
lemma exists_d_of_forces_δ (hD : w ⊩[⟨codingFrame I, V⟩] δ) : ∃ m, w = d m := by
  obtain ⟨u, hu₀, hu⟩ := exists_p01_chain hD;
  obtain ⟨m, hm⟩ := strict_chain_all_d (fun i => (hu i).1) (fun i => (hu i).2.1) 0;
  exact ⟨m, hu₀ ▸ hm⟩

/-- If `d_m` forces `δ`, every `d_k` with `m ≤ k` forces `#0 ⋎ #1`. -/
lemma forces_p01_at {m : ℕ} (hD : d m ⊩[⟨codingFrame I, V⟩] δ) {k : ℕ} (hk : m ≤ k) :
    d k ⊩[⟨codingFrame I, V⟩] #0 ⋎ #1 := by
  obtain ⟨u, hu₀, hu⟩ := exists_p01_chain hD;
  have hd : ∀ i, ∃ k, u i = d k := by
    intro i;
    exact strict_chain_all_d (fun j => (hu j).1) (fun j => (hu j).2.1) i;
  choose kf hkf using hd;
  have hmono : StrictMono kf := by
    apply strictMono_nat_of_lt_succ;
    intro i;
    have h := (hu i).2.1;
    rw [hkf i, hkf (i + 1)] at h;
    simpa using h;
  have h₁ : d (kf k) ⊩[⟨codingFrame I, V⟩] #0 ⋎ #1 := by
    rw [← hkf k];
    exact (hu k).2.2.2;
  by_contra hcon;
  obtain ⟨-, -, -, hbox⟩ := forces_δ_iff.mp hD;
  have h₂ := forces_box.mp hbox (d k) (by simp [hk]) (forces_neg.mpr hcon);
  exact forces_neg.mp (forces_box.mp h₂ (d (kf k)) (by simpa using hmono.le_apply)) h₁

section Frame

variable {j : ℕ}

/-- `b_{j+2}` is the only point seeing `b_{j+1}` and `c_j` but not `c_{j+1}`. -/
lemma rel_b_succ_iff :
    (z ≺ b (j + 1) ∧ z ≺ c j ∧ z ⊀ c (j + 1)) ↔ z = (b (j + 2) : (codingFrame I).World) := by
  cases z using casesOn <;> simp <;> grind

/-- `c_{j+2}` is the only point seeing `c_{j+1}` and `b_j` but not `b_{j+1}`. -/
lemma rel_c_succ_iff :
    (z ≺ c (j + 1) ∧ z ≺ b j ∧ z ⊀ b (j + 1)) ↔ z = (c (j + 2) : (codingFrame I).World) := by
  cases z using casesOn <;> simp <;> grind

/-- The points seeing `b_{j+1}` and `c_{j+1}` but neither `b_{j+2}` nor `c_{j+2}` are `a_j` and,
when `j - 1 ∈ I`, `t_{j-1}`. -/
lemma rel_α_iff :
    (z ≺ b (j + 1) ∧ z ≺ c (j + 1) ∧ z ⊀ b (j + 2) ∧ z ⊀ c (j + 2)) ↔
      z = (a j : (codingFrame I).World) ∨ (1 ≤ j ∧ j - 1 ∈ I ∧ z = t (j - 1)) := by
  cases z using casesOn <;> simp <;> grind

/-- The points seeing an `α_i`-point and an `α_{i+1}`-point but no `α_{i+2}`-point, where `α_j` is
pinned as in `rel_α_iff`, are exactly `t_i` for `i ∈ I`. -/
lemma rel_η_iff :
    ((z ≺ a i ∨ (1 ≤ i ∧ i - 1 ∈ I ∧ z ≺ t (i - 1))) ∧
      (z ≺ a (i + 1) ∨ (1 ≤ i + 1 ∧ i + 1 - 1 ∈ I ∧ z ≺ t (i + 1 - 1))) ∧
      ¬(z ≺ a (i + 2) ∨ (1 ≤ i + 2 ∧ i + 2 - 1 ∈ I ∧ z ≺ t (i + 2 - 1)))) ↔
      i ∈ I ∧ z = (t i : (codingFrame I).World) := by
  cases z using casesOn <;> simp <;> grind

/-- Seeing a point of the form given by `rel_α_iff` is seeing `a_j` or `t_{j-1}`. -/
lemma exists_rel_α_iff {j : ℕ} :
    (∃ y, z ≺ y ∧ (y = (a j : (codingFrame I).World) ∨ (1 ≤ j ∧ j - 1 ∈ I ∧ y = t (j - 1)))) ↔
      z ≺ a j ∨ (1 ≤ j ∧ j - 1 ∈ I ∧ z ≺ t (j - 1)) := by
  constructor;
  · rintro ⟨y, hzy, rfl | ⟨h₁, h₂, rfl⟩⟩;
    · exact Or.inl hzy;
    · exact Or.inr ⟨h₁, h₂, hzy⟩;
  · rintro (h | ⟨h₁, h₂, h⟩);
    · exact ⟨a j, h, Or.inl rfl⟩;
    · exact ⟨t (j - 1), h, Or.inr ⟨h₁, h₂, rfl⟩⟩

end Frame

section Cone

variable {k : ℕ}

/-- A point above `d_k` sees `b_0`, unless it is `c_0` or `c_1`. -/
lemma eq_or_rel_b₀ (h : d k ≺ z) : z ≺ b 0 ∨ z = c 0 ∨ z = c 1 := by
  cases z using casesOn <;> simp_all
  grind

/-- A point above `d_k` sees `c_0`, unless it is `b_0` or `b_1`. -/
lemma eq_or_rel_c₀ (h : d k ≺ z) : z ≺ c 0 ∨ z = b 0 ∨ z = b 1 := by
  cases z using casesOn <;> simp_all
  grind

/-- A point above `d_k` not seeing `c_0` is `b_0` or `b_1`. -/
lemma eq_of_not_rel_c₀ (h : d k ≺ z) (hz : z ⊀ c 0) : z = b 0 ∨ z = b 1 := by
  cases z using casesOn <;> simp_all
  grind

/-- A point above `d_k` not seeing `b_0` is `c_0` or `c_1`. -/
lemma eq_of_not_rel_b₀ (h : d k ≺ z) (hz : z ⊀ b 0) : z = c 0 ∨ z = c 1 := by
  cases z using casesOn <;> simp_all
  grind

/-- A point above `d_k` not seeing `b_1` is `b_0` or one of `c_0`, `c_1`, `c_2`. -/
lemma eq_of_not_rel_b₁ (h : d k ≺ z) (hz : z ⊀ b 1) : z = b 0 ∨ z = c 0 ∨ z = c 1 ∨ z = c 2 := by
  cases z using casesOn <;> simp_all
  grind

/-- A point above `d_k` not seeing `c_1` is `c_0` or one of `b_0`, `b_1`, `b_2`. -/
lemma eq_of_not_rel_c₁ (h : d k ≺ z) (hz : z ⊀ c 1) : z = c 0 ∨ z = b 0 ∨ z = b 1 ∨ z = b 2 := by
  cases z using casesOn <;> simp_all
  grind

end Cone

/-- Forcing is invariant under `swap` together with the valuation `V ∘ swap`. -/
lemma forces_swap_iff :
    x ⊩[⟨codingFrame I, V⟩] A ↔ swap x ⊩[⟨codingFrame I, V ∘ swap⟩] A := by
  induction A generalizing x with
  | atom a => simp [Function.comp]
  | falsum => simp [Model.World.Forces]
  | imp B C ihB ihC => simp [Model.World.Forces, ihB, ihC]
  | dia B ih =>
    simp only [Model.World.Forces];
    constructor;
    · rintro ⟨y, hxy, hy⟩;
      exact ⟨swap y, rel_swap.mpr hxy, ih.mp hy⟩;
    · rintro ⟨y, hxy, hy⟩;
      use swap y;
      and_intros;
      · exact rel_swap.mp (by simpa using hxy);
      · exact ih.mpr (by simpa using hy)

/-- If `A` is forced exactly at the points satisfying `S` on the cone of `w`, then on this cone
`◇A` is forced exactly at the points seeing such a point. -/
lemma forces_dia_iff_of_pinned {S : (codingFrame I).World → Prop}
    (hA : ∀ y, w ≺ y → (y ⊩[⟨codingFrame I, V⟩] A ↔ S y)) (hz : w ≺ z) :
    z ⊩[⟨codingFrame I, V⟩] ◇A ↔ ∃ y, z ≺ y ∧ S y := by
  rw [forces_dia];
  constructor;
  · rintro ⟨y, hzy, hy⟩;
    exact ⟨y, hzy, (hA y (Frame.rel_trans hz hzy)).mp hy⟩;
  · rintro ⟨y, hzy, hy⟩;
    exact ⟨y, hzy, (hA y (Frame.rel_trans hz hzy)).mpr hy⟩

/-- If `A` is forced exactly at `p` on the cone of `w`, then on this cone `◇A` is forced exactly
at the points seeing `p`. -/
lemma forces_dia_iff_of_eq {p : (codingFrame I).World}
    (hA : ∀ y, w ≺ y → (y ⊩[⟨codingFrame I, V⟩] A ↔ y = p)) (hz : w ≺ z) :
    z ⊩[⟨codingFrame I, V⟩] ◇A ↔ z ≺ p := by
  rw [forces_dia_iff_of_pinned hA hz];
  simp

/-- The pinning conditions at a point `w`: `w` forces `δ`, `◇(α m)` and `ι 0`, and the atoms
`q₀` and `r₀` spread to the successors and exclude each other and `q₁`, `r₁`. -/
structure PinData (I : Set ℕ) (V : (codingFrame I).World → ℕ → Prop)
    (w : (codingFrame I).World) (m : ℕ) : Prop where
  hδ : w ⊩[⟨codingFrame I, V⟩] δ
  hα : w ⊩[⟨codingFrame I, V⟩] ◇(α m)
  hι : w ⊩[⟨codingFrame I, V⟩] ι 0
  h₂ : w ⊩[⟨codingFrame I, V⟩] □(#2 🡒 □#2)
  h₄ : w ⊩[⟨codingFrame I, V⟩] □(#4 🡒 □#4)
  h₂₄ : w ⊩[⟨codingFrame I, V⟩] □(∼(#2 ⋏ #4))
  h₂₃ : w ⊩[⟨codingFrame I, V⟩] □(∼(#2 ⋏ #3))
  h₄₅ : w ⊩[⟨codingFrame I, V⟩] □(∼(#4 ⋏ #5))
  h₂₅ : w ⊩[⟨codingFrame I, V⟩] □(∼(#2 ⋏ #5))
  h₄₃ : w ⊩[⟨codingFrame I, V⟩] □(∼(#4 ⋏ #3))

namespace PinData

/-- Exchanging `b` and `c` transports the pinning conditions. -/
lemma swapped (hP : PinData I V w m) : PinData I (V ∘ swap) (swap w) m where
  hδ := forces_swap_iff.mp hP.hδ
  hα := forces_swap_iff.mp hP.hα
  hι := forces_swap_iff.mp hP.hι
  h₂ := forces_swap_iff.mp hP.h₂
  h₄ := forces_swap_iff.mp hP.h₄
  h₂₄ := forces_swap_iff.mp hP.h₂₄
  h₂₃ := forces_swap_iff.mp hP.h₂₃
  h₄₅ := forces_swap_iff.mp hP.h₄₅
  h₂₅ := forces_swap_iff.mp hP.h₂₅
  h₄₃ := forces_swap_iff.mp hP.h₄₃

section Base

variable {k : ℕ} {u v : (codingFrame I).World} (hP : PinData I V (d k) m)

include hP

lemma up₂ (hu : d k ≺ u) (h : u ⊩[⟨codingFrame I, V⟩] #2) (huz : u ≺ z) :
    z ⊩[⟨codingFrame I, V⟩] #2 :=
  forces_box.mp (forces_box.mp hP.h₂ u hu h) z huz

lemma up₄ (hu : d k ≺ u) (h : u ⊩[⟨codingFrame I, V⟩] #4) (huz : u ≺ z) :
    z ⊩[⟨codingFrame I, V⟩] #4 :=
  forces_box.mp (forces_box.mp hP.h₄ u hu h) z huz

lemma excl₂₄ (hz : d k ≺ z) (h₂ : z ⊩[⟨codingFrame I, V⟩] #2)
    (h₄ : z ⊩[⟨codingFrame I, V⟩] #4) : False :=
  forces_neg.mp (forces_box.mp hP.h₂₄ z hz) (forces_and.mpr ⟨h₂, h₄⟩)

lemma excl₂₃ (hz : d k ≺ z) (h₂ : z ⊩[⟨codingFrame I, V⟩] #2)
    (h₃ : z ⊩[⟨codingFrame I, V⟩] #3) : False :=
  forces_neg.mp (forces_box.mp hP.h₂₃ z hz) (forces_and.mpr ⟨h₂, h₃⟩)

lemma excl₄₅ (hz : d k ≺ z) (h₄ : z ⊩[⟨codingFrame I, V⟩] #4)
    (h₅ : z ⊩[⟨codingFrame I, V⟩] #5) : False :=
  forces_neg.mp (forces_box.mp hP.h₄₅ z hz) (forces_and.mpr ⟨h₄, h₅⟩)

lemma excl₂₅ (hz : d k ≺ z) (h₂ : z ⊩[⟨codingFrame I, V⟩] #2)
    (h₅ : z ⊩[⟨codingFrame I, V⟩] #5) : False :=
  forces_neg.mp (forces_box.mp hP.h₂₅ z hz) (forces_and.mpr ⟨h₂, h₅⟩)

lemma excl₄₃ (hz : d k ≺ z) (h₄ : z ⊩[⟨codingFrame I, V⟩] #4)
    (h₃ : z ⊩[⟨codingFrame I, V⟩] #3) : False :=
  forces_neg.mp (forces_box.mp hP.h₄₃ z hz) (forces_and.mpr ⟨h₄, h₃⟩)

lemma ι₁_at (hu : d k ≺ u) (h : u ⊩[⟨codingFrame I, V⟩] #3) :
    (∃ x, u ≺ x ∧ x ⊩[⟨codingFrame I, V⟩] #2) ∧
      ∀ x, u ≺ x → ¬ x ⊩[⟨codingFrame I, V⟩] #4 := by
  obtain ⟨h₁, h₂⟩ := forces_and.mp
    (forces_box.mp (forces_ι_iff.mp hP.hι).1 u hu (by simpa using h));
  exact ⟨by simpa using forces_dia.mp h₁,
    fun x hx h₄ => forces_neg.mp h₂ (forces_dia.mpr ⟨x, hx, by simpa using h₄⟩)⟩

lemma ι₂_at (hu : d k ≺ u) (h : u ⊩[⟨codingFrame I, V⟩] #5) :
    (∃ x, u ≺ x ∧ x ⊩[⟨codingFrame I, V⟩] #4) ∧
      ∀ x, u ≺ x → ¬ x ⊩[⟨codingFrame I, V⟩] #2 := by
  obtain ⟨h₁, h₂⟩ := forces_and.mp
    (forces_box.mp (forces_ι_iff.mp hP.hι).2.1 u hu (by simpa using h));
  exact ⟨by simpa using forces_dia.mp h₁,
    fun x hx h₄ => forces_neg.mp h₂ (forces_dia.mpr ⟨x, hx, by simpa using h₄⟩)⟩

lemma ι₃_at (hu : d k ≺ u) (h : u ⊩[⟨codingFrame I, V⟩] #2) :
    ∀ x, u ≺ x → ¬ x ⊩[⟨codingFrame I, V⟩] #3 := by
  have h₂ := forces_box.mp (forces_ι_iff.mp hP.hι).2.2.1 u hu (by simpa using h);
  exact fun x hx h₃ => forces_neg.mp h₂ (forces_dia.mpr ⟨x, hx, by simpa using h₃⟩)

lemma ι₄_at (hu : d k ≺ u) (h : u ⊩[⟨codingFrame I, V⟩] #4) :
    ∀ x, u ≺ x → ¬ x ⊩[⟨codingFrame I, V⟩] #5 := by
  have h₂ := forces_box.mp (forces_ι_iff.mp hP.hι).2.2.2 u hu (by simpa using h);
  exact fun x hx h₃ => forces_neg.mp h₂ (forces_dia.mpr ⟨x, hx, by simpa using h₃⟩)

lemma exists_atom₃ : ∃ y, d k ≺ y ∧ y ⊩[⟨codingFrame I, V⟩] #3 := by
  obtain ⟨s, hs, hsα⟩ := forces_dia.mp hP.hα;
  obtain ⟨y, Rsy, hy⟩ := forces_dia.mp (forces_α_iff.mp hsα).1;
  obtain ⟨z, Ryz, hz⟩ := exists_forces_atom₃_of_forces_β hy;
  exact ⟨z, Frame.rel_trans hs (Frame.rel_trans Rsy Ryz), hz⟩

lemma exists_atom₅ : ∃ y, d k ≺ y ∧ y ⊩[⟨codingFrame I, V⟩] #5 := by
  obtain ⟨s, hs, hsα⟩ := forces_dia.mp hP.hα;
  obtain ⟨y, Rsy, hy⟩ := forces_dia.mp (forces_α_iff.mp hsα).2.1;
  obtain ⟨z, Ryz, hz⟩ := exists_forces_atom₅_of_forces_γ hy;
  exact ⟨z, Frame.rel_trans hs (Frame.rel_trans Rsy Ryz), hz⟩

lemma exists_atom₂ : ∃ y, d k ≺ y ∧ y ⊩[⟨codingFrame I, V⟩] #2 := by
  obtain ⟨y, hy, h⟩ := hP.exists_atom₃;
  obtain ⟨x, hyx, hx⟩ := (hP.ι₁_at hy h).1;
  exact ⟨x, Frame.rel_trans hy hyx, hx⟩

lemma exists_atom₄ : ∃ y, d k ≺ y ∧ y ⊩[⟨codingFrame I, V⟩] #4 := by
  obtain ⟨y, hy, h⟩ := hP.exists_atom₅;
  obtain ⟨x, hyx, hx⟩ := (hP.ι₂_at hy h).1;
  exact ⟨x, Frame.rel_trans hy hyx, hx⟩

/-- Either `b_0` forces `q₀` and `c_0` forces `r₀`, or the other way round. -/
lemma orientation : (b 0 ⊩[⟨codingFrame I, V⟩] #2 ∧ c 0 ⊩[⟨codingFrame I, V⟩] #4) ∨
    (c 0 ⊩[⟨codingFrame I, V⟩] #2 ∧ b 0 ⊩[⟨codingFrame I, V⟩] #4) := by
  obtain ⟨u, hu, hu₂⟩ := hP.exists_atom₂;
  obtain ⟨v, hv, hv₄⟩ := hP.exists_atom₄;
  have hb : ¬(u ≺ b 0 ∧ v ≺ b 0) := fun ⟨h₁, h₂⟩ =>
    hP.excl₂₄ (by simp) (hP.up₂ hu hu₂ h₁) (hP.up₄ hv hv₄ h₂);
  have hc : ¬(u ≺ c 0 ∧ v ≺ c 0) := fun ⟨h₁, h₂⟩ =>
    hP.excl₂₄ (by simp) (hP.up₂ hu hu₂ h₁) (hP.up₄ hv hv₄ h₂);
  have hC : (u = c 0 ∨ u = c 1) ∨ (v = c 0 ∨ v = c 1) := by
    by_cases h : u ≺ b 0;
    · exact Or.inr (eq_of_not_rel_b₀ hv fun h' => hb ⟨h, h'⟩);
    · exact Or.inl (eq_of_not_rel_b₀ hu h);
  have hB : (u = b 0 ∨ u = b 1) ∨ (v = b 0 ∨ v = b 1) := by
    by_cases h : u ≺ c 0;
    · exact Or.inr (eq_of_not_rel_c₀ hv fun h' => hc ⟨h, h'⟩);
    · exact Or.inl (eq_of_not_rel_c₀ hu h);
  rcases hC with huC | hvC;
  · have hvB : v = b 0 ∨ v = b 1 := by
      rcases hB with huB | hvB;
      · grind;
      · exact hvB;
    right;
    constructor;
    · exact hP.up₂ hu hu₂ (by rcases huC with rfl | rfl <;> simp);
    · exact hP.up₄ hv hv₄ (by rcases hvB with rfl | rfl <;> simp);
  · have huB : u = b 0 ∨ u = b 1 := by
      rcases hB with huB | hvB;
      · exact huB;
      · grind;
    left;
    constructor;
    · exact hP.up₂ hu hu₂ (by rcases huB with rfl | rfl <;> simp);
    · exact hP.up₄ hv hv₄ (by rcases hvC with rfl | rfl <;> simp)

end Base

section CaseA

variable {k : ℕ} {z : (codingFrame I).World} (hP : PinData I V (d k) m)
  (hb : b 0 ⊩[⟨codingFrame I, V⟩] #2) (hc : c 0 ⊩[⟨codingFrame I, V⟩] #4)

include hP hb hc

lemma eq_b₁_of_atom₃ (hz : d k ≺ z) (h : z ⊩[⟨codingFrame I, V⟩] #3) : z = b 1 := by
  have h₄ := (hP.ι₁_at hz h).2;
  rcases eq_of_not_rel_c₀ hz fun hzc => h₄ (c 0) hzc hc with rfl | rfl;
  · exact (hP.excl₂₃ hz hb h).elim;
  · rfl

lemma forces_atom₃_b₁ : b 1 ⊩[⟨codingFrame I, V⟩] #3 := by
  obtain ⟨y, hy, h⟩ := hP.exists_atom₃;
  obtain rfl := eq_b₁_of_atom₃ hP hb hc hy h;
  exact h

lemma eq_c₁_of_atom₅ (hz : d k ≺ z) (h : z ⊩[⟨codingFrame I, V⟩] #5) : z = c 1 := by
  have h₂ := (hP.ι₂_at hz h).2;
  rcases eq_of_not_rel_b₀ hz fun hzb => h₂ (b 0) hzb hb with rfl | rfl;
  · exact (hP.excl₄₅ hz hc h).elim;
  · rfl

lemma forces_atom₅_c₁ : c 1 ⊩[⟨codingFrame I, V⟩] #5 := by
  obtain ⟨y, hy, h⟩ := hP.exists_atom₅;
  obtain rfl := eq_c₁_of_atom₅ hP hb hc hy h;
  exact h

lemma eq_b₀_of_atom₂ (hz : d k ≺ z) (h : z ⊩[⟨codingFrame I, V⟩] #2) : z = b 0 := by
  have h₃ := hP.ι₃_at hz h;
  rcases eq_of_not_rel_b₁ hz fun hzb => h₃ (b 1) hzb (forces_atom₃_b₁ hP hb hc) with
    rfl | rfl | rfl | rfl;
  · rfl;
  · exact (hP.excl₂₄ hz h hc).elim;
  · exact (hP.excl₂₄ (by simp) (hP.up₂ hz h (by simp)) hc).elim;
  · exact (hP.excl₂₄ (by simp) (hP.up₂ hz h (by simp)) hc).elim

lemma eq_c₀_of_atom₄ (hz : d k ≺ z) (h : z ⊩[⟨codingFrame I, V⟩] #4) : z = c 0 := by
  have h₅ := hP.ι₄_at hz h;
  rcases eq_of_not_rel_c₁ hz fun hzc => h₅ (c 1) hzc (forces_atom₅_c₁ hP hb hc) with
    rfl | rfl | rfl | rfl;
  · rfl;
  · exact (hP.excl₂₄ hz hb h).elim;
  · exact (hP.excl₂₄ (by simp) hb (hP.up₄ hz h (by simp))).elim;
  · exact (hP.excl₂₄ (by simp) hb (hP.up₄ hz h (by simp))).elim

/-- With `b_0` forcing `q₀` and `c_0` forcing `r₀`, the formulas `β_j` and `γ_j` are forced exactly
at `b_j` and `c_j` on the cone of `d_k`. -/
lemma pinned_aux (j : ℕ) :
    (∀ z, d k ≺ z → (z ⊩[⟨codingFrame I, V⟩] β j ↔ z = b j) ∧
      (z ⊩[⟨codingFrame I, V⟩] γ j ↔ z = c j)) ∧
    (∀ z, d k ≺ z → (z ⊩[⟨codingFrame I, V⟩] β (j + 1) ↔ z = b (j + 1)) ∧
      (z ⊩[⟨codingFrame I, V⟩] γ (j + 1) ↔ z = c (j + 1))) := by
  induction j with
  | zero =>
    constructor;
    · intro z hz;
      simp only [β_zero, γ_zero, forces_atom];
      constructor;
      · exact ⟨eq_b₀_of_atom₂ hP hb hc hz, fun h => h ▸ hb⟩;
      · exact ⟨eq_c₀_of_atom₄ hP hb hc hz, fun h => h ▸ hc⟩;
    · intro z hz;
      simp only [Nat.zero_add, β_one, γ_one, forces_atom];
      constructor;
      · exact ⟨eq_b₁_of_atom₃ hP hb hc hz, fun h => h ▸ forces_atom₃_b₁ hP hb hc⟩;
      · exact ⟨eq_c₁_of_atom₅ hP hb hc hz, fun h => h ▸ forces_atom₅_c₁ hP hb hc⟩
  | succ j ih =>
    obtain ⟨ih₀, ih₁⟩ := ih;
    refine ⟨ih₁, fun z hz => ?_⟩;
    have e₁ : z ⊩[⟨codingFrame I, V⟩] ◇(β (j + 1)) ↔ z ≺ b (j + 1) :=
      forces_dia_iff_of_eq (fun y hy => (ih₁ y hy).1) hz;
    have e₂ : z ⊩[⟨codingFrame I, V⟩] ◇(γ (j + 1)) ↔ z ≺ c (j + 1) :=
      forces_dia_iff_of_eq (fun y hy => (ih₁ y hy).2) hz;
    have e₃ : z ⊩[⟨codingFrame I, V⟩] ◇(β j) ↔ z ≺ b j :=
      forces_dia_iff_of_eq (fun y hy => (ih₀ y hy).1) hz;
    have e₄ : z ⊩[⟨codingFrame I, V⟩] ◇(γ j) ↔ z ≺ c j :=
      forces_dia_iff_of_eq (fun y hy => (ih₀ y hy).2) hz;
    constructor;
    · rw [show j + 1 + 1 = j + 2 from rfl, β_add_two, forces_and, forces_and, forces_neg];
      simp only [NotForces, e₁, e₄, e₂];
      exact rel_b_succ_iff;
    · rw [show j + 1 + 1 = j + 2 from rfl, γ_add_two, forces_and, forces_and, forces_neg];
      simp only [NotForces, e₂, e₃, e₁];
      exact rel_c_succ_iff

end CaseA

/-- (P2) Either the atoms `q_j`, `r_j` pin `β_j` to `b_j` and `γ_j` to `c_j` on the cone of `w`,
or the same holds with `b` and `c` exchanged. -/
theorem pinned (hP : PinData I V w m) :
    (∀ j z, w ≺ z → (z ⊩[⟨codingFrame I, V⟩] β j ↔ z = b j) ∧
      (z ⊩[⟨codingFrame I, V⟩] γ j ↔ z = c j)) ∨
    (∀ j z, w ≺ z → (z ⊩[⟨codingFrame I, V⟩] β j ↔ z = c j) ∧
      (z ⊩[⟨codingFrame I, V⟩] γ j ↔ z = b j)) := by
  obtain ⟨k, rfl⟩ := exists_d_of_forces_δ hP.hδ;
  rcases hP.orientation with ⟨hb, hc⟩ | ⟨hb, hc⟩;
  · exact Or.inl fun j z hz => (pinned_aux hP hb hc j).1 z hz;
  · right;
    intro j z hz;
    have hz' : d k ≺ swap z := by simpa using rel_swap.mpr hz;
    have := (pinned_aux hP.swapped (forces_swap_iff.mp hb) (forces_swap_iff.mp hc) j).1 _ hz';
    rw [forces_swap_iff (x := z), forces_swap_iff (x := z) (A := γ j)];
    simpa [swap_involutive.eq_iff] using this

/-- (P3) On the cone of `w`, `α_j` is forced exactly at `a_j` and at `t_{j-1}` when `j - 1 ∈ I`. -/
theorem forces_α_iff_of_pin (hP : PinData I V w m) (j : ℕ) (hz : w ≺ z) :
    z ⊩[⟨codingFrame I, V⟩] α j ↔
      z = a j ∨ (1 ≤ j ∧ j - 1 ∈ I ∧ z = t (j - 1)) := by
  rcases hP.pinned with h | h;
  · simp only [forces_α_iff, forces_neg, NotForces,
      forces_dia_iff_of_eq (fun y hy => (h (j + 1) y hy).1) hz,
      forces_dia_iff_of_eq (fun y hy => (h (j + 1) y hy).2) hz,
      forces_dia_iff_of_eq (fun y hy => (h (j + 2) y hy).1) hz,
      forces_dia_iff_of_eq (fun y hy => (h (j + 2) y hy).2) hz];
    exact rel_α_iff;
  · simp only [forces_α_iff, forces_neg, NotForces,
      forces_dia_iff_of_eq (fun y hy => (h (j + 1) y hy).1) hz,
      forces_dia_iff_of_eq (fun y hy => (h (j + 1) y hy).2) hz,
      forces_dia_iff_of_eq (fun y hy => (h (j + 2) y hy).1) hz,
      forces_dia_iff_of_eq (fun y hy => (h (j + 2) y hy).2) hz];
    rw [← rel_α_iff];
    tauto

/-- (P4) On the cone of `w`, `η_i` is forced exactly at `t_i` when `i ∈ I`. -/
theorem forces_η_iff_of_pin (hP : PinData I V w m) (i : ℕ) (hz : w ≺ z) :
    z ⊩[⟨codingFrame I, V⟩] η i ↔ i ∈ I ∧ z = t i := by
  have h : ∀ j, ∀ y, w ≺ y →
      (y ⊩[⟨codingFrame I, V⟩] α j ↔ y = a j ∨ (1 ≤ j ∧ j - 1 ∈ I ∧ y = t (j - 1))) :=
    fun j y hy => hP.forces_α_iff_of_pin j hy;
  simp only [forces_η_iff, forces_neg, NotForces, forces_dia_iff_of_pinned (h i) hz,
    forces_dia_iff_of_pinned (h (i + 1)) hz, forces_dia_iff_of_pinned (h (i + 2)) hz,
    exists_rel_α_iff];
  exact rel_η_iff

/-- (P1) The pinned point is a `d`-point `d_k` with `k ≤ m`. -/
theorem exists_d_le (hP : PinData I V w m) : ∃ k, w = d k ∧ k ≤ m := by
  obtain ⟨k, rfl⟩ := exists_d_of_forces_δ hP.hδ;
  obtain ⟨s, hs, hsα⟩ := forces_dia.mp hP.hα;
  rcases (hP.forces_α_iff_of_pin m hs).mp hsα with rfl | ⟨h₁, h₂, rfl⟩;
  · exact ⟨k, rfl, by simpa using hs⟩;
  · simp only [rel_d_t] at hs;
    exact ⟨k, rfl, by omega⟩

/-- (P5) Every `d_{k'}` above the pinned point `d_k` forces `#0 ⋎ #1`. -/
theorem forces_p01 {k k' : ℕ} (hP : PinData I V w m) (hk : w = d k) (hk' : k ≤ k') :
    d k' ⊩[⟨codingFrame I, V⟩] #0 ⋎ #1 :=
  forces_p01_at (hk ▸ hP.hδ) hk'

end PinData

end codingFrame

end Modal

end
