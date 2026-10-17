module

public import BlokDichotomy.GeneralFrame.Basic
public import BlokDichotomy.Kripke.Cycle
public import BlokDichotomy.Kripke.Makinson
public import Mathlib.Data.Set.Card
public import Mathlib.Basic.Finite.Sum

/-!
# The hooked frames

The hooked general frame `D.hooked I` for `D : HookData κ` and `I : Set ℕ`, with its accessibility
relation, admissible sets and reachability bounds.

## References

- [CZ98, Fig. 10.4, Fig. 10.5]
- [Blok78, Definition 4.3]
-/

@[expose] public section

universe u

namespace Frame

variable {κ : Type u} {F : Frame κ} {x y : F.World}

lemma exists_relItr_lt_card [Finite F.World] (h : y ∈ F.Reach x) :
    ∃ n < Nat.card F.World, x ≺^[n] y := by
  obtain ⟨n, hn⟩ := h;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hlt : n < Nat.card F.World;
    · exact ⟨n, hlt, hn⟩;
    obtain ⟨p, hp₀, hpn, hp⟩ := exists_path hn;
    have hni : ¬Function.Injective (fun i : Fin (Nat.card F.World + 1) => p i) := by
      intro hi;
      have := Nat.card_le_card_of_injective _ hi;
      simp at this;
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hni;
    have hne' : (i : ℕ) ≠ j := Fin.val_ne_of_ne hne;
    wlog hij' : (i : ℕ) < j generalizing i j;
    · exact this j i hij.symm hne.symm hne'.symm <| by omega;
    have h₁ := relItr_of_path hp (Nat.zero_le i) (by omega);
    have h₂ := relItr_of_path hp (i := j) (j := n) (by omega) le_rfl;
    rw [hp₀] at h₁;
    rw [hpn, ← hij] at h₂;
    exact ih _ (by omega) (relItr_trans h₁ h₂);

end Frame


/-- The data of a hooked frame: a rooted frame `F`, an infinite path in `F`, the number `len + 1`
of copies, the length `m` of the `d`-chain, and whether `dBot` is reflexive.
- [CZ98, Fig. 10.4, Fig. 10.5]
- [Blok78, Definition 4.3]
-/
structure HookData (κ : Type u) where
  F : Frame κ
  root : F.Root
  path : ℕ → F.World
  path_rel : ∀ t, path t ≺ path (t + 1)
  /-- The copies are `copy 0, …, copy len`. -/
  len : ℕ
  /-- The `d`-chain is `d m ≺ ⋯ ≺ d 0`. -/
  m : ℕ
  card_add_len_lt : Nat.card F.World + len + 2 ≤ m
  /-- Whether `dBot` sees itself. -/
  refl : Prop

namespace HookData

variable {κ : Type u} (D : HookData κ) (I : Set ℕ)

inductive World : Type u
  | base (u : D.F.World)
  | copy (t : ℕ) (ht : t ≤ D.len)
  | c
  | b
  | a (i : ℕ) (twin : Bool) (h : twin = true → i ∈ I)
  | d (j : ℕ) (hj : j ≤ D.m)
  | dBot

/-- The accessibility relation of the hooked frame.
- [CZ98, Fig. 10.4, Fig. 10.5]
-/
def Rel : D.World I → D.World I → Prop
  | .base u, .base v => u ≺ v
  | .base u, .copy t _ => u = D.path 0 ∧ t = 0
  | .copy t _, .base v => D.path (t + 1) ≺ v
  | .copy t _, .copy t' _ => t' = t + 1
  | .copy t _, .d j _ => t = D.len ∧ j = 0
  | .d j _, .base v => j = 0 ∧ v = D.root
  | .d j _, .c => j = 0
  | .d j _, .d j' _ => j = j' + 1
  | .d j _, .dBot => j = 0
  | .dBot, .dBot => D.refl
  | .c, .b => True
  | .b, .a _ _ _ => True
  | .a i _ _, .a j _ _ => j < i
  | .a i _ _, .d j _ => i = 0 ∧ j = D.m
  | _, _ => False

def hookFrame : Frame (D.World I) := ⟨D.Rel I⟩

variable {D I}

namespace World

def IsA : D.World I → Prop
  | .a _ _ _ => True
  | _ => False

def index : D.World I → ℕ
  | .a i _ _ => i
  | _ => 0

def twin : D.World I → Bool
  | .a _ t _ => t
  | _ => false

def IsUnwound : D.World I → Prop
  | .base _ => True
  | .copy _ _ => True
  | _ => False

@[simp] lemma isA_a {i : ℕ} {t : Bool} {h : t = true → i ∈ I} : (World.a i t h : D.World I).IsA :=
  trivial

@[simp] lemma index_a {i : ℕ} {t : Bool} {h : t = true → i ∈ I} :
    (World.a i t h : D.World I).index = i := rfl

lemma isA_iff {w : D.World I} : w.IsA ↔ ∃ i t h, w = .a i t h := by
  cases w <;> simp_all [IsA];

lemma isUnwound_iff {w : D.World I} :
    w.IsUnwound ↔ (∃ u, w = .base u) ∨ ∃ t ht, w = .copy t ht := by
  cases w <;> simp_all [IsUnwound];

end World

@[simp] lemma hookFrame_rel {x y : (D.hookFrame I).World} : x ≺ y ↔ D.Rel I x y := Iff.rfl

open World

lemma finite_isA_index_le (n : ℕ) : {w : D.World I | w.IsA ∧ w.index ≤ n}.Finite := by
  apply Set.Finite.of_finite_image (f := fun w => (w.index, w.twin));
  · apply ((Set.finite_le_nat n).prod Set.finite_univ).subset;
    rintro _ ⟨w, ⟨-, hw⟩, rfl⟩;
    exact ⟨hw, trivial⟩;
  · rintro (_ | _ | _ | _ | ⟨i, t, h⟩ | _ | _) ⟨⟨⟩, -⟩ (_ | _ | _ | _ | ⟨i', t', h'⟩ | _ | _)
      ⟨⟨⟩, -⟩ he;
    simp only [index, twin, Prod.mk.injEq] at he;
    obtain ⟨rfl, rfl⟩ := he;
    rfl;

/-- The admissible sets of the hooked frame: the sets `S` such that only finitely many `a`-points
disagree with `b` about membership in `S`.
- [CZ98, Fig. 10.5]
- [Blok78, Definition 4.3]
-/
def Adm (D : HookData κ) (I : Set ℕ) : Set (Set (D.World I)) :=
  {S | {w | w.IsA ∧ (w ∈ S ↔ World.b ∉ S)}.Finite}

lemma mem_adm_iff {S : Set (D.World I)} :
    S ∈ D.Adm I ↔ (World.b ∈ S → {w | w.IsA ∧ w ∉ S}.Finite) ∧
      (World.b ∉ S → {w | w.IsA ∧ w ∈ S}.Finite) := by
  by_cases hb : World.b ∈ S <;> simp [Adm, hb];

lemma mem_adm_of_not_mem_of_finite {S : Set (D.World I)} (hb : World.b ∉ S)
    (hS : {w | w.IsA ∧ w ∈ S}.Finite) : S ∈ D.Adm I :=
  mem_adm_iff.mpr ⟨fun h => absurd h hb, fun _ => hS⟩

lemma mem_adm_of_forall {S : Set (D.World I)} (hS : ∀ w ∈ S, w ≠ .b ∧ ¬w.IsA) : S ∈ D.Adm I :=
  mem_adm_of_not_mem_of_finite (fun h => (hS _ h).1 rfl) <|
    Set.finite_empty.subset fun w ⟨hw, hwS⟩ => (hS w hwS).2 hw

lemma adm_compl {S : Set (D.World I)} (hS : S ∈ D.Adm I) : Sᶜ ∈ D.Adm I := by
  apply hS.subset;
  rintro w ⟨hw, h⟩;
  simp only [Set.mem_compl_iff] at h;
  exact ⟨hw, by tauto⟩;

lemma adm_inter {S T : Set (D.World I)} (hS : S ∈ D.Adm I) (hT : T ∈ D.Adm I) :
    S ∩ T ∈ D.Adm I := by
  apply (hS.union hT).subset;
  rintro w ⟨hw, h⟩;
  simp only [Set.mem_inter_iff, not_and] at h;
  simp only [Set.mem_union, Set.mem_ofPred_eq];
  tauto;

lemma mem_diaSet_b {S : Set (D.World I)} :
    World.b ∈ (D.hookFrame I).diaSet S ↔ ∃ w ∈ S, w.IsA := by
  constructor;
  · rintro ⟨w, hw, hwS⟩;
    exact ⟨w, hwS, by cases w <;> simp_all [Rel, IsA]⟩;
  · rintro ⟨w, hwS, hw⟩;
    obtain ⟨i, t, h, rfl⟩ := isA_iff.mp hw;
    exact ⟨.a i t h, trivial, hwS⟩;

lemma mem_diaSet_of_isA {S : Set (D.World I)} {w : D.World I} (hw : w.IsA) :
    w ∈ (D.hookFrame I).diaSet S ↔
      (∃ w' ∈ S, w'.IsA ∧ w'.index < w.index) ∨ (w.index = 0 ∧ World.d D.m le_rfl ∈ S) := by
  obtain ⟨i, t, h, rfl⟩ := isA_iff.mp hw;
  constructor;
  · rintro ⟨w', hw', hw'S⟩;
    cases w' with
    | a j t' h' => exact Or.inl ⟨_, hw'S, trivial, hw'⟩;
    | d j hj =>
      obtain ⟨rfl, rfl⟩ := hw';
      exact Or.inr ⟨rfl, hw'S⟩;
    | _ => simp_all [Rel];
  · rintro (⟨w', hw'S, hw', hlt⟩ | ⟨h₀, hd⟩);
    · obtain ⟨j, t', h', rfl⟩ := isA_iff.mp hw';
      exact ⟨.a j t' h', hlt, hw'S⟩;
    · exact ⟨.d D.m le_rfl, ⟨h₀, rfl⟩, hd⟩;

lemma adm_diaSet {S : Set (D.World I)} : (D.hookFrame I).diaSet S ∈ D.Adm I := by
  by_cases h : ∃ w ∈ S, w.IsA;
  · obtain ⟨z, hzS, hz⟩ := h;
    apply (finite_isA_index_le z.index).subset;
    rintro w ⟨hw, hwS⟩;
    use hw;
    by_contra! hlt;
    exact (hwS.mp <| (mem_diaSet_of_isA hw).mpr <| Or.inl ⟨z, hzS, hz, hlt⟩) <|
      mem_diaSet_b.mpr ⟨z, hzS, hz⟩;
  · apply (finite_isA_index_le 0).subset;
    rintro w ⟨hw, hwS⟩;
    use hw;
    rcases (mem_diaSet_of_isA hw).mp (hwS.mpr fun hb => h <| mem_diaSet_b.mp hb) with
      ⟨w', hw'S, hw', -⟩ | ⟨h₀, -⟩;
    · exact absurd ⟨w', hw'S, hw'⟩ h;
    · omega;

variable (D I) in
/-- The hooked general frame.
- [CZ98, Fig. 10.4, Fig. 10.5]
- [Blok78, Definition 4.3]
-/
def hooked : GeneralFrame (D.World I) where
  toFrame := D.hookFrame I
  Adm := D.Adm I
  univ_mem := Set.finite_empty.subset fun _ ⟨_, h⟩ => h.mp trivial trivial
  inter_mem := adm_inter
  compl_mem := adm_compl
  diaSet_mem _ := adm_diaSet

@[simp] lemma hooked_toFrame : (D.hooked I).toFrame = D.hookFrame I := rfl

@[simp] lemma hooked_adm : (D.hooked I).Adm = D.Adm I := rfl


section Rel

/-! ### Successors and predecessors -/

variable {x y : (D.hookFrame I).World}

lemma rel_base_iff {u : D.F.World} :
    (.base u : (D.hookFrame I).World) ≺ y ↔
      (∃ v, y = .base v ∧ u ≺ v) ∨ (u = D.path 0 ∧ y = .copy 0 (Nat.zero_le _)) := by
  cases y <;> simp [Rel];

lemma rel_copy_iff {t : ℕ} {ht : t ≤ D.len} :
    (.copy t ht : (D.hookFrame I).World) ≺ y ↔
      (∃ v, y = .base v ∧ D.path (t + 1) ≺ v) ∨ (∃ h, y = .copy (t + 1) h) ∨
        (t = D.len ∧ y = .d 0 (Nat.zero_le _)) := by
  cases y <;> simp [Rel, eq_comm];
  omega;

lemma rel_c_iff : (.c : (D.hookFrame I).World) ≺ y ↔ y = .b := by
  cases y <;> simp [Rel];

lemma rel_b_iff : (.b : (D.hookFrame I).World) ≺ y ↔ y.IsA := by
  cases y <;> simp [Rel, IsA];

lemma rel_a_iff {i : ℕ} {t : Bool} {h : t = true → i ∈ I} :
    (.a i t h : (D.hookFrame I).World) ≺ y ↔
      (y.IsA ∧ y.index < i) ∨ (i = 0 ∧ y = .d D.m le_rfl) := by
  cases y <;> simp [Rel, IsA, index];

lemma rel_a_zero_iff {t : Bool} {h : t = true → 0 ∈ I} :
    (.a 0 t h : (D.hookFrame I).World) ≺ y ↔ y = .d D.m le_rfl := by
  rw [rel_a_iff];
  simp;

lemma rel_d_succ_iff {j : ℕ} {hj : j + 1 ≤ D.m} :
    (.d (j + 1) hj : (D.hookFrame I).World) ≺ y ↔ y = .d j (by omega) := by
  cases y <;> simp [Rel, eq_comm];

lemma rel_d_zero_iff {hj : 0 ≤ D.m} :
    (.d 0 hj : (D.hookFrame I).World) ≺ y ↔ y = .dBot ∨ y = .c ∨ y = .base D.root := by
  cases y <;> simp [Rel, eq_comm];

lemma rel_dBot_iff : (.dBot : (D.hookFrame I).World) ≺ y ↔ y = .dBot ∧ D.refl := by
  cases y <;> simp [Rel];

lemma rel_to_base_iff {v : D.F.World} :
    x ≺ (.base v : (D.hookFrame I).World) ↔
      (∃ u, x = .base u ∧ u ≺ v) ∨
        (∃ t ht, x = .copy t ht ∧ D.path (t + 1) ≺ v) ∨
        (x = .d 0 (Nat.zero_le _) ∧ v = D.root) := by
  cases x <;> simp_all [Rel];

lemma rel_to_copy_iff {t : ℕ} {ht : t ≤ D.len} :
    x ≺ (.copy t ht : (D.hookFrame I).World) ↔
      (t = 0 ∧ x = .base (D.path 0)) ∨ ∃ s hs, t = s + 1 ∧ x = .copy s hs := by
  cases x <;> simp [Rel, and_comm];
  omega;

lemma rel_to_c_iff : x ≺ (.c : (D.hookFrame I).World) ↔ x = .d 0 (Nat.zero_le _) := by
  cases x <;> simp [Rel];

lemma rel_to_b_iff : x ≺ (.b : (D.hookFrame I).World) ↔ x = .c := by
  cases x <;> simp [Rel];

lemma rel_to_a_iff {i : ℕ} {t : Bool} {h : t = true → i ∈ I} :
    x ≺ (.a i t h : (D.hookFrame I).World) ↔ x = .b ∨ (x.IsA ∧ i < x.index) := by
  cases x <;> simp [Rel, IsA, index];

lemma rel_to_d_iff {j : ℕ} {hj : j ≤ D.m} :
    x ≺ (.d j hj : (D.hookFrame I).World) ↔
      (∃ h, x = .d (j + 1) h) ∨ (j = 0 ∧ x = .copy D.len le_rfl) ∨
        (j = D.m ∧ x.IsA ∧ x.index = 0) := by
  cases x <;> simp [Rel, IsA, index, and_comm];
  omega;

lemma rel_to_dBot_iff :
    x ≺ (.dBot : (D.hookFrame I).World) ↔ x = .d 0 (Nat.zero_le _) ∨ (x = .dBot ∧ D.refl) := by
  cases x <;> simp [Rel];

lemma isUnwound_of_rel (hy : y.IsUnwound) (Rxy : x ≺ y) :
    x.IsUnwound ∨ x = .d 0 (Nat.zero_le _) := by
  cases x <;> cases y <;> simp_all [Rel, IsUnwound];

lemma isUnwound_of_isUnwound_rel (hx : x.IsUnwound) (Rxy : x ≺ y) :
    y.IsUnwound ∨ y = .d 0 (Nat.zero_le _) := by
  cases x <;> cases y <;> simp_all [Rel, IsUnwound];

lemma isA_of_rel (hy : y.IsA) (Rxy : x ≺ y) : x = .b ∨ x.IsA := by
  cases x <;> cases y <;> simp_all [Rel, IsA];

end Rel


section Reach

/-! ### Reachability -/

open Frame

variable {x y : (D.hookFrame I).World} {n : ℕ}

lemma relItr_base {u v : D.F.World} (Ruv : u ≺^[n] v) :
    RelItr (F := D.hookFrame I) n (.base u) (.base v) :=
  relItr_map (G := D.hookFrame I) World.base (fun h => h) Ruv

lemma relItr_copy {t t' : ℕ} {ht : t ≤ D.len} {ht' : t' ≤ D.len} (h : t ≤ t') :
    RelItr (F := D.hookFrame I) (t' - t) (.copy t ht) (.copy t' ht') := by
  induction t' with
  | zero =>
    obtain rfl : t = 0 := by omega;
    simp;
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h;
    · simp;
    · rw [show t' + 1 - t = t' - t + 1 by omega];
      exact relItr_tail (ih (ht' := by omega) (by omega)) (by simp [Rel]);

lemma relItr_d {j j' : ℕ} {hj : j ≤ D.m} {hj' : j' ≤ D.m} (h : j ≤ j') :
    RelItr (F := D.hookFrame I) (j' - j) (.d j' hj') (.d j hj) := by
  induction j' with
  | zero =>
    obtain rfl : j = 0 := by omega;
    simp;
  | succ j' ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h;
    · simp;
    · rw [show j' + 1 - j = (j' - j) + 1 by omega, iff_relItr_succ];
      exact ⟨.d j' (by omega), by simp [Rel], ih (hj' := by omega) (by omega)⟩;

/-- `.b ≺^[D.m + 3] .base D.root`.
- [CZ98, p. 367]
-/
lemma b_relItr_root : RelItr (F := D.hookFrame I) (D.m + 3) .b (.base D.root) := by
  have h₁ : RelItr (F := D.hookFrame I) (D.m - 0) (.d D.m le_rfl) (.d 0 (Nat.zero_le _)) :=
    relItr_d (Nat.zero_le _);
  have h₂ := relItr_tail h₁ (z := .base D.root) (by simp [Rel]);
  have h₃ := relItr_head (x := .a 0 false (by simp)) (by simp [Rel]) h₂;
  have h₄ := relItr_head (x := .b) (by simp [Rel]) h₃;
  rwa [show D.m - 0 + 1 + 1 + 1 = D.m + 3 by omega] at h₄;

lemma eq_dBot_of_dBot_relItr (RdBoty : (.dBot : (D.hookFrame I).World) ≺^[n] y) : y = .dBot := by
  induction n generalizing y with
  | zero => exact RdBoty.symm;
  | succ n ih =>
    obtain ⟨z, h₁, h₂⟩ := iff_relItr_succ'.mp RdBoty;
    obtain rfl := ih h₁;
    exact (rel_dBot_iff.mp h₂).1;

variable (D I) in
/-- The points `.dBot` and `.base u` with `D.path 0 ∉ D.F.Reach u`.
- [CZ98, p. 367]
-/
def detached : Set (D.hookFrame I).World :=
  {x | x = .dBot ∨ ∃ u, x = .base u ∧ D.path 0 ∉ D.F.Reach u}

@[simp] lemma dBot_mem_detached : (.dBot : (D.hookFrame I).World) ∈ D.detached I := Or.inl rfl

@[simp] lemma base_mem_detached_iff {u : D.F.World} :
    (.base u : (D.hookFrame I).World) ∈ D.detached I ↔ D.path 0 ∉ D.F.Reach u := by
  simp [detached];

lemma eq_dBot_or_isUnwound_of_mem_detached (hx : x ∈ D.detached I) :
    x = .dBot ∨ x.IsUnwound := by
  rcases hx with rfl | ⟨u, rfl, -⟩;
  · exact Or.inl rfl;
  · exact Or.inr trivial;

lemma mem_detached_of_rel (hx : x ∈ D.detached I) (Rxy : x ≺ y) : y ∈ D.detached I := by
  rcases hx with rfl | ⟨u, rfl, hu⟩;
  · rw [(rel_dBot_iff.mp Rxy).1];
    exact dBot_mem_detached;
  · rcases rel_base_iff.mp Rxy with ⟨v, rfl, Ruv⟩ | ⟨rfl, -⟩;
    · exact base_mem_detached_iff.mpr fun hv => hu <| reach_trans (mem_reach_of_rel Ruv) hv;
    · exact absurd self_mem_reach hu;

lemma relItr_base_iff_of_not_mem_reach {u : D.F.World} (hu : D.path 0 ∉ D.F.Reach u) :
    ((.base u : (D.hookFrame I).World) ≺^[n] y) ↔
      ∃ v : D.F.World, (u ≺^[n] v) ∧ y = .base v := by
  induction n generalizing y with
  | zero => simp [eq_comm];
  | succ n ih =>
    constructor;
    · intro h;
      obtain ⟨z, h₁, h₂⟩ := iff_relItr_succ'.mp h;
      obtain ⟨w, hw, rfl⟩ := ih.mp h₁;
      rcases rel_base_iff.mp h₂ with ⟨v, rfl, hwv⟩ | ⟨rfl, -⟩;
      · exact ⟨v, relItr_tail hw hwv, rfl⟩;
      · exact absurd (mem_reach_of_relItr hw) hu;
    · rintro ⟨v, h, rfl⟩;
      exact relItr_base h;

def pointGenerateBase {u : D.F.World} (hu : D.path 0 ∉ D.F.Reach u) :
    D.F⥜u →ₚ (D.hookFrame I)⥜(.base u) where
  toFun v := ⟨.base v.1, v.2.elim fun _ h => mem_reach_of_relItr <| relItr_base h⟩
  forth h := h
  back {v z} h := by
    obtain ⟨z, n, hn⟩ := z;
    obtain ⟨w, -, rfl⟩ := (relItr_base_iff_of_not_mem_reach hu).mp hn;
    exact ⟨⟨w, reach_of_rel v.2 h⟩, h, rfl⟩;

lemma pointGenerateBase_surjective {u : D.F.World} (hu : D.path 0 ∉ D.F.Reach u) :
    Function.Surjective (pointGenerateBase (I := I) hu) := by
  rintro ⟨z, n, hn⟩;
  obtain ⟨w, hw, rfl⟩ := (relItr_base_iff_of_not_mem_reach hu).mp hn;
  exact ⟨⟨w, n, hw⟩, rfl⟩;

lemma pointGenerate_base_validates {α : Type*} {L : NormalLogic α} {u : D.F.World}
    (hu : D.path 0 ∉ D.F.Reach u) (h : D.F⥜u ⊧ L) :
    (D.hookFrame I)⥜(.base u) ⊧ L :=
  ValidateLogic.of_surjective_pMorphism (pointGenerateBase hu) (pointGenerateBase_surjective hu) h

lemma surjective_to_pointGenerate_dBot {ι : Type*}
    (f : ι → ((D.hookFrame I)⥜.dBot).World) [Nonempty ι] :
    Function.Surjective f := by
  rintro ⟨z, n, hn⟩;
  obtain rfl := eq_dBot_of_dBot_relItr hn;
  obtain ⟨k, hk⟩ := (f (Classical.arbitrary ι)).2;
  exact ⟨Classical.arbitrary ι, Subtype.ext <| eq_dBot_of_dBot_relItr hk⟩;

lemma pointGenerate_dBot_validates {α : Type*} {L : NormalLogic α}
    (h₁ : ¬D.refl → deadEnd ⊧ L) (h₂ : D.refl → reflPoint ⊧ L) :
    (D.hookFrame I)⥜.dBot ⊧ L := by
  by_cases hr : D.refl;
  · let f : reflPoint →ₚ (D.hookFrame I)⥜.dBot :=
      { toFun := fun _ => (pointGenerate.root _ _).1
        forth := fun _ => hr
        back := by
          rintro _ ⟨z, n, hn⟩ -;
          obtain rfl := eq_dBot_of_dBot_relItr hn;
          exact ⟨0, trivial, rfl⟩ };
    exact ValidateLogic.of_surjective_pMorphism f (surjective_to_pointGenerate_dBot f) (h₂ hr);
  · let f : deadEnd →ₚ (D.hookFrame I)⥜.dBot :=
      { toFun := fun _ => (pointGenerate.root _ _).1
        forth := fun h => h.elim
        back := fun h => absurd (rel_dBot_iff.mp h).2 hr };
    exact ValidateLogic.of_surjective_pMorphism f (surjective_to_pointGenerate_dBot f) (h₁ hr);

/-- If `x ∈ D.detached I` and `φ ∈ L`, then `x ⊩[(D.hooked I).model V] φ`, provided
`D.F⥜u ⊧ L` for every non-root `u`, `deadEnd ⊧ L` when `¬D.refl`, and `reflPoint ⊧ L` when
`D.refl`.
- [CZ98, p. 367]
-/
lemma forces_of_mem_detached {α : Type*} {L : NormalLogic α}
    (hF : ∀ u : D.F.World, ¬D.F.IsRootedBy u → D.F⥜u ⊧ L)
    (h₁ : ¬D.refl → deadEnd ⊧ L) (h₂ : D.refl → reflPoint ⊧ L)
    (hx : x ∈ D.detached I) {φ : Formula α} (hA : φ ∈ L) (V : D.World I → α → Prop) :
    x ⊩[(D.hooked I).model V] φ := by
  rcases hx with rfl | ⟨u, rfl, hu⟩;
  · exact GeneralFrame.forces_of_pointGenerate_validatesLogic
      (G := D.hooked I) (pointGenerate_dBot_validates h₁ h₂) hA V;
  · apply GeneralFrame.forces_of_pointGenerate_validatesLogic (G := D.hooked I) _ hA V;
    apply pointGenerate_base_validates hu;
    exact hF u fun hr => hu <| hr _;

/-- If `D.refl` and every point of `D.F` has a successor, then every point of the hooked frame
has a successor.
- [CZ98, p. 367]
-/
lemma exists_rel (hr : D.refl) (hF : ∀ u : D.F.World, ∃ v, u ≺ v) (x : (D.hookFrame I).World) :
    ∃ y, x ≺ y := by
  cases x with
  | base u =>
    obtain ⟨v, hv⟩ := hF u;
    exact ⟨.base v, hv⟩;
  | copy t ht => exact ⟨.base (D.path (t + 2)), D.path_rel (t + 1)⟩;
  | c => exact ⟨.b, by simp [Rel]⟩;
  | b => exact ⟨.a 0 false (by simp), by simp [Rel]⟩;
  | a i t h =>
    rcases Nat.eq_zero_or_pos i with rfl | hi;
    · exact ⟨.d D.m le_rfl, by simp [Rel]⟩;
    · exact ⟨.a 0 false (by simp), by simpa [Rel] using hi⟩;
  | d j hj =>
    cases j with
    | zero => exact ⟨.dBot, by simp [Rel]⟩;
    | succ j => exact ⟨.d j (by omega), by simp [Rel]⟩;
  | dBot => exact ⟨.dBot, hr⟩;

variable [Finite D.F.World]

/-- If `x ∉ D.detached I`, then `x ≺^[n] .d 0 _` for some `n ≤ D.m + 3`.
- [CZ98, p. 367]
-/
lemma exists_relItr_d_zero (hx : x ∉ D.detached I) :
    ∃ n ≤ D.m + 3, x ≺^[n] .d 0 (Nat.zero_le _) := by
  have hm := D.card_add_len_lt;
  have hcopy (t : ℕ) (ht : t ≤ D.len) :
      RelItr (F := D.hookFrame I) (D.len - t + 1) (.copy t ht) (.d 0 (Nat.zero_le _)) :=
    relItr_tail (relItr_copy (ht' := le_rfl) ht) (by simp [Rel]);
  have hdm : RelItr (F := D.hookFrame I) (D.m - 0) (.d D.m le_rfl) (.d 0 (Nat.zero_le _)) :=
    relItr_d (Nat.zero_le _);
  have ha₀ : RelItr (F := D.hookFrame I) (D.m - 0 + 1) (.a 0 false (by simp))
      (.d 0 (Nat.zero_le _)) :=
    relItr_head (by simp [Rel]) hdm;
  cases x with
  | base u =>
    have hu : D.path 0 ∈ D.F.Reach u := by simpa using hx;
    obtain ⟨k, hk, hku⟩ := exists_relItr_lt_card hu;
    exact ⟨_, by omega, relItr_trans (relItr_base hku) <|
      relItr_head (y := .copy 0 (Nat.zero_le _)) (by simp [Rel]) (hcopy 0 _)⟩;
  | copy t ht => exact ⟨_, by omega, hcopy t ht⟩;
  | c => exact ⟨_, by omega, relItr_head (y := .b) (by simp [Rel]) <|
      relItr_head (by simp [Rel]) ha₀⟩;
  | b => exact ⟨_, by omega, relItr_head (by simp [Rel]) ha₀⟩;
  | a i t h =>
    rcases Nat.eq_zero_or_pos i with rfl | hi;
    · exact ⟨_, by omega, relItr_head (by simp [Rel]) hdm⟩;
    · exact ⟨_, by omega, relItr_head (by simpa [Rel] using hi) ha₀⟩;
  | d j hj => exact ⟨_, by omega, relItr_d (Nat.zero_le j)⟩;
  | dBot => exact absurd dBot_mem_detached hx;

/-- `.d 0 _ ≺^[n] y` for some `n ≤ D.m + 4`.
- [CZ98, p. 367]
-/
lemma d_zero_exists_relItr (y : (D.hookFrame I).World) :
    ∃ n ≤ D.m + 4, RelItr (F := D.hookFrame I) n (.d 0 (Nat.zero_le _)) y := by
  have hm := D.card_add_len_lt;
  have hb : RelItr (F := D.hookFrame I) (1 + 1) (.d 0 (Nat.zero_le _)) .b :=
    relItr_head (y := .c) (by simp [Rel]) <| relItr_head (by simp [Rel]) relItr_zero_self;
  have hroot (v : D.F.World) : ∃ k < Nat.card D.F.World,
      RelItr (F := D.hookFrame I) (1 + k) (.d 0 (Nat.zero_le _)) (.base v) := by
    obtain ⟨k, hk, hkv⟩ := exists_relItr_lt_card (D.root.2 v);
    exact ⟨k, hk, relItr_trans (n := 1) (by simp [Rel]) (relItr_base hkv)⟩;
  cases y with
  | base v =>
    obtain ⟨k, hk, h⟩ := hroot v;
    exact ⟨_, by omega, h⟩;
  | copy t ht =>
    obtain ⟨k, hk, h⟩ := hroot (D.path 0);
    exact ⟨_, by omega, relItr_trans h <| relItr_head (y := .copy 0 (Nat.zero_le _))
      (by simp [Rel]) (relItr_copy (ht' := ht) (Nat.zero_le t))⟩;
  | c => exact ⟨1, by omega, by simp [Rel]⟩;
  | b => exact ⟨_, by omega, hb⟩;
  | a i t h => exact ⟨_, by omega, relItr_tail hb (z := .a i t h) (by simp [Rel])⟩;
  | d j hj =>
    exact ⟨_, by omega, relItr_trans hb <| relItr_head (y := .a 0 false (by simp))
      (by simp [Rel]) <| relItr_head (by simp [Rel]) (relItr_d (hj' := le_rfl) hj)⟩;
  | dBot => exact ⟨1, by omega, by simp [Rel]⟩;

/-- If `x ∉ D.detached I`, then `x ≺^[n] y` for some `n ≤ 2 * D.m + 7`.
- [CZ98, p. 367]
-/
lemma exists_relItr_of_not_mem_detached (hx : x ∉ D.detached I) (y : (D.hookFrame I).World) :
    ∃ n ≤ 2 * D.m + 7, x ≺^[n] y := by
  obtain ⟨k, hk, h⟩ := exists_relItr_d_zero hx;
  obtain ⟨k', hk', h'⟩ := d_zero_exists_relItr y;
  exact ⟨_, by omega, relItr_trans h h'⟩;

lemma exists_relItr_c (hx : x ∉ D.detached I) : ∃ n ≤ D.m + 4, x ≺^[n] .c := by
  obtain ⟨k, hk, h⟩ := exists_relItr_d_zero hx;
  exact ⟨_, by omega, relItr_tail h (by simp [Rel])⟩;

lemma exists_relItr_dBot (hx : x ∉ D.detached I) : ∃ n ≤ D.m + 4, x ≺^[n] .dBot := by
  obtain ⟨k, hk, h⟩ := exists_relItr_d_zero hx;
  exact ⟨_, by omega, relItr_tail h (by simp [Rel])⟩;

end Reach


section Unwound

/-! ### The size of the unwound frame -/

variable (D I) in
def unwoundPoint : D.F.World ⊕ Fin (D.len + 1) → D.World I
  | .inl u => .base u
  | .inr t => .copy t (by omega)

lemma range_unwoundPoint : Set.range (D.unwoundPoint I) = {w | w.IsUnwound} := by
  ext w;
  constructor;
  · rintro ⟨u | t, rfl⟩ <;> trivial;
  · intro hw;
    rcases isUnwound_iff.mp hw with ⟨u, rfl⟩ | ⟨t, ht, rfl⟩;
    · exact ⟨.inl u, rfl⟩;
    · exact ⟨.inr ⟨t, by omega⟩, rfl⟩;

variable [Finite D.F.World]

lemma finite_isUnwound : {w : D.World I | w.IsUnwound}.Finite :=
  range_unwoundPoint ▸ Set.finite_range _

lemma ncard_isUnwound_le :
    {w : D.World I | w.IsUnwound}.ncard ≤ Nat.card D.F.World + D.len + 1 := by
  rw [← range_unwoundPoint, ← Set.image_univ];
  calc (D.unwoundPoint I '' Set.univ).ncard
      ≤ (Set.univ : Set (D.F.World ⊕ Fin (D.len + 1))).ncard := Set.ncard_image_le Set.finite_univ
    _ = Nat.card D.F.World + D.len + 1 := by simp [Set.ncard_univ, Nat.card_sum]; omega;

lemma ncard_isUnwound_lt : {w : D.World I | w.IsUnwound}.ncard < D.m := by
  have := D.card_add_len_lt;
  have := ncard_isUnwound_le (D := D) (I := I);
  omega;

end Unwound

end HookData

end
