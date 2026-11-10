module

public import K4S4.Construction.Frame
public import Mathlib.Tactic.FinCases

/-!
# The four minimal nonterminal points
-/

@[expose] public section

namespace Modal.K4S4.Construction

variable {I : Set ℕ}

def basePoint (k : Fin 4) : Point I :=
  if h : k.val < 3 then .ladder ⟨k.val, h⟩ 0 else .h

@[simp] lemma basePoint_castSucc (k : Fin 3) : basePoint (I := I) k.castSucc = .ladder k 0 := by
  simp [basePoint, k.isLt];

@[simp] lemma basePoint_three : basePoint (I := I) 3 = .h := rfl

lemma basePoint_nonterminal (k : Fin 4) :
    (basePoint k : Point I) ≠ .o ∧ (basePoint k : Point I) ≠ .o' := by
  unfold basePoint;
  split <;> simp;

lemma basePoint_injective : Function.Injective (basePoint (I := I)) := by
  intro k l h;
  fin_cases k <;> fin_cases l <;> simp_all [basePoint];

lemma exists_basePoint {x : Point I} (hx : x ≠ .o ∧ x ≠ .o') :
    ∃ j : Fin 4, rel x (basePoint j) := by
  cases x with
  | o => exact False.elim <| hx.1 rfl;
  | o' => exact False.elim <| hx.2 rfl;
  | r => exact ⟨3, by simp [rel]⟩;
  | h => exact ⟨3, by simp [basePoint, rel]⟩;
  | ladder k n =>
    use ⟨k.val, by omega⟩;
    simp [basePoint, k.isLt, rel, ladderRel];
    omega;
  | d n => exact ⟨0, by simp [basePoint, rel]⟩;
  | e n => exact ⟨0, by simp [basePoint, rel]⟩;
  | y n => exact ⟨0, by simp [basePoint, rel]⟩;

lemma eq_basePoint_of_unique {x : Point I} (hx : x ≠ .o ∧ x ≠ .o') (k : Fin 4)
    (h : ∀ j, rel x (basePoint j) → j = k) : x = basePoint k := by
  have h₀ := h 0;
  have h₁ := h 1;
  have h₂ := h 2;
  have h₃ := h 3;
  clear h;
  fin_cases k <;> cases x <;> simp_all [basePoint, rel, ladderRel] <;> omega;

lemma exists_ladder_succ_sees_base_pair {a b : Fin 4}
    (ha : a ≠ 3) (hb : b ≠ 3) (hab : a ≠ b) :
    ∃ k : Fin 3, rel (Point.ladder k 1 : Point I) (basePoint a) ∧
      rel (Point.ladder k 1 : Point I) (basePoint b) := by
  fin_cases a <;> fin_cases b;
  all_goals solve | exact False.elim <| ha rfl | exact False.elim <| hb rfl |
    exact False.elim <| hab rfl | (use 0; simp [basePoint, rel, ladderRel]) |
    (use 1; simp [basePoint, rel, ladderRel]) | (use 2; simp [basePoint, rel, ladderRel]);

end Modal.K4S4.Construction
