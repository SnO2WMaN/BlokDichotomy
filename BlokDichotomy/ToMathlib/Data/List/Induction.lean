module

public import Mathlib.Data.List.Basic

/-!
# Induction on lists with a separate singleton case
-/

@[expose] public section

namespace List

/-- Induction on a list where the step case only adds an element to a nonempty list. -/
@[elab_as_elim]
lemma induction_with_singleton {α : Type*} {p : List α → Prop} (nil : p []) (singleton : ∀ a, p [a])
    (cons : ∀ a l, l ≠ [] → p l → p (a :: l)) : ∀ l, p l
  | [] => nil
  | [a] => singleton a
  | a :: b :: l => cons a (b :: l) (by simp) (induction_with_singleton nil singleton cons (b :: l))

end List

end
