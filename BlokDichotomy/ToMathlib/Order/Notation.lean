module

public import Mathlib.Init

/-!
# Notation classes for modal operators

The notation classes `Box` and `Dia` for the unary operators `□` and `◇`, in the manner of the
notation classes `Max`, `Compl` and `HImp` for `⊔`, `ᶜ` and `⇨`.
-/

@[expose] public section

universe u

/-- Notation class for the necessity operator `□`. -/
class Box (α : Type u) where
  box : α → α

/-- Notation class for the possibility operator `◇`. -/
class Dia (α : Type u) where
  dia : α → α

@[inherit_doc] prefix:95 "□" => Box.box
@[inherit_doc] prefix:95 "◇" => Dia.dia

attribute [match_pattern] Box.box Dia.dia

end
