module

public import BlokDichotomy.Modal.Kripke.Correspondence
public import BlokDichotomy.Modal.Kripke.Degree

/-!
# An indexed construction above S4

Points and naming formulas for reflexive transitive frames with a three-column ladder,
an ascending chain, and independently optional coding points.
-/

@[expose] public section

namespace Modal.K4S4.Construction

inductive Point (I : Set ℕ)
  | r
  | h
  | o
  | o'
  | ladder (k : Fin 3) (n : ℕ)
  | d (n : ℕ)
  | e (n : I)
  | y (n : ℕ)
  deriving DecidableEq

open Formula

def terminalType : Bool → Formula ℕ
  | true => #0 ⋏ #1 ⋏ #2
  | false => ∼#0 ⋏ ∼#1 ⋏ ∼#2

def ladderType (k : Fin 3) : Formula ℕ :=
  (if k = 0 then #0 else ∼#0) ⋏
    (if k = 1 then #1 else ∼#1) ⋏ (if k = 2 then #2 else ∼#2)

def markerType : Formula ℕ := #0 ⋏ #1 ⋏ ∼#2

def nameO : Formula ℕ := □(terminalType true)

def nameO' : Formula ℕ := □(terminalType false)

def mu : Formula ℕ := ◇nameO ⋏ ◇nameO'

def nameH : Formula ℕ := mu ⋏ markerType ⋏ □(mu 🡒 markerType)

def nameLadder : Fin 3 → ℕ → Formula ℕ
  | k, 0 => mu ⋏ ladderType k ⋏ □(mu 🡒 ladderType k)
  | k, n + 1 =>
    ∼(nameLadder 0 n ⋎ nameLadder 1 n ⋎ nameLadder 2 n) ⋏
      ◇(nameLadder k n) ⋏ ◇(nameLadder (k + 1) n) ⋏ ∼◇(nameLadder (k + 2) n)

def tau (n : ℕ) : Formula ℕ := nameLadder 0 n ⋎ nameLadder 1 n ⋎ nameLadder 2 n

def exactlyOne (A B C : Formula ℕ) : Formula ℕ :=
  (A ⋏ ∼B ⋏ ∼C) ⋎ (∼A ⋏ B ⋏ ∼C) ⋎ (∼A ⋏ ∼B ⋏ C)

def nameD (n : ℕ) : Formula ℕ :=
  ◇(nameLadder 0 n) ⋏ ◇(nameLadder 1 n) ⋏ ◇(nameLadder 2 n) ⋏ ∼◇(tau (n + 1))

def nameE (n : ℕ) : Formula ℕ :=
  ∼(nameD n) ⋏ ◇(nameD n) ⋏ exactlyOne
    (◇(nameLadder 0 (n + 1))) (◇(nameLadder 1 (n + 1))) (◇(nameLadder 2 (n + 1)))

def nameY : ℕ → Formula ℕ
  | 0 => ∼(nameD 0) ⋏ ◇(nameD 0) ⋏ ◇(nameD 1) ⋏ ∼◇nameH
  | n + 1 =>
    ∼(nameD (n + 1)) ⋏ ◇(nameD (n + 1)) ⋏ ◇(nameD (n + 2)) ⋏ ∼◇(nameD n)

def nameR : Formula ℕ :=
  ◇(nameLadder 0 0) ⋏ ◇(nameLadder 1 0) ⋏ ◇(nameLadder 2 0) ⋏ ◇nameH ⋏ ◇(nameY 0)

def sigma : Formula ℕ :=
  let A := (#3 : Formula ℕ)
  let B := ∼A ⋏ #4
  ∼(A ⋏ ((A 🡒 ◇B) ⋏ □(A 🡒 ◇B)) ⋏ ((B 🡒 ◇A) ⋏ □(B 🡒 ◇A)))

def theta (n : ℕ) : Formula ℕ :=
  nameR 🡒 □(nameY n 🡒 ◇(nameY (n + 1) ⋏ ∼◇(nameY n)))

def chi (n : ℕ) : Formula ℕ := nameR 🡒 ∼◇(nameE n)

/-- `S4` extended by the chain formula and all transition formulas. -/
abbrev baseLogic : NormalLogic ℕ := 𝐒𝟒 + insert sigma (Set.range theta)

/-- The base logic extended by the coding formulas for indices outside `I`. -/
abbrev sourceLogic (I : Set ℕ) : NormalLogic ℕ := baseLogic + chi '' Iᶜ

end Modal.K4S4.Construction
