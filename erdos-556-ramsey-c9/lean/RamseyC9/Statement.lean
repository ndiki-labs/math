import Std

namespace RamseyC9

abbrev EdgeColouring (n : Nat) := Fin n → Fin n → Fin 3

def next (i : Fin 9) : Fin 9 := ⟨(i.val + 1) % 9, by omega⟩

/-- A copy of the cycle uses nine distinct vertices. The closing edge is included. -/
def MonochromaticC9 (colour : EdgeColouring n) : Prop :=
  ∃ vertices : Fin 9 → Fin n, Function.Injective vertices ∧
    ∃ c : Fin 3, ∀ i, colour (vertices i) (vertices (next i)) = c

/-- Symmetric colourings represent all edge colourings of the complete graph. -/
def HasRamseyProperty (n : Nat) : Prop :=
  ∀ colour : EdgeColouring n, (∀ u v, colour u v = colour v u) → MonochromaticC9 colour

/-- The order is the least at which every three-colouring has a monochromatic C₉. -/
def IsRamseyNumber (n : Nat) : Prop :=
  HasRamseyProperty n ∧ ∀ m < n, ¬ HasRamseyProperty m

end RamseyC9
