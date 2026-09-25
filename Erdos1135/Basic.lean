import FormalConjectures.Wikipedia.CollatzConjecture
import Mathlib.Tactic

open Function

namespace Erdos1135

abbrev collatzStep : ℕ → ℕ :=
  CollatzConjecture.collatzStep

end Erdos1135
