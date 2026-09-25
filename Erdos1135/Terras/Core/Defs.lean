import Erdos1135.CollatzStep
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos1135

namespace Terras

def twoAdicExponent (n : ℕ) : ℕ :=
  n.factorization 2

def oddOnly (n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ twoAdicExponent (3 * n + 1)

end Terras

end Erdos1135
