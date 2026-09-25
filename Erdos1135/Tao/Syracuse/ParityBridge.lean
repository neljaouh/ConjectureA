import Erdos1135.Tao.Syracuse.Affine
import Erdos1135.Terras.Core.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

namespace Erdos1135

namespace Tao

theorem syracuse_iterate_odd (n N : ℕ) (hN : Odd N) :
    Odd ((syracuse^[n]) N) := by
  induction n generalizing N with
  | zero =>
      simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (syracuse N) (syracuse_odd N)

end Tao

end Erdos1135
