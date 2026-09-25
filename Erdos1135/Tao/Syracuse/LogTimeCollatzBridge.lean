import Erdos1135.Tao.Syracuse.CollatzBridge
import Erdos1135.Tao.Syracuse.ParityBridge

namespace Erdos1135

namespace Tao

noncomputable section

theorem collatz_iterate_syracuseValuationTime
    (n M : ℕ) (hM : Odd M) :
    (collatzStep^[n +
      taoTupleWeight (syracuseValuationPNatList n M hM)]) M =
        (syracuse^[n]) M := by
  induction n generalizing M with
  | zero =>
      simp [syracuseValuationPNatList, taoTupleWeight]
  | succ n ih =>
      let a : ℕ := syracuseExponent M
      let W : ℕ := taoTupleWeight
        (syracuseValuationPNatList n (syracuse M) (syracuse_odd M))
      have htime :
          n + 1 + (a + W) = (n + W) + (a + 1) := by omega
      simp only [syracuseValuationPNatList, taoTupleWeight,
        Function.iterate_succ_apply]
      change (collatzStep^[n + 1 + (a + W)]) M =
        (syracuse^[n]) (syracuse M)
      rw [htime, Function.iterate_add_apply]
      rw [collatz_iterate_syracuse_block hM]
      exact ih (syracuse M) (syracuse_odd M)

end

end Tao

end Erdos1135
