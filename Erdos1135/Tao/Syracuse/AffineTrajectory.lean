import Erdos1135.Tao.Syracuse.AffineEnvelope

namespace Erdos1135

namespace Tao

theorem syracuse_iterate_odd_trajectory
    (n N : ℕ) (hN : Odd N) : Odd ((syracuse^[n]) N) := by
  induction n generalizing N with
  | zero => simpa using hN
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (syracuse N) (syracuse_odd N)

theorem syracuseValuationPNatList_add
    (m n N : ℕ) (hN : Odd N) :
    syracuseValuationPNatList (m + n) N hN =
      syracuseValuationPNatList m N hN ++
        syracuseValuationPNatList n ((syracuse^[m]) N)
          (syracuse_iterate_odd_trajectory m N hN) := by
  induction m generalizing N with
  | zero =>
      simp [syracuseValuationPNatList]
  | succ m ih =>
      rw [Nat.succ_add]
      simp only [syracuseValuationPNatList, List.cons_append]
      rw [ih (syracuse N) (syracuse_odd N)]
      congr 2

theorem taoTupleWeight_append_trajectory (xs ys : List ℕ+) :
    taoTupleWeight (xs ++ ys) = taoTupleWeight xs + taoTupleWeight ys := by
  simp [taoTupleWeight]

end Tao

end Erdos1135
