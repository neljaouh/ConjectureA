import Erdos1135.Tao.Syracuse.AffineTrajectory
import Erdos1135.Tao.Syracuse.Defs
import Mathlib.Tactic

namespace Erdos1135

namespace Tao

noncomputable section

def syracuseTerminalExponentPNat
    (r M : ℕ) (hM : Odd M) : ℕ+ :=
  ⟨syracuseExponent ((syracuse^[r]) M),
    syracuseExponent_pos_of_odd
      (syracuse_iterate_odd_trajectory r M hM)⟩

theorem syracuseValuationPNatList_succ_eq_append_terminal
    (r M : ℕ) (hM : Odd M) :
    syracuseValuationPNatList (r + 1) M hM =
      syracuseValuationPNatList r M hM ++
        [syracuseTerminalExponentPNat r M hM] := by
  rw [syracuseValuationPNatList_add r 1 M hM]
  simp [syracuseValuationPNatList, syracuseTerminalExponentPNat]

theorem taoTupleWeight_syracuseValuationPNatList_succ
    (r M : ℕ) (hM : Odd M) :
    taoTupleWeight (syracuseValuationPNatList (r + 1) M hM) =
      taoTupleWeight (syracuseValuationPNatList r M hM) +
        (syracuseTerminalExponentPNat r M hM : ℕ) := by
  rw [syracuseValuationPNatList_succ_eq_append_terminal,
    taoTupleWeight_append_trajectory]
  simp [taoTupleWeight]

end

end Tao

end Erdos1135
