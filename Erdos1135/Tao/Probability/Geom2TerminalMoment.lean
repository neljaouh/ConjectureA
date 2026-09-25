import Erdos1135.Tao.Probability.CountableMarkov
import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Probability.Geom2ListProjectivity

namespace Erdos1135

namespace Tao

noncomputable section

def geom2PNatListTerminalValue (as : List ℕ+) : ℕ :=
  match as.getLast? with
  | none => 0
  | some a => (a : ℕ)

theorem geom2PNatListTerminalValue_eq_getLast
    {as : List ℕ+} (has : as ≠ []) :
    geom2PNatListTerminalValue as = (as.getLast has : ℕ) := by
  simp [geom2PNatListTerminalValue,
    List.getLast?_eq_getLast_of_ne_nil has]

end

end Tao

end Erdos1135
