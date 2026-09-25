import Erdos1135.CollatzStep
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Probability.Geom2TerminalMoment
import Erdos1135.Tao.Section5.FiveStepCompression
import Erdos1135.Tao.Syracuse.AffineOdd
import Erdos1135.Tao.Syracuse.AffineTrajectory
import Erdos1135.Tao.Syracuse.Defs
import Erdos1135.Tao.Syracuse.FirstPassageInterval
import Erdos1135.Tao.Syracuse.ParityBridge
import Erdos1135.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135.Terras.Core.Defs
import Erdos1135.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace Erdos1135

namespace Tao

noncomputable section

theorem taoTupleWeight_eq_dropLast_add_terminalValue (bs : List ℕ+) :
    taoTupleWeight bs =
      taoTupleWeight bs.dropLast + geom2PNatListTerminalValue bs := by
  by_cases hbs : bs = []
  · simp [hbs, taoTupleWeight, geom2PNatListTerminalValue]
  · calc
      taoTupleWeight bs =
          taoTupleWeight (bs.dropLast ++ [bs.getLast hbs]) := by
        rw [List.dropLast_append_getLast hbs]
      _ = taoTupleWeight bs.dropLast +
          taoTupleWeight [bs.getLast hbs] :=
        taoTupleWeight_append_trajectory _ _
      _ = taoTupleWeight bs.dropLast +
          geom2PNatListTerminalValue bs := by
        rw [geom2PNatListTerminalValue_eq_getLast hbs]
        simp [taoTupleWeight]

end

end Tao

end Erdos1135
