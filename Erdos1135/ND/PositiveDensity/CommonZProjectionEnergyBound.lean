import Erdos1135.CollatzStep
import Erdos1135.ND.PositiveDensity.CommonZEndpointPrefixFactorization
import Erdos1135.ND.PositiveDensity.CommonZFullReverseKernel
import Erdos1135.Tao.Fourier.MixingStatement
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Probability.Geom2CenteredMoment
import Erdos1135.Tao.Probability.Geom2ListReverse
import Erdos1135.Tao.Probability.Geom2TerminalMoment
import Erdos1135.Tao.Section5.EndpointRatio
import Erdos1135.Tao.Section5.FiveStepCompression
import Erdos1135.Tao.Section6.UniformLift
import Erdos1135.Tao.Syracuse.AffineOdd
import Erdos1135.Tao.Syracuse.AffineTrajectory
import Erdos1135.Tao.Syracuse.Defs
import Erdos1135.Tao.Syracuse.FirstPassageInterval
import Erdos1135.Tao.Syracuse.ParityBridge
import Erdos1135.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135.Terras.Core.Defs
import Erdos1135.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Erdos1135

namespace ND

namespace PositiveDensity

open scoped BigOperators

noncomputable section

def ndTernaryUniformScale (q : ℕ) : ℝ :=
  1 / ((3 ^ q : ℕ) : ℝ)

def ndTernaryUniformMean (q : ℕ) (f : ZMod (3 ^ q) → ℝ) : ℝ :=
  ndTernaryUniformScale q * ∑ x, f x

def ndSyracuseUniformDensity (q : ℕ) (x : ZMod (3 ^ q)) : ℝ :=
  ((3 ^ q : ℕ) : ℝ) * Tao.syracPMFMassVector q x

end

end PositiveDensity

end ND

end Erdos1135
