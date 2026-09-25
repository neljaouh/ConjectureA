import Erdos1135.Basic
import Erdos1135.Tao.Fourier.Section7SChiActualQ
import Erdos1135.Tao.Fourier.Section7SourceLaw
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Section5.AffineSourceLaw
import Erdos1135.Tao.Section6.FiniteFourierCollision
import Erdos1135.Tao.Section6.GatedSourceConvolution
import Erdos1135.Tao.Section6.ModulusProjection
import Erdos1135.Tao.Syracuse.AffineTrajectory
import Erdos1135.Tao.Syracuse.Defs
import Erdos1135.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace Erdos1135

namespace ND

open scoped BigOperators

open Tao

noncomputable section

noncomputable def ndPMFWeightedExpectation
    {alpha : Type*} (p : PMF alpha) (phi : alpha → ℝ) : ℝ :=
  ∑' u, (p u).toReal * phi u

end

end ND

end Erdos1135
