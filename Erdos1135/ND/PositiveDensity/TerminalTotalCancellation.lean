import Erdos1135.Basic
import Erdos1135.ND.Fourier.FixedTotalReferenceRatio
import Erdos1135.Tao.Fourier.Section7SChiActualQ
import Erdos1135.Tao.Fourier.Section7SourceLaw
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Probability.Geom2ListProjectivity
import Erdos1135.Tao.Section5.AffineSourceLaw
import Erdos1135.Tao.Section6.FiniteFourierCollision
import Erdos1135.Tao.Section6.GatedSourceConvolution
import Erdos1135.Tao.Syracuse.AffineReverse
import Erdos1135.Tao.Syracuse.AffineTrajectory
import Erdos1135.Tao.Syracuse.Defs
import Erdos1135.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace Erdos1135

namespace ND

namespace PositiveDensity

noncomputable section

theorem summable_pmf_toReal_mul_of_abs_le
    {alpha : Type*} (p : PMF alpha) (phi : alpha → ℝ) (H : ℝ)
    (_hH : 0 ≤ H) (hphi : ∀ x, |phi x| ≤ H) :
    Summable fun x => (p x).toReal * phi x := by
  refine Summable.of_norm_bounded
    ((Tao.taoPMF_summable_toReal p).mul_right H) ?_
  intro x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hphi x) ENNReal.toReal_nonneg

end

end PositiveDensity

end ND

end Erdos1135
