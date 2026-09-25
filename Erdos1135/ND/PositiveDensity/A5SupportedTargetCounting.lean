import Erdos1135.Basic
import Erdos1135.ND.PositiveDensity.CommonZPathTelescoping
import Erdos1135.ND.PositiveDensity.CommonZReverseGenerator
import Erdos1135.ND.PositiveDensity.TargetCounting
import Erdos1135.Tao.Fourier.Section7SChiActualQ
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Probability.GatedSubmassPartition
import Erdos1135.Tao.Section5.FiveStepCompression
import Erdos1135.Tao.Syracuse.AffineEnvelope
import Erdos1135.Tao.Syracuse.AffineOdd
import Erdos1135.Tao.Syracuse.AffineResidue
import Erdos1135.Tao.Syracuse.AffineTrajectory
import Erdos1135.Tao.Syracuse.Defs
import Erdos1135.Tao.Syracuse.OddSource
import Erdos1135.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135.Tao.Syracuse.ValuationDistribution
import Erdos1135.Terras.Density.NaturalDensity
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Erdos1135

namespace ND

namespace PositiveDensity

noncomputable section

theorem finset_card_le_natCount_of_subset_range
    {S : Finset ℕ} {A : Set ℕ} {X : ℕ}
    (hX : S ⊆ Finset.range X) (hA : ↑S ⊆ A) :
    S.card ≤ Terras.natCount A X := by
  classical
  rw [Terras.natCount_eq_count, Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro N hN
  exact Finset.mem_filter.mpr ⟨hX hN, hA hN⟩

end

end PositiveDensity

end ND

end Erdos1135
