import Erdos1135.Tao.Fourier.Basic
import Mathlib.Analysis.Complex.Norm

open scoped BigOperators

open scoped ZMod

namespace Erdos1135

namespace Tao

def zmodThreeMultiple (n : ℕ) (ξ : ZMod (3 ^ n)) : Prop :=
  ∃ η : ZMod (3 ^ n), ξ = (3 : ZMod (3 ^ n)) * η

def zmodThreePrimitive (n : ℕ) (ξ : ZMod (3 ^ n)) : Prop :=
  ¬ zmodThreeMultiple n ξ

def syracPMFPrimitiveDFTBound (n : ℕ) (B : ℝ) : Prop :=
  ∀ ξ : ZMod (3 ^ n), zmodThreePrimitive n ξ →
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) ξ‖ ≤ B

def syracPMFPrimitivePolynomialDecayAt (A : ℕ) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    syracPMFPrimitiveDFTBound n (C / (n : ℝ) ^ A)

theorem syracPMFPrimitivePolynomialDecayAt.apply
    {A n : ℕ} {C : ℝ}
    (h : syracPMFPrimitivePolynomialDecayAt A C) (hn : 1 ≤ n)
    {ξ : ZMod (3 ^ n)} (hξ : zmodThreePrimitive n ξ) :
    ‖ZMod.dft (pmfComplexMass (syracPMF n)) ξ‖ ≤ C / (n : ℝ) ^ A :=
  h n hn ξ hξ

end Tao

end Erdos1135
