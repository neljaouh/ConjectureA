import Erdos1135.Tao.Syracuse.Syrac
import Mathlib.Analysis.Fourier.ZMod

open scoped BigOperators

open scoped ZMod

namespace Erdos1135

namespace Tao

noncomputable def pmfComplexMass {α : Type*} (p : PMF α) : α → ℂ :=
  fun x => ((p x).toReal : ℂ)

noncomputable def taoForwardDFTKernel {N : ℕ} [NeZero N] (x ξ : ZMod N) : ℂ :=
  ZMod.stdAddChar (-(x * ξ))

theorem tao_dft_apply {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (ξ : ZMod N) :
    ZMod.dft Φ ξ = ∑ x : ZMod N, taoForwardDFTKernel x ξ • Φ x := by
  rw [ZMod.dft_apply]
  simp [taoForwardDFTKernel]

theorem tao_dft_pmfComplexMass_apply {N : ℕ} [NeZero N]
    (p : PMF (ZMod N)) (ξ : ZMod N) :
    ZMod.dft (pmfComplexMass p) ξ =
      ∑ x : ZMod N, taoForwardDFTKernel x ξ * (((p x).toReal : ℝ) : ℂ) := by
  rw [tao_dft_apply]
  simp [taoForwardDFTKernel, pmfComplexMass, smul_eq_mul]

end Tao

end Erdos1135
