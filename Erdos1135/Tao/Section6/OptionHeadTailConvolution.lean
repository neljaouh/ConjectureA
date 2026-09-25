import Erdos1135.Tao.Probability.GatedSubmass
import Erdos1135.Tao.Section6.FiniteFourierConvolution

open scoped BigOperators

namespace Erdos1135

namespace Tao

noncomputable section

noncomputable def taoOptionHeadTailKernel
    {N : ℕ} [NeZero N] (tau : PMF (ZMod N)) :
    Option (ZMod N) → PMF (Option (ZMod N))
  | none => PMF.pure none
  | some y => tau.map (fun z => some (y + z))

noncomputable def taoOptionHeadTailPMF
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) :
    PMF (Option (ZMod N)) :=
  h.bind (taoOptionHeadTailKernel tau)

theorem taoOptionHeadTailKernel_apply_some
    {N : ℕ} [NeZero N] (tau : PMF (ZMod N)) (x y : ZMod N) :
    taoOptionHeadTailKernel tau (some y) (some x) = tau (x - y) := by
  unfold taoOptionHeadTailKernel
  rw [PMF.map_apply]
  rw [tsum_eq_single (x - y)]
  · simp
  · intro z hz
    have hne : some x ≠ some (y + z) := by
      intro h
      apply hz
      simpa [eq_sub_iff_add_eq, add_comm] using (Option.some.inj h).symm
    simp [hne]

theorem taoOptionHeadTailPMF_apply_some
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) (x : ZMod N) :
    taoOptionHeadTailPMF h tau (some x) =
      ∑ y : ZMod N, h (some y) * tau (x - y) := by
  unfold taoOptionHeadTailPMF
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  have hnone :
      (PMF.pure none : PMF (Option (ZMod N))) (some x) = 0 := by
    simp
  rw [show taoOptionHeadTailKernel tau none = PMF.pure none by rfl]
  rw [hnone, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [taoOptionHeadTailKernel_apply_some]

theorem taoOptionHeadTailPMF_apply_some_toReal
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) (x : ZMod N) :
    (taoOptionHeadTailPMF h tau (some x)).toReal =
      ∑ y : ZMod N, (h (some y)).toReal * (tau (x - y)).toReal := by
  rw [taoOptionHeadTailPMF_apply_some]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro y _hy
    exact ENNReal.mul_ne_top (h.apply_ne_top (some y))
      (tau.apply_ne_top (x - y))

theorem taoOptionHeadTailPMF_apply_some_toReal_eq_rawConvolution
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) (x : ZMod N) :
    (taoOptionHeadTailPMF h tau (some x)).toReal =
      taoZModRawConvolution
        (fun y => (h (some y)).toReal)
        (fun z => (tau z).toReal) x := by
  rw [taoOptionHeadTailPMF_apply_some_toReal]
  rfl

end

end Tao

end Erdos1135
