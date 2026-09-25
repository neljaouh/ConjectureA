import Erdos1135.Tao.Fourier.Section7SourceDomain
import Erdos1135.Tao.Renewal.QActualLimit
import Erdos1135.Tao.Renewal.SourceListBridge

namespace Erdos1135

namespace Tao

noncomputable def taoSection7SourceActualW
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    TaoSection7RenewalPoint → Prop :=
  taoSection7SourceWhiteRenewal
    (taoSection7SourceWhiteWCutoff n xi epsilon (n / 2))

noncomputable def taoSection7SourceActualQ
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    TaoSection7RenewalPoint → ℝ :=
  taoSection7ActualQFiniteLimit epsilon
    (taoSection7SourceActualW n xi epsilon)

theorem taoSection7SourceActualQ_finiteLimit
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    TaoSection7ActualQFiniteLimitStatement epsilon
      (taoSection7SourceActualW n xi epsilon)
      (taoSection7SourceActualQ n xi epsilon) :=
  taoSection7ActualQFiniteLimit_statement hepsilon
    (taoSection7SourceActualW n xi epsilon)

theorem taoSection7SourceActualQ_bounded01
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    TaoSection7QBounded01
      (taoSection7SourceActualQ n xi epsilon) :=
  taoSection7ActualQFiniteLimit_bounded01 hepsilon
    (taoSection7SourceActualW n xi epsilon)

theorem taoSection7SourceActualQ_nonneg
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7SourceActualQ n xi epsilon p :=
  (taoSection7SourceActualQ_bounded01
    (n := n) (xi := xi) hepsilon p).1

theorem taoSection7SourceActualQ_fullHoldQRecursion
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (p : TaoSection7RenewalPoint) :
    taoSection7SourceActualQ n xi epsilon p =
      taoSection7FullHoldQRecursionRHS epsilon
        (taoSection7SourceActualW n xi epsilon)
        (taoSection7SourceActualQ n xi epsilon) p :=
  taoSection7ActualQFiniteLimit_fullHoldQRecursion hepsilon
    (taoSection7SourceActualW n xi epsilon) p

end Tao

end Erdos1135
