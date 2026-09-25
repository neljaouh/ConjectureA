import Erdos1135.Tao.Fourier.Section7Geometry
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Renewal.Lemma710EprimeProbability
import Erdos1135.Tao.Renewal.Lemma710KernelWindow
import Erdos1135.Tao.Renewal.Lemma710PostStoppedKernel
import Erdos1135.Tao.Renewal.Lemma77PotentialCore
import Erdos1135.Tao.Section6.Corollary63

namespace Erdos1135

namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

def relativeVerticalOvershoot (s : ℕ) (ell : ℤ) : ℤ :=
  ell - (s : ℤ)

theorem relativeVerticalOvershoot_pos_of_lt
    {s : ℕ} {ell : ℤ} (hlt : (s : ℤ) < ell) :
    0 < relativeVerticalOvershoot s ell := by
  exact sub_pos.mpr hlt

end TaoSection7Lemma77

end

end Tao

end Erdos1135
